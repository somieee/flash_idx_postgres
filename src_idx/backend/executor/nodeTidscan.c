/*-------------------------------------------------------------------------
 *
 * nodeTidscan.c
 *	  Routines to support direct tid scans of relations
 *
 * Portions Copyright (c) 1996-2013, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * IDENTIFICATION
 *	  src/backend/executor/nodeTidscan.c
 *
 *-------------------------------------------------------------------------
 */
/*
 * INTERFACE ROUTINES
 *
 *		ExecTidScan			scans a relation using tids
 *		ExecInitTidScan		creates and initializes state info.
 *		ExecReScanTidScan	rescans the tid relation.
 *		ExecEndTidScan		releases all storage.
 *		ExecTidMarkPos		marks scan position.
 *		ExecTidRestrPos		restores scan position.
 */
#include "postgres.h"

#include "access/sysattr.h"
#include "catalog/pg_type.h"
#include "executor/execdebug.h"
#include "executor/nodeTidscan.h"
#include "optimizer/clauses.h"
#include "storage/bufmgr.h"
#include "utils/array.h"
#include "utils/rel.h"

/* FIXME : DASOM */
#include "access/dasom.h"
#include <time.h>
#include <sys/time.h>
#define IsCTIDVar(node)  \
	((node) != NULL && \
	 IsA((node), Var) && \
	 ((Var *) (node))->varattno == SelfItemPointerAttributeNumber && \
	 ((Var *) (node))->varlevelsup == 0)

/*DASOM : TIME FLAG*/
#define TIME 0
#define DASOM_LOG 0
static void TidListCreate(TidScanState *tidstate);
static int	itemptr_comparator(const void *a, const void *b);
static TupleTableSlot *TidNext(TidScanState *node);
/*
 * FIXME:DASOM 
 */
static void _TidListCreate(TidScanState *tidstate);
static TupleTableSlot *TidNext_Multiple(TidScanState *node);
/*
 * Compute the list of TIDs to be visited, by evaluating the expressions
 * for them.
 *
 * (The result is actually an array, not a list.)
 */
static void
TidListCreate(TidScanState *tidstate)
{
	List	   *evalList = tidstate->tss_tidquals;
	ExprContext *econtext = tidstate->ss.ps.ps_ExprContext;
	BlockNumber nblocks;
	ItemPointerData *tidList;
	int			numAllocTids;
	int			numTids;
	ListCell   *l; /*union-3 diff data type and ListCell * for next*/
	
	/*
	 * We silently discard any TIDs that are out of range at the time of scan
	 * start.  (Since we hold at least AccessShareLock on the table, it won't
	 * be possible for someone to truncate away the blocks we intend to
	 * visit.)
	 */
	nblocks = RelationGetNumberOfBlocks(tidstate->ss.ss_currentRelation);

	/*
	 * We initialize the array with enough slots for the case that all quals
	 * are simple OpExprs or CurrentOfExprs.  If there are any
	 * ScalarArrayOpExprs, we may have to enlarge the array.
	 */
	numAllocTids = list_length(evalList);
	tidList = (ItemPointerData *)
		palloc(numAllocTids * sizeof(ItemPointerData));
	numTids = 0;
	tidstate->tss_isCurrentOf = false;

	foreach(l, evalList) /*for loop each Lists in evalList*/
	{
		ExprState  *exstate = (ExprState *) lfirst(l);
		Expr	   *expr = exstate->expr;
		ItemPointer itemptr;
		bool		isNull;

		if (is_opclause(expr))
		{
			FuncExprState *fexstate = (FuncExprState *) exstate;
			Node	   *arg1;
			Node	   *arg2;
			arg1 = get_leftop(expr);
			arg2 = get_rightop(expr);
			if (IsCTIDVar(arg1))
				exstate = (ExprState *) lsecond(fexstate->args);
			else if (IsCTIDVar(arg2))
				exstate = (ExprState *) linitial(fexstate->args);
			else
				elog(ERROR, "could not identify CTID variable");
			
		

			itemptr = (ItemPointer)
				DatumGetPointer(ExecEvalExprSwitchContext(exstate,
														  econtext,
														  &isNull,
														  NULL));
			if (!isNull &&
				ItemPointerIsValid(itemptr) &&
				ItemPointerGetBlockNumber(itemptr) < nblocks)
			{
				if (numTids >= numAllocTids)
				{
					numAllocTids *= 2;
					tidList = (ItemPointerData *)
						repalloc(tidList,
								 numAllocTids * sizeof(ItemPointerData));
				}
				tidList[numTids++] = *itemptr;
			}
		}
		/* my path */
		else if (expr && IsA(expr, ScalarArrayOpExpr))
		{
			ScalarArrayOpExprState *saexstate = (ScalarArrayOpExprState *) exstate;
			Datum		arraydatum;
			ArrayType  *itemarray;
			Datum	   *ipdatums;
			bool	   *ipnulls;
			int			ndatums;
			int			i;

			exstate = (ExprState *) lsecond(saexstate->fxprstate.args);
			arraydatum = ExecEvalExprSwitchContext(exstate,
												   econtext,
												   &isNull,
												   NULL);
			if (isNull)
				continue;
			itemarray = DatumGetArrayTypeP(arraydatum);
			deconstruct_array(itemarray,
							  TIDOID, SizeOfIptrData, false, 's',
							  &ipdatums, &ipnulls, &ndatums);
			if (numTids + ndatums > numAllocTids)
			{
				numAllocTids = numTids + ndatums;
				tidList = (ItemPointerData *)
					repalloc(tidList,
							 numAllocTids * sizeof(ItemPointerData));
			}
			for (i = 0; i < ndatums; i++)
			{
				if (!ipnulls[i])
				{
					itemptr = (ItemPointer) DatumGetPointer(ipdatums[i]);
					if (ItemPointerIsValid(itemptr) &&
						ItemPointerGetBlockNumber(itemptr) < nblocks)
						tidList[numTids++] = *itemptr;
				}
			}
			pfree(ipdatums);
			pfree(ipnulls);
		}
		else if (expr && IsA(expr, CurrentOfExpr))
		{
			CurrentOfExpr *cexpr = (CurrentOfExpr *) expr;
			ItemPointerData cursor_tid;

			if (execCurrentOf(cexpr, econtext,
						   RelationGetRelid(tidstate->ss.ss_currentRelation),
							  &cursor_tid))
			{
				if (numTids >= numAllocTids)
				{
					numAllocTids *= 2;
					tidList = (ItemPointerData *)
						repalloc(tidList,
								 numAllocTids * sizeof(ItemPointerData));
				}
				tidList[numTids++] = cursor_tid;
				tidstate->tss_isCurrentOf = true;
			}
		}
		else
			elog(ERROR, "could not identify CTID expression");
	}

	/*
	 * Sort the array of TIDs into order, and eliminate duplicates.
	 * Eliminating duplicates is necessary since we want OR semantics across
	 * the list.  Sorting makes it easier to detect duplicates, and as a bonus
	 * ensures that we will visit the heap in the most efficient way.
	 */
	if (numTids > 1)
	{
		int			lastTid;
		int			i;
		/*DASOM for measuring time*/
		time_t startTime=0;
		time_t endTime=0;
		float time;	

		/* CurrentOfExpr could never appear OR'd with something else */
		Assert(!tidstate->tss_isCurrentOf);
/*To measure the sorting time*/		
#if TIME		
		startTime=clock();
#endif
		qsort((void *) tidList, numTids, sizeof(ItemPointerData),
			  itemptr_comparator);
#if TIME	
		endTime=clock();
		time=(float)(endTime-startTime)/(CLOCKS_PER_SEC);
		fprintf(stderr, "TIME: Qsort : %f, ", time);
#endif		
/*End sorting time*/

		lastTid = 0;
		for (i = 1; i < numTids; i++)
		{
			if (!ItemPointerEquals(&tidList[lastTid], &tidList[i]))
				tidList[++lastTid] = tidList[i];
		}
		numTids = lastTid + 1;
	}

	tidstate->tss_TidList = tidList;
	tidstate->tss_NumTids = numTids;
	tidstate->tss_TidPtr = -1;
}

/*
 * FIXME:DASOM
 */
#if 1
static void
_TidListCreate(TidScanState *tidstate)
{
	List	   *evalList = tidstate->tss_tidquals;
	ExprContext *econtext = tidstate->ss.ps.ps_ExprContext;
	BlockNumber nblocks;
	ItemPointerData *tidList = NULL;
	int			numAllocTids;
	int			numTids;
	ListCell   *l;
	
	/*
	 * FIXME:DASOM
	 */
	EState *estate;
	
	/*DASOM : for measuring time*/
	time_t start=0;
	time_t end=0;
	double exec;

	struct timeval tv1, tv2;

	/*
	 * We silently discard any TIDs that are out of range at the time of scan
	 * start.  (Since we hold at least AccessShareLock on the table, it won't
	 * be possible for someone to truncate away the blocks we intend to
	 * visit.)
	 */
	nblocks = RelationGetNumberOfBlocks(tidstate->ss.ss_currentRelation);

	/*
	 * We initialize the array with enough slots for the case that all quals
	 * are simple OpExprs or CurrentOfExprs.  If there are any
	 * ScalarArrayOpExprs, we may have to enlarge the array.
	 */
	numAllocTids = list_length(evalList);
	estate = tidstate->ss.ps.state;

	/*DASOM : econtext->Parent_Type = T_Tidscan
	econtext->parentType = nodeTag(tidstate); 
*/

	/*FIXME DASOM*/
//	estate->numAlloctids = numAllocTids;

	/* FIXME : DASOM*/
	tidList = (ItemPointerData *)
		palloc(numAllocTids * sizeof(ItemPointerData));
	//numTids = 0;

		tidstate->tss_isCurrentOf = false;

		foreach(l, evalList)
		{
			ExprState  *exstate = (ExprState *) lfirst(l);
			Expr	   *expr = exstate->expr;
			ItemPointer itemptr;
			bool		isNull;

			if (is_opclause(expr))
			{
				FuncExprState *fexstate = (FuncExprState *) exstate;
				Node	   *arg1;
				Node	   *arg2;
	
				arg1 = get_leftop(expr);
				arg2 = get_rightop(expr);
				if (IsCTIDVar(arg1))
					exstate = (ExprState *) lsecond(fexstate->args);
				else if (IsCTIDVar(arg2))
					exstate = (ExprState *) linitial(fexstate->args);
				else
					elog(ERROR, "could not identify CTID variable");
				
	
				itemptr = (ItemPointer)
					DatumGetPointer(ExecEvalExprSwitchContext(exstate,
															  econtext,
															  &isNull,
															  NULL));
				if (!isNull &&
					ItemPointerIsValid(itemptr) &&
					ItemPointerGetBlockNumber(itemptr) < nblocks)
				{
					if (numTids >= numAllocTids)
					{
						numAllocTids *= 2;
						tidList = (ItemPointerData *)
							repalloc(tidList,
									 numAllocTids * sizeof(ItemPointerData));
					}
					tidList[numTids++] = *itemptr;

				}
			}
			else if (expr && IsA(expr, ScalarArrayOpExpr))
			{
				ScalarArrayOpExprState *saexstate = (ScalarArrayOpExprState *) exstate;
				Datum		arraydatum;
				ArrayType  *itemarray;
				Datum	   *ipdatums;
				bool	   *ipnulls;
				int			ndatums;
				int			i;
	
				exstate = (ExprState *) lsecond(saexstate->fxprstate.args);
				
				arraydatum = ExecEvalExprSwitchContext(exstate,
													   econtext,
												   	   &isNull,
													   NULL);
			


				/* FIXME : DASOM */
				if(estate->_tidListptr!=NULL)
				{
					tidList = estate->_tidListptr;
					numTids = estate->numtid;
					tidstate->tss_isCurrentOf = false;
					
					break; 
				}
				else
				{
					/*arraydatum = ExecEvalExprSwitchContext(exstate,
														   econtext,
													   	   &isNull,
														   NULL);
		
					*/

					if (isNull)
						continue;
					itemarray = DatumGetArrayTypeP(arraydatum);
					deconstruct_array(itemarray,
									  TIDOID, SizeOfIptrData, false, 's',
									  &ipdatums, &ipnulls, &ndatums);
					if (numTids + ndatums > numAllocTids)
					{
						numAllocTids = numTids + ndatums;
						tidList = (ItemPointerData *)
						repalloc(tidList,
							 numAllocTids * sizeof(ItemPointerData));
						//fprintf(stderr, "numTids:%d, numAlloc:%d, current tidList addr : %p, itemptr:%p\n", numTids, numAllocTids, tidList, &tidList[numTids]);
					}
					for (i = 0; i < ndatums; i++)
					{
						if (!ipnulls[i])
						{
							itemptr = (ItemPointer) DatumGetPointer(ipdatums[i]);
							if (ItemPointerIsValid(itemptr) &&
								ItemPointerGetBlockNumber(itemptr) < nblocks)
								tidList[numTids++] = *itemptr;

						//	fprintf(stderr, "numTids:%d/%d, tidList: %p, itemptr:%p\n", numTids, numAllocTids, tidList, &tidList[numTids]);

						}
					}	
					pfree(ipdatums);
					pfree(ipnulls);
				}
			}
			else if (expr && IsA(expr, CurrentOfExpr))
			{
				CurrentOfExpr *cexpr = (CurrentOfExpr *) expr;
				ItemPointerData cursor_tid;

				if (execCurrentOf(cexpr, econtext,
							   RelationGetRelid(tidstate->ss.ss_currentRelation),
								  &cursor_tid))
				{
					if (numTids >= numAllocTids)
					{
						numAllocTids *= 2;
						tidList = (ItemPointerData *)
							repalloc(tidList,
									 numAllocTids * sizeof(ItemPointerData));
				}
					tidList[numTids++] = cursor_tid;
					tidstate->tss_isCurrentOf = true;
				}
			}
			else
				elog(ERROR, "could not identify CTID expression");
		}	

	/* change location
	tidList = estate->_tidListptr;
	
	if( tidList!=NULL)
	{
		numTids = estate->numtid;
		tidstate->tss_isCurrentOf = false;
	}
	*/

		/*
		 * Sort the array of TIDs into order, and eliminate duplicates.
		 * Eliminating duplicates is necessary since we want OR semantics across
		 * the list.  Sorting makes it easier to detect duplicates, and as a bonus
		 * ensures that we will visit the heap in the most efficient way.
		 */
		if (numTids > 1)
		{
			int			lastTid;
			int			i;

			/* CurrentOfExpr could never appear OR'd with something else */
			Assert(!tidstate->tss_isCurrentOf);
			
/*DASOM: start to measure the time*/
#if TIME
			gettimeofday(&tv1, NULL);
#endif

			qsort((void *) tidList, numTids, sizeof(ItemPointerData),
				  itemptr_comparator);
			
/*DASOM: end to measure the time*/
#if TIME
			gettimeofday(&tv2, NULL);
			fprintf(stderr, "sort time,%f\n",(double)(tv2.tv_usec - tv1.tv_usec) / 1000000 + (double) (tv2.tv_sec - tv1.tv_sec));
#endif
			/*Eliminate duplicates*/
			lastTid = 0;
			for (i = 1; i < numTids; i++)
			{
				if (!ItemPointerEquals(&tidList[lastTid], &tidList[i]))
					tidList[++lastTid] = tidList[i];
			}
			numTids = lastTid + 1;
		}

		tidstate->tss_TidList = tidList;
		tidstate->tss_NumTids = numTids;
	tidstate->tss_TidPtr = -1;
}

#endif

/*
 * qsort comparator for ItemPointerData items
 */
static int
itemptr_comparator(const void *a, const void *b)
{
	const ItemPointerData *ipa = (const ItemPointerData *) a;
	const ItemPointerData *ipb = (const ItemPointerData *) b;
	BlockNumber ba = ItemPointerGetBlockNumber(ipa);
	BlockNumber bb = ItemPointerGetBlockNumber(ipb);
	OffsetNumber oa = ItemPointerGetOffsetNumber(ipa);
	OffsetNumber ob = ItemPointerGetOffsetNumber(ipb);

	if (ba < bb)
		return -1;
	if (ba > bb)
		return 1;
	if (oa < ob)
		return -1;
	if (oa > ob)
		return 1;
	return 0;
}

/* ----------------------------------------------------------------
 *		TidNext
 *
 *		Retrieve a tuple from the TidScan node's currentRelation
 *		using the tids in the TidScanState information.
 *
 * FIXME:DASOM TidScanState variable is changed; tss_htup become an array.
 * ----------------------------------------------------------------
 */
static TupleTableSlot *
TidNext(TidScanState *node)
{
	EState	   *estate;
	ScanDirection direction;
	Snapshot	snapshot;
	Relation	heapRelation;
	HeapTuple	tuple;
	TupleTableSlot *slot;
	Buffer		buffer = InvalidBuffer;
	ItemPointerData *tidList;
	int			numTids;
	bool		bBackward;

	/*
	 * extract necessary information from tid scan node
	 */
	estate = node->ss.ps.state;
	direction = estate->es_direction;
	snapshot = estate->es_snapshot;
	heapRelation = node->ss.ss_currentRelation;
	slot = node->ss.ss_ScanTupleSlot;

	/*
	 * First time through, compute the list of TIDs to be visited
	 */
	if (node->tss_TidList == NULL)
//		_TidListCreate(node); /* FIXME:DASOM */
	//	TidListCreate(node);
	tidList = node->tss_TidList;
	numTids = node->tss_NumTids;
	
	/*DASOM*/
	//elog(LOG,"SOM : tidNums : %d",numTids);

	tuple = &(node->tss_htup[0]); //modified

	/*
	 * Initialize or advance scan position, depending on direction.
	 */
	bBackward = ScanDirectionIsBackward(direction);
	if (bBackward)
	{
		if (node->tss_TidPtr < 0)
		{
			/* initialize for backward scan */
			node->tss_TidPtr = numTids - 1;
		}
		else
			node->tss_TidPtr--;
	}
	else
	{
		if (node->tss_TidPtr < 0)
		{
			/* initialize for forward scan */
			node->tss_TidPtr = 0;
		}
		else
			node->tss_TidPtr++;
	}
	//start to fetch tuples based on tidList.
	while (node->tss_TidPtr >= 0 && node->tss_TidPtr < numTids)
	{
		tuple[0].t_self = tidList[node->tss_TidPtr]; //modified

		/*
		 * For WHERE CURRENT OF, the tuple retrieved from the cursor might
		 * since have been updated; if so, we should fetch the version that is
		 * current according to our snapshot.
		 */
		if (node->tss_isCurrentOf)
			heap_get_latest_tid(heapRelation, snapshot, &tuple[0].t_self);//modified

		/* DASOM POINT */ //modified
		if (heap_fetch(heapRelation, snapshot, &tuple[0], &buffer, false, NULL))
		{
			/*
			 * store the scanned tuple in the scan tuple slot of the scan
			 * state.  Eventually we will only do this and not return a tuple.
			 * Note: we pass 'false' because tuples returned by amgetnext are
			 * pointers onto disk pages and were not created with palloc() and
			 * so should not be pfree()'d.
			 */
			ExecStoreTuple(&tuple[0],		/* tuple to store *///modified
						   slot,	/* slot to store in */
						   buffer,		/* buffer associated with tuple  */
						   false);		/* don't pfree */

			/*
			 * At this point we have an extra pin on the buffer, because
			 * ExecStoreTuple incremented the pin count. Drop our local pin.
			 */
			ReleaseBuffer(buffer);

			return slot;
		}
		/* Bad TID or failed snapshot qual; try next */
		if (bBackward)
			node->tss_TidPtr--;
		else
			node->tss_TidPtr++;
	}

	/*
	 * if we get here it means the tid scan failed so we are at the end of the
	 * scan..
	 */
	return ExecClearTuple(slot);
}

#if 0
static TupleTableSlot *
TidNext_Multiple(TidScanState *node)
{
	EState	   *estate;
	ScanDirection direction;
	Snapshot	snapshot;
	Relation	heapRelation;
	HeapTuple	tuple;		
	TupleTableSlot *slot;
	Buffer		*buffer; 
	ItemPointerData *tidList;
	int			numTids;
	bool		bBackward;
	int mbufNum;

	/*DASOM: for measuring the executing time*/
	struct timeval tv1, tv2;
	static int remain_tid=0;
	BlockNumber blk;
	OffsetNumber offnum;

	/*
	 * extract necessary information from tid scan node
	 */
	
	estate = node->ss.ps.state;
	direction = estate->es_direction;
	snapshot = estate->es_snapshot;
	heapRelation = node->ss.ss_currentRelation;
	slot = node->ss.ss_ScanTupleSlot;


	/*DASOM : Indicates the caller(Parent node) is TidScan*/
	node->ss.ps.ps_ExprContext->parentType = nodeTag(node);

	/*
	 * First time through, compute the list of TIDs to be visited
	 */
	if (node->tss_TidList == NULL)
	{
/*DASOM :for measuring the time*/
#if TIME	
		gettimeofday(&tv1, NULL);
#endif
		_TidListCreate(node); /* FIXME:DASOM */

/*DASOM: for measuring the time*/		
#if TIME
		gettimeofday(&tv2, NULL);
		fprintf(stderr, "create list time,%f\n",(double)(tv2.tv_usec - tv1.tv_usec) / 1000000 + (double) (tv2.tv_sec - tv1.tv_sec));

#endif
	}
		//	TidListCreate(node);
	/*
	 * FIXME:DASOM
	 */
	tidList = node->tss_TidList;
	numTids = node->tss_NumTids;
	tuple = node->tss_htup;
	buffer = node->xs_mbuf;
	mbufNum = node->numberOfmbuf;

	if(remain_tid == 0)
		remain_tid = numTids;

	/*
	 * Initialize or advance scan position, depending on direction.
	 */
	bBackward = ScanDirectionIsBackward(direction);
	if (bBackward)
	{
		if (node->tss_TidPtr < 0) //tss_TidPtr init
		{
			/* initialize for backward scan */
			node->tss_TidPtr = numTids - 1;
			elog(LOG, "backward"); /*DASOM log*/
		}
		//else //next turn after init
		//	node->tss_TidPtr=node->tss_TidPtr-mbufNum;
	}
	else
	{
		if (node->tss_TidPtr < 0)
		{
			/* initialize for forward scan */
			node->tss_TidPtr = 0;
	//		elog(LOG, "forward"); /*DASOM log*/
		}
		//else
		//	node->tss_TidPtr=node->tss_TidPtr+mbufNum;
	}
//FIXME

//start to fetch tuples based on tidList.
	while(node->tss_TidPtr >= 0 && node->tss_TidPtr < numTids)
	{
		
		/*
		 * FIXME: DASOM - for proper fetch boundary
		 */
		if(bBackward)
		{
			if((node->tss_TidPtr >= mbufNum))
				tuple[0].t_self = tidList[(node->tss_TidPtr-mbufNum+1)];
			else
				tuple[0].t_self = tidList[0];
		}
		else
		{
			tuple[0].t_self = tidList[node->tss_TidPtr];
////			fprintf(stderr, "tss_TidPtr:%d, current tidList : %p\n", node->tss_TidPtr, tidList);
		}

		/*
		 * For WHERE CURRENT OF, the tuple retrieved from the cursor might
		 * since have been updated; if so, we should fetch the version that is
		 * current according to our snapshot.
		 */
		if (node->tss_isCurrentOf)
			heap_get_latest_tid(heapRelation, snapshot, &tuple[0].t_self);
		/*
		 * FIXME:DASOM
		 * node->multiple_read == falase, heap_fetch_multiple
		 * Otherwise, store each tuples into slot and return until all tuples read by heap_fetch multiple are sent.
		 * When finishing sending mulil fetched tuples, set node->multiple_read = true
		 * and adjust node->tss_TidPtr which is the tidList index.
		 */
		
		/*DASOM - 280715 - add a condition*/
		if(remain_tid < mbufNum)
			mbufNum = remain_tid;
		fprintf(stderr,"remain_tid=%d, TidPtr = %d\n",remain_tid, node->tss_TidPtr);	
		//DASOM : make no errors for executing even if Request%mbufNum!=0
		if(!(node->multiple_read))
		{
			if (heap_fetch_multiple(heapRelation, snapshot, tuple, false, NULL,
								buffer, mbufNum, &tidList[node->tss_TidPtr]))
			{
				/* DASOM log
			 	 * fprintf(stderr,"%dth complete multiple reads.\n",node->i);
				 */
				node->multiple_read=true;
				//(node->i)++;
				//break;
			}
#if 0 //We deal with this error in other point.
			/*
			 * FIXME:DASOM
			 * if not success to fetch multple tuples with the current tidList item,
			 * set tidList to point the next item.
			 */
			/*
			 * It doesn't make sense if we are here. - IMPOSSIBLE
			 * should return "ExecClearTuple(slot)"  
			 *  if fails here, just don't need to move the cursor.
			 *  -- then, it Occurs an infinite loop
			 *  should be fixed.
			 */
			fprintf(stderr, "FATAL ERROR! - IMPOSSIBLE to be here.\n");
			
			if (bBackward)
				node->tss_TidPtr--;
			
			else
				node->tss_TidPtr++;
			tuple[0].t_self = tidList[node->tss_TidPtr];
#endif
		}
		if(node->multiple_read) //DASOM : change else -> if(node->multiple_read)
		{
			fprintf(stderr, "cur_tuple = %d\n", node->cur_tuple);
			if(node->cur_tuple < mbufNum)
			{
				/* DASOM - 270715
				 * If buffer / tuple == Invalid, skip ExecStoreTuple
				 * Gonna add "conditional routine" - DONE
				 */

				if(ItemPointerIsValid(&tidList[node->cur_tuple])) //should be fixed-done	
				{
					blk = ItemPointerGetBlockNumber(&tidList[node->cur_tuple]);
					offnum = ItemPointerGetOffsetNumber(&tidList[node->cur_tuple]);
					fprintf(stderr, "TidList[%d]=(%u, %u) in Buffer[%d] is valid.\n", node->cur_tuple, blk, offnum, buffer[node->cur_tuple]-1);
					/*
					 * store the scanned tuple in the scan tuple slot of the scan
					 * state.  Eventually we will only do this and not return a tuple.
					 * Note: we pass 'false' because tuples returned by amgetnext are
					 * pointers onto disk pages and were not created with palloc() and
					 * so should not be pfree()'d.
					 */
					
					ExecStoreTuple(&tuple[node->cur_tuple],		/* tuple to store */
								   slot,	/* slot to store in */
								   buffer[node->cur_tuple],		/* buffer associated with tuple  */
								   false);		/* don't pfree */
					
					/*
					 * At this point we have an extra pin on the buffer, because
					 * ExecStoreTuple incremented the pin count. Drop our local pin.
					 */
					ReleaseBuffer(buffer[node->cur_tuple]);
					node->cur_tuple++;
					return slot;
				}
				node->cur_tuple++;
			}
			else
			{
				node->cur_tuple=0;
				node->multiple_read=false;
				remain_tid-=mbufNum;
				if (bBackward)
					node->tss_TidPtr-=mbufNum;
				
				else
				{
					node->tss_TidPtr+=mbufNum;
					//tidList = &tidList[node->tss_TidPtr];
				}
			}
		}
	}

	/*
	 * if we get here it means the tid scan failed so we are at the end of the
	 * scan..
	 */
	return ExecClearTuple(slot);
}
#endif

#if 0  //used
static TupleTableSlot *
TidNext_Multiple(TidScanState *node)
{
	EState	   *estate;
	ScanDirection direction;
	Snapshot	snapshot;
	Relation	heapRelation;
	HeapTuple	tuple;		
	TupleTableSlot *slot;
	Buffer		*buffer; 
	ItemPointerData *tidList;
	int			numTids;
	bool		bBackward;
	int mbufNum;

	/*DASOM: for measuring the executing time*/
	struct timeval tv1, tv2;
	static int remain_tid=0;
	BlockNumber blk;
	OffsetNumber offnum;

	/*
	 * extract necessary information from tid scan node
	 */
	
	estate = node->ss.ps.state;
	direction = estate->es_direction;
	snapshot = estate->es_snapshot;
	heapRelation = node->ss.ss_currentRelation;
	slot = node->ss.ss_ScanTupleSlot;


	/*
	 * DASOM : Indicates the caller(Parent node) is TidScan
	 * will be removed soon.
	 */
	node->ss.ps.ps_ExprContext->parentType = nodeTag(node);

	/*
	 * First time through, compute the list of TIDs to be visited
	 */
	if (node->tss_TidList == NULL)
	{
/*DASOM :for measuring the time*/
#if TIME	
		gettimeofday(&tv1, NULL);
#endif
		_TidListCreate(node); /* FIXME:DASOM */

/*DASOM: for measuring the time*/		
#if TIME
		gettimeofday(&tv2, NULL);
		fprintf(stderr, "create list time,%f\n",(double)(tv2.tv_usec - tv1.tv_usec) / 1000000 + (double) (tv2.tv_sec - tv1.tv_sec));

#endif
	}
		//	TidListCreate(node);
	/*
	 * FIXME:DASOM
	 */
	tidList = node->tss_TidList;
	numTids = node->tss_NumTids;
	tuple = node->tss_htup;
	buffer = node->xs_mbuf;
	mbufNum = node->numberOfmbuf;

	if(remain_tid == 0)
		remain_tid = numTids;

	/*
	 * Initialize or advance scan position, depending on direction.
	 */
	bBackward = ScanDirectionIsBackward(direction);
	if (bBackward)
	{
		if (node->tss_TidPtr < 0) //tss_TidPtr init
		{
			/* initialize for backward scan */
			node->tss_TidPtr = numTids - 1;
			elog(LOG, "backward"); /*DASOM log*/
		}
		//else //next turn after init
		//	node->tss_TidPtr=node->tss_TidPtr-mbufNum;
	}
	else
	{
		if (node->tss_TidPtr < 0)
		{
			/* initialize for forward scan */
			node->tss_TidPtr = 0;
	//		elog(LOG, "forward"); /*DASOM log*/
		}
		//else
		//	node->tss_TidPtr=node->tss_TidPtr+mbufNum;
	}
//FIXME

//start to fetch tuples based on tidList.
	while(node->tss_TidPtr >= 0 && node->tss_TidPtr < numTids)
	{
		
		/*
		 * FIXME: DASOM - for proper fetch boundary
		 */
		if(bBackward)
		{
			if((node->tss_TidPtr >= mbufNum))
				tuple[0].t_self = tidList[(node->tss_TidPtr-mbufNum+1)];
			else
				tuple[0].t_self = tidList[0];
		}
		else
		{
			tuple[0].t_self = tidList[node->tss_TidPtr];
////			fprintf(stderr, "tss_TidPtr:%d, current tidList : %p\n", node->tss_TidPtr, tidList);
		}

		/*
		 * For WHERE CURRENT OF, the tuple retrieved from the cursor might
		 * since have been updated; if so, we should fetch the version that is
		 * current according to our snapshot.
		 */
		if (node->tss_isCurrentOf)
			heap_get_latest_tid(heapRelation, snapshot, &tuple[0].t_self);
		/*
		 * FIXME:DASOM
		 * node->multiple_read == falase, heap_fetch_multiple
		 * Otherwise, store each tuples into slot and return until all tuples read by heap_fetch multiple are sent.
		 * When finishing sending mulil fetched tuples, set node->multiple_read = true
		 * and adjust node->tss_TidPtr which is the tidList index.
		 */
		
		/*DASOM - 280715 - add a condition*/
		if(remain_tid < mbufNum)
			mbufNum = remain_tid;
#if DASOM_LOG
		fprintf(stderr,"remain_tid=%d, TidPtr = %d\n",remain_tid, node->tss_TidPtr);	
#endif
		//DASOM : make no errors for executing even if Request%mbufNum!=0
		if(!(node->multiple_read)) //while?
		{
			if (heap_fetch_multiple(heapRelation, snapshot, tuple, false, NULL,
								buffer, mbufNum, &tidList[node->tss_TidPtr]))
			{
				node->multiple_read=true;
			}
		}
		if(node->multiple_read) //DASOM : change else -> if(node->multiple_read)
		{
			while(node->cur_tuple < mbufNum)
			{
#if DASOM_LOG
				fprintf(stderr, "cur_tuple = %d\n", node->cur_tuple);
#endif
				
				/* DASOM - 270715
				 * If buffer / tuple == Invalid, skip ExecStoreTuple
				 * Gonna add "conditional routine" - DONE
				 */
				if(ItemPointerIsValid(&tidList[(node->tss_TidPtr)+(node->cur_tuple)])) 	
				{
#if DASOM_LOG	
					blk = ItemPointerGetBlockNumber(&tidList[(node->tss_TidPtr)+(node->cur_tuple)]);
					offnum = ItemPointerGetOffsetNumber(&tidList[(node->tss_TidPtr)+(node->cur_tuple)]);
					fprintf(stderr, "TidList[%d]=(%u, %u) in Buffer[%d] is valid.\n", node->cur_tuple, blk, offnum, buffer[node->cur_tuple]-1);
#endif
					/*
					 * store the scanned tuple in the scan tuple slot of the scan
					 * state.  Eventually we will only do this and not return a tuple.
					 * Note: we pass 'false' because tuples returned by amgetnext are
					 * pointers onto disk pages and were not created with palloc() and
					 * so should not be pfree()'d.
					 */
					
					ExecStoreTuple(&tuple[node->cur_tuple],		/* tuple to store */
								   slot,	/* slot to store in */
								   buffer[node->cur_tuple],		/* buffer associated with tuple  */
								   false);		/* don't pfree */
					
					/*
					 * At this point we have an extra pin on the buffer, because
					 * ExecStoreTuple incremented the pin count. Drop our local pin.
					 */
					ReleaseBuffer(buffer[node->cur_tuple]);
					node->cur_tuple++;
					return slot;
				}
				node->cur_tuple++;
			}
			node->cur_tuple=0;
			node->multiple_read=false;
			remain_tid-=mbufNum;
			if (bBackward)
				node->tss_TidPtr-=mbufNum;
			else
			{
				node->tss_TidPtr+=mbufNum;
#if DASOM_LOG
				fprintf(stderr, "Move tidlist cursor : %d\n", node->tss_TidPtr);
#endif
			}
		}
	}

	/*
	 * if we get here it means the tid scan failed so we are at the end of the
	 * scan..
	 */
	return ExecClearTuple(slot);
}
#endif


/*
 * TidRecheck -- access method routine to recheck a tuple in EvalPlanQual
 */
static bool
TidRecheck(TidScanState *node, TupleTableSlot *slot)
{
	/*
	 * XXX shouldn't we check here to make sure tuple matches TID list? In
	 * runtime-key case this is not certain, is it?  However, in the WHERE
	 * CURRENT OF case it might not match anyway ...
	 */
	return true;
}


/* ----------------------------------------------------------------
 *		ExecTidScan(node)
 *
 *		Scans the relation using tids and returns
 *		   the next qualifying tuple in the direction specified.
 *		We call the ExecScan() routine and pass it the appropriate
 *		access method functions.
 *
 *		Conditions:
 *		  -- the "cursor" maintained by the AMI is positioned at the tuple
 *			 returned previously.
 *
 *		Initial States:
 *		  -- the relation indicated is opened for scanning so that the
 *			 "cursor" is positioned before the first qualifying tuple.
 *		  -- tidPtr is -1.
 * ----------------------------------------------------------------
 */
// FIXME:DASOM
TupleTableSlot *
ExecTidScan(TidScanState *node)
{
	return ExecScan(&node->ss,
					(ExecScanAccessMtd) TidNext, //TidNext_Multiple,
					(ExecScanRecheckMtd) TidRecheck);
}

/* ----------------------------------------------------------------
 *		ExecReScanTidScan(node)
 * ----------------------------------------------------------------
 */
void
ExecReScanTidScan(TidScanState *node)
{
	if (node->tss_TidList)
		pfree(node->tss_TidList);
	node->tss_TidList = NULL;
	node->tss_NumTids = 0;
	node->tss_TidPtr = -1;

	ExecScanReScan(&node->ss);
}

/* ----------------------------------------------------------------
 *		ExecEndTidScan
 *
 *		Releases any storage allocated through C routines.
 *		Returns nothing.
 * ----------------------------------------------------------------
 */
void
ExecEndTidScan(TidScanState *node)
{
	//int i = 0; //FIXME:DASOM adding an int variable for FOR loop
	/*
	 * Free the exprcontext
	 */
	ExecFreeExprContext(&node->ss.ps);

	/*
	 * clear out tuple table slots
	 */
	ExecClearTuple(node->ss.ps.ps_ResultTupleSlot);
	ExecClearTuple(node->ss.ss_ScanTupleSlot);

	/* FIXME:DASOM release any held pins on a heap page */
	//if(BufferIsValid(node->xs_mbuf[i])

	/*
	 * close the heap relation.
	 */
	ExecCloseScanRelation(node->ss.ss_currentRelation);
}

/* ----------------------------------------------------------------
 *		ExecTidMarkPos
 *
 *		Marks scan position by marking the current tid.
 *		Returns nothing.
 * ----------------------------------------------------------------
 */
void
ExecTidMarkPos(TidScanState *node)
{
	node->tss_MarkTidPtr = node->tss_TidPtr;
}

/* ----------------------------------------------------------------
 *		ExecTidRestrPos
 *
 *		Restores scan position by restoring the current tid.
 *		Returns nothing.
 *
 *		XXX Assumes previously marked scan position belongs to current tid
 * ----------------------------------------------------------------
 */
void
ExecTidRestrPos(TidScanState *node)
{
	node->tss_TidPtr = node->tss_MarkTidPtr;
}

/* ----------------------------------------------------------------
 *		ExecInitTidScan
 *
 *		Initializes the tid scan's state information, creates
 *		scan keys, and opens the base and tid relations.
 *
 *		Parameters:
 *		  node: TidNode node produced by the planner.
 *		  estate: the execution state initialized in InitPlan.
 * ----------------------------------------------------------------
 */
TidScanState *
ExecInitTidScan(TidScan *node, EState *estate, int eflags)
{
	TidScanState *tidstate;
	Relation	currentRelation;

	/*
	 * create state structure
	 */
	tidstate = makeNode(TidScanState);
	tidstate->ss.ps.plan = (Plan *) node;
	tidstate->ss.ps.state = estate;

	/*
	 * Miscellaneous initialization
	 *
	 * create expression context for node
	 */
	ExecAssignExprContext(estate, &tidstate->ss.ps);

	tidstate->ss.ps.ps_TupFromTlist = false;

	/*
	 * initialize child expressions
	 */
	tidstate->ss.ps.targetlist = (List *)
		ExecInitExpr((Expr *) node->scan.plan.targetlist,
					 (PlanState *) tidstate);
	tidstate->ss.ps.qual = (List *)
		ExecInitExpr((Expr *) node->scan.plan.qual,
					 (PlanState *) tidstate);

	tidstate->tss_tidquals = (List *)
		ExecInitExpr((Expr *) node->tidquals,
					 (PlanState *) tidstate);

	/*
	 * tuple table initialization
	 */
	ExecInitResultTupleSlot(estate, &tidstate->ss.ps);
	ExecInitScanTupleSlot(estate, &tidstate->ss);

	/*
	 * mark tid list as not computed yet
	 */
	tidstate->tss_TidList = NULL;
	tidstate->tss_NumTids = 0;
	tidstate->tss_TidPtr = -1;

	/*
	 * DASOM
	 * init the new variables
	 */
	tidstate->numberOfmbuf = MAX_LIBAIO;
	tidstate->cur_tuple = 0;
	tidstate->multiple_read = false;
	tidstate->i = 0;

	/*
	 * open the base relation and acquire appropriate lock on it.
	 */
	currentRelation = ExecOpenScanRelation(estate, node->scan.scanrelid, eflags);

	tidstate->ss.ss_currentRelation = currentRelation;
	tidstate->ss.ss_currentScanDesc = NULL;		/* no heap scan here */

	/*
	 * get the scan type from the relation descriptor.
	 */
	ExecAssignScanType(&tidstate->ss, RelationGetDescr(currentRelation));

	/*
	 * Initialize result tuple type and projection info.
	 */
	ExecAssignResultTypeFromTL(&tidstate->ss.ps);
	ExecAssignScanProjectionInfo(&tidstate->ss);

	/*
	 * all done.
	 */
	return tidstate;
}
