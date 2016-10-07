/*-------------------------------------------------------------------------
 *
 * dasom_bufmgr.h
 *	  Add functions for AIO - POSTGRES buffer manager definitions.
 *
 *
 * Portions Copyright (c) 1996-2013, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 * src/include/storage/bufmgr.h
 *
 *-------------------------------------------------------------------------
 */
#ifndef DASOM_BUFMGR_H
#define DASOM_BUFMGR_H

#include "storage/block.h"
#include "storage/buf.h"
#include "storage/bufpage.h"
#include "storage/relfilenode.h"
#include "utils/relcache.h"

#include "storage/smgr.h"

/*
 * prototypes for new functions in bufmgr.c
 */

extern void ReadBufferMultiple(Relation reln, Buffer *mbuf, int mbufNum, ItemPointerData *tidList);
extern void ReadBufferExtendedMultiple(Relation reln, ForkNumber forkNum, Buffer *mbuf,
		int mbufNum, ItemPointerData *tidList, ReadBufferMode mode, BufferAccessStrategy strategy);
extern void ReadBufferMultiple_common(SMgrRelation smgr, char relpersistence, ForkNumber forkNum, 
		ItemPointerData *tidList, int mbufNum, Buffer *mbuf, ReadBufferMode mode, BufferAccessStrategy strategy, bool *hit);

#endif

