/*
 * mm-naive.c - 가장 빠르지만 메모리 효율성은 가장 낮은 malloc 패키지입니다.
 *
 * 이 단순한(naive) 방식에서는 brk 포인터를 증가시키기만 함으로써 블록을 할당합니다.
 * 블록은 순수한 페이로드(payload)로만 구성되며 헤더나 푸터는 없습니다.
 * 블록은 결코 병합(coalesce)되거나 재사용되지 않습니다.
 * Realloc은 mm_malloc과 mm_free를 사용하여 직접 구현됩니다.
 *
 * 학생들을 위한 참고 사항: 이 헤더 주석을 본인의 솔루션에 대한
 * 전반적인 설명을 담은 헤더 주석으로 교체하세요.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * 학생들을 위한 참고 사항: 다른 작업을 시작하기 전에,
 * 다음 구조체에 팀 정보를 입력해 주세요.
 ********************************************************/
team_t team = {
    /* 팀 이름 */
    "team11",
    /* 첫 번째 팀원의 전체 이름 */
    "Jae-Hoo Joe",
    /* 첫 번째 팀원의 이메일 주소 */
    "grooochyjeff1234@gmail.com",
    /* 두 번째 팀원의 전체 이름 (없으면 비워둠) */
    "",
    /* 두 번째 팀원의 이메일 주소 (없으면 비워둠) */
    ""};

/* 싱글 워드(4) 또는 더블 워드(8) 정렬(alignment) */
#define ALIGNMENT 8

/* ALIGNMENT의 가장 가까운 배수로 올림 */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE (1<<12)

#define MAX(x, y) ((x) > (y) ? (x) : (y))

#define PACK(size, alloc) ((size) | (alloc))

#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp)) - WSIZE))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp)) - DSIZE))

static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);

static char *heap_listp;

/*
 * mm_init - malloc 패키지를 초기화합니다.
 */
int mm_init(void)
{
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)
    {
        return -1;
    }

    PUT(heap_listp, 0);
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));
    heap_listp += (2*WSIZE);

    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
    {
        return -1;
    }

    return 0;
}

static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;

    if ((long)(bp = mem_sbrk(size)) == -1)
    {
        return NULL;
    }

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    return coalesce(bp);
}

/*
 * mm_malloc - brk 포인터를 증가시켜 블록을 할당합니다.
 *     항상 정렬(alignment)의 배수 크기로 블록을 할당합니다.
 */
void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendSize;
    char *bp;

    if (size == 0)
    {
        return NULL;
    }

    if (size <= DSIZE)
    {
        asize = 2*DSIZE;
    }
    else
    {
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);
    }

    if ((bp = find_fit(asize)) != NULL)
    {
        place(bp, asize);
        return bp;
    }

    extendSize = MAX(asize, CHUNKSIZE);

    if ((bp = extend_heap(extendSize/WSIZE)) == NULL)
    {
        return NULL;    
    }

    place(bp, asize);
    return bp;
}

/*
 * mm_free - 블록을 해제(free)해도 아무 작업도 수행하지 않습니다.
 */
void mm_free(void *ptr)
{
    void *bp = ptr;
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));

    coalesce(bp);
}

static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc)
    {
        return bp;
    }
    else if (prev_alloc && !next_alloc)
    {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));

        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    else if (!prev_alloc && next_alloc)
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));

        PUT(FTRP(bp), PACK(size, 0));          
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); 

        bp = PREV_BLKP(bp);
    }
    else
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp)));

        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); 
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0)); 

        bp = PREV_BLKP(bp);
    }

    return bp;
}

/*
 * mm_realloc - mm_malloc과 mm_free를 이용해 단순하게 구현되었습니다.
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;

    size_t copySize;
   
    newptr = mm_malloc(size);

    if (newptr == NULL)
    {
      return NULL;
    }

    copySize = GET_SIZE(HDRP(oldptr));

    if (size < copySize)
    {
      copySize = size;
    }

    memcpy(newptr, oldptr, copySize);

    mm_free(oldptr);

    return newptr;
}

static void *find_fit(size_t asize)
{
    void *bp;

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
    {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
        {
            return bp;
        } 
    }

    return NULL;
}

static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));

    if ((csize - asize) >= (2*DSIZE))
    {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));

        bp = NEXT_BLKP(bp);

        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
    }
    else
    {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}