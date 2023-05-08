/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 *
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  Blocks are never coalesced or reused.  The size of
 * a block is found at the first aligned word before the block (we need
 * it for realloc).
 *
 * This code is correct and blazingly fast, but very bad usage-wise since
 * it never frees anything.
 */
#include <assert.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "memlib.h"
#include "mm.h"


/*空闲块结构：
    * 1. header: 4 bytes
    * 2. prev: 8 bytes (for OPT2, it's 4 bytes)
    * 3. next: 8 bytes (for OPT2, it's 4 bytes)
    * 4. footer: 4 bytes
 
    * allocated块结构：
    * 1. header: 4 bytes
    * 2. payload: size bytes
    * 3. footer: 4 bytes (for OPT1, it's 0 bytes)
 
 *空闲链表设计：
    * 1. 采用双向循环链表
    * 2. 每个空闲块的header和footer中的allocated位都为0
    * 3. 每个空闲块的header中的size位为整个块的大小
    * 4. 每个空闲块的prev和next指针指向前后的空闲块

 *分配器操作：
    * 1. malloc: 从空闲链表中找到第一个合适的空闲块，若剩余空间满足最小空闲块要求，就将其分割成两个块，一个用于分配，一个用于剩余空间
    * 2. free: 将空闲块加入到空闲链表中，然后进行合并操作
    * 3. realloc: 如果新的size比原来的size小，调用place函数；
    如果新的size比原来的size大，那么重新分配一个新的块，然后将原来的块中的数据拷贝到新的块中，最后释放原来的块
    * 4. calloc: 分配一个size大小的块，然后将块中的每个字节都初始化为0
 */


/* If you want debugging output, use the following macro.  When you hand
 * in, remove the #define DEBUG line. */
// #define DEBUG
#ifdef DEBUG
#define dbg_printf(...) printf(__VA_ARGS__)
#else
#define dbg_printf(...)
#endif

/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

/* single word (4) or double word (8) alignment */

#define OPT1 //remove footer
#define OPT2 //remove
// #define TOFILE

#define WSIZE 4
#ifndef OPT2
#define DSIZE 8
#else
#define DSIZE 4
#endif
#define ALIGNMENT 8

#ifndef OPT2
#define CHUNKSIZE 456
#define MINSIZE 24 // 4 + 8 + 8 + 4(保证了free一个块之后可以成为一个blank block)
#else
#define CHUNKSIZE 176
#define MINSIZE 16
#endif

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define SIZE_PTR(p) ((size_t *)(((char *)(p)) - SIZE_T_SIZE))

#define MAX(x, y) ((x) > (y) ? (x) : (y))

/*Pack a size and allocated bit into a word*/
#define PACK(size, alloc) ((size) | (alloc))

/*Read and write a word at address p*/
#define GET(p) ((p) ? *(uint *)(p) : 0)
#define PUT(p, val) ((p) ? *(uint *)(p) = (val) : 0)
/*Read and write a pointer at address p*/
#ifndef OPT2
#define GET_PTR(p) ((p) ? (void *)(*(size_t *)(p)) : 0)
#define PUT_PTR(p, ptr) ((p) ? *(size_t *)(p) = (size_t)(ptr) : 0)
#else
#define GET_PTR(p) ((p) ? (void *)((size_t)(*(uint *)(p)) + 0x800000000) : 0)
#define PUT_PTR(p, ptr)                                                        \
((p) ? *(uint *)(p) = (uint)((size_t)(ptr)-0x800000000) : 0)
#endif

/*Read the size and allocated fields from address p*/
/*warning: have to ensure that p is pointing to the head*/
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_SELF_ALLOC(p) (GET(p) & 0x1)
//for OPT1
#define GET_PREV_ALLOC(p) (GET(p) & 0x2)
#define GET_ALL_ALLOC(p) (GET(p) & 0x3)

/*Given block ptr bp, compute address of its header and footer*/
#define HEAD(bp) ((char *)(bp)-WSIZE)
#define FOOT(bp) ((char *)(bp) + GET_SIZE(HEAD(bp)) - 2 * WSIZE)

/*for blank block, get the prev and next blank block pos*/
#define PREV_BLANK_POS(bp) ((char *)(bp))
#define NEXT_BLANK_POS(bp) ((bp) ? ((char *)(bp) + DSIZE) : (char *)0)
#define PREV_BLANK_PTR(bp) (GET_PTR(PREV_BLANK_POS(bp)))
#define NEXT_BLANK_PTR(bp) (GET_PTR(NEXT_BLANK_POS(bp)))

/*Given block ptr bp, compute address of next and previous blocks*/
#define PREV_BLOCK(bp) ((char *)(bp)-GET_SIZE(((char *)(bp)-2 * WSIZE)))
#define NEXT_BLOCK(bp) ((char *)(bp) + GET_SIZE(HEAD(bp)))

static char *heap_listp = 0;

//-----------------maintain the blank list----------------------
/*add a free block to the linklist*/
static inline void add_to_list(void *bp) {
    dbg_printf("[add_to_list] bp = %llx \n", (long long) (bp));
    void *last_bp = NEXT_BLANK_PTR(heap_listp);
    PUT_PTR(PREV_BLANK_POS(bp), heap_listp);
    PUT_PTR(NEXT_BLANK_POS(bp), last_bp);
    PUT_PTR(PREV_BLANK_POS(last_bp), bp);
    PUT_PTR(NEXT_BLANK_POS(heap_listp), bp);
}

/*remove a free block from the linklist*/
static inline void remove_from_list(void *bp) {
    dbg_printf("[remove_from_list] bp = %llx \n", (long long) (bp));
    void *prev_bp = PREV_BLANK_PTR(bp);
    void *next_bp = NEXT_BLANK_PTR(bp);
    PUT_PTR(NEXT_BLANK_POS(prev_bp), next_bp);
    PUT_PTR(PREV_BLANK_POS(next_bp), prev_bp);
}

//-----------------block operation----------------------
/*check if a free block has free neighbours, if so, merge then together*/
void *coalesce(void *bp) {
    dbg_printf("[coalesce] enter \n");
    dbg_printf("[coalesce] bp = %llx \n", (long long) bp);
    size_t size = GET_SIZE(HEAD(bp));
#ifndef OPT1
    size_t prev_alloc = GET_SELF_ALLOC(FOOT(PREV_BLOCK(bp)));
#else
    size_t prev_alloc = GET_PREV_ALLOC(HEAD(bp));
    dbg_printf("[coalesce] prev_alloc = %lld \n", (long long)prev_alloc);
#endif

    size_t next_alloc = GET_SELF_ALLOC(HEAD(NEXT_BLOCK(bp)));

    if (!prev_alloc) {
        void *prev_ptr = PREV_BLOCK(bp);
        dbg_printf("[coalesce] prev_ptr = %llx \n", (long long) prev_ptr);
        remove_from_list(prev_ptr);
        size += GET_SIZE(HEAD(prev_ptr));

#ifndef OPT1
        PUT(HEAD(prev_ptr), PACK(size, 0));
        PUT(FOOT(bp), PACK(size, 0));
#else
        size_t prev_all_alloc = GET_ALL_ALLOC(HEAD(prev_ptr));
        PUT(HEAD(prev_ptr), PACK(size, prev_all_alloc));
        PUT(FOOT(bp), PACK(size, prev_all_alloc));
#endif

        bp = prev_ptr;
    }
    if (!next_alloc) {
        void *next_ptr = NEXT_BLOCK(bp);
        remove_from_list(next_ptr);
        size += GET_SIZE(HEAD(next_ptr));

#ifndef OPT1
        PUT(HEAD(bp), PACK(size, 0));
        PUT(FOOT(next_ptr), PACK(size, 0));
#else
        size_t bp_all_alloc = GET_ALL_ALLOC(HEAD(bp));
        PUT(HEAD(bp), PACK(size, bp_all_alloc));
        PUT(FOOT(next_ptr), PACK(size, bp_all_alloc));
#endif
    } else {
#ifdef OPT1
        void *next_head_ptr = HEAD(NEXT_BLOCK(bp));
        PUT(next_head_ptr, PACK(GET_SIZE(next_head_ptr), 1));
#endif
    }
    add_to_list(bp);
    dbg_printf("[coalesce] exit \n");
    return bp;
}
/*find a free block large enough to hold the wanted space, if failed, return NULL*/
static void *find_fit(size_t asize) {//asize = actual size
    void *bp;
    dbg_printf("[find fit] NEXT_BLANK_POS(head_listp) = %llx \n",
               (long long) NEXT_BLANK_POS(heap_listp));
    for (bp = NEXT_BLANK_PTR(heap_listp);
         bp && (long long) bp >= (long long) heap_listp; bp = NEXT_BLANK_PTR(bp)) {
        dbg_printf("[find fit] bp = %llx \n", (long long) bp);
        if (asize <= GET_SIZE(HEAD(bp))) {
            return bp;
        }
    }
    return NULL;
}
/*a function to capture asize starting at bp*/
static void place(void *bp, size_t asize) {
    dbg_printf("[place] enter \n");
    size_t csize = GET_SIZE(HEAD(bp));
    dbg_printf("[place] asize = %lld, csize = %lld \n", (long long) asize,
               (long long) csize);

    size_t bp_alloc = GET_SELF_ALLOC(HEAD(bp));
#ifdef OPT1
    size_t bp_all_alloc = GET_ALL_ALLOC(HEAD(bp));
#endif
    if (!bp_alloc)
        remove_from_list(bp);
    if ((csize - asize) >= MINSIZE) {
        dbg_printf("[place] split, bp = %llx \n", (long long) (bp));
#ifndef OPT1
        PUT(HEAD(bp), PACK(asize, 1));
        PUT(FOOT(bp), PACK(asize, 1));
        bp = NEXT_BLOCK(bp);
        PUT(HEAD(bp), PACK(csize - asize, 0));
        PUT(FOOT(bp), PACK(csize - asize, 0));
        add_to_list(bp);
#else
        PUT(HEAD(bp), PACK(asize, bp_all_alloc | 1));
        bp = NEXT_BLOCK(bp);
        PUT(HEAD(bp), PACK(csize - asize, 2));
        PUT(FOOT(bp), PACK(csize - asize, 2));
        add_to_list(bp);
#endif
    } else {
#ifndef OPT1
        PUT(HEAD(bp), PACK(csize, 1));
        PUT(FOOT(bp), PACK(csize, 1));
#else
        PUT(HEAD(bp), PACK(csize, bp_all_alloc | 1));
        void *nxt_head_ptr = HEAD(NEXT_BLOCK(bp));
        PUT(nxt_head_ptr,
            PACK(GET_SIZE(nxt_head_ptr), GET_SELF_ALLOC(nxt_head_ptr) | 2));
#endif
    }
    dbg_printf("[place] exit \n");
}

static void *extend_heap(size_t size) {
    dbg_printf("[extend_heap] enter \n");
    char *bp;
    /*Allocate an even number of words to maintain alignment*/
    if ((long) (bp = mem_sbrk(size)) == -1) {
        return NULL;
    }

/*Initialize free block header/footer and the epilogue header*/
#ifndef OPT1
    PUT(HEAD(bp), PACK(size, 0));          /*Free block header*/
    PUT(FOOT(bp), PACK(size, 0));          /*Free block footer*/
    PUT(HEAD(NEXT_BLOCK(bp)), PACK(0, 1)); /*New epilogue header*/
#else
    size_t prev_alloc = GET_PREV_ALLOC(HEAD(bp));
    PUT(HEAD(bp), PACK(size, prev_alloc | 0));
    PUT(FOOT(bp), PACK(size, prev_alloc | 0));
    PUT(HEAD(NEXT_BLOCK(bp)), PACK(0, 1));
#endif
    dbg_printf("[extend_heap] exit \n");
    /*Coalesce if the previous block was free*/
    return coalesce(bp);
}

/*
 * mm_init - Called when a new trace starts.
 */
int mm_init(void) {
#ifdef TOFILE
    freopen("log.txt", "w", stdout);
#endif
    dbg_printf("[mm_init] enter \n");

#ifndef OPT2
    heap_listp = mem_sbrk(8 * WSIZE);
#else
    heap_listp = mem_sbrk(6 * WSIZE);
#endif
    if (heap_listp == (void *) -1)
        return -1;

#ifndef OPT2
    PUT(heap_listp, 0);                                /* Alignment padding */
    PUT(heap_listp + (1 * WSIZE), PACK(6 * WSIZE, 1)); /* Prologue header */
    PUT_PTR(heap_listp + (2 * WSIZE), 0);              /* Blank prev pointer */
    PUT_PTR(heap_listp + (4 * WSIZE), 0);              /* Blank next pointer */
    PUT(heap_listp + (6 * WSIZE), PACK(6 * WSIZE, 1)); /* Prologue footer */

#ifndef OPT1
    PUT(heap_listp + (7 * WSIZE), PACK(0, 1)); /* Epilogue header */
#else
    PUT(heap_listp + (7 * WSIZE), PACK(0, 3)); /* Epilogue header */
#endif
#else
    PUT(heap_listp, 0);                                /* Alignment padding */
    PUT(heap_listp + (1 * WSIZE), PACK(4 * WSIZE, 1)); /* Prologue header */
    PUT_PTR(heap_listp + (2 * WSIZE), 0);              /* Blank prev pointer */
    PUT_PTR(heap_listp + (3 * WSIZE), 0);              /* Blank next pointer */
    PUT(heap_listp + (4 * WSIZE), PACK(4 * WSIZE, 1)); /* Prologue footer */

#ifndef OPT1
    PUT(heap_listp + (5 * WSIZE), PACK(0, 1));         /* Epilogue header */
#else
    PUT(heap_listp + (5 * WSIZE), PACK(0, 3)); /* Epilogue header */
#endif
#endif
    heap_listp += (2 * WSIZE);

    dbg_printf("[mm_init] exit \n");
    return 0;
}

/*
 * malloc - Allocate a block by reusing free block if feasible. Otherwise by incrementing the brk pointer.
 *      Always allocate a block whose size is a multiple of the alignment.
 */
void *malloc(size_t size) {
    // mm_checkheap(0);
    dbg_printf("[malloc] enter \n");
    dbg_printf("[malloc] size = %lld \n", (long long) size);
#ifndef OPT1
    int newsize = ALIGN(MAX(MINSIZE, size + 2 * WSIZE));
#else
    int newsize = ALIGN(MAX(MINSIZE, size + WSIZE));
#endif
    void *target_bp = find_fit(newsize);
    if (target_bp == NULL) {
        dbg_printf("[malloc] extend heap \n");
        target_bp = extend_heap(MAX(ALIGN(CHUNKSIZE), newsize));
        if (target_bp == NULL) {
            dbg_printf("[malloc] wrong exit \n");
            return NULL;
        }
    }
    place(target_bp, newsize);
    dbg_printf("[malloc] exit \n");
    return target_bp;
}

/*add block to the link list*/
void free(void *ptr) {
    /*Get gcc to be quiet */
    dbg_printf("[free] enter %lld\n", ((long long) ptr - 0X800000000));
    if (ptr == NULL || ptr < mem_heap_lo() || ptr > mem_heap_hi()) {
        dbg_printf("[free] wrong exit \n");
        return;
    }
    size_t size = GET_SIZE(HEAD(ptr));
#ifndef OPT1
    PUT(HEAD(ptr), PACK(size, 0));
    PUT(FOOT(ptr), PACK(size, 0));
#else
    size_t prev_alloc = GET_PREV_ALLOC(HEAD(ptr));
    PUT(HEAD(ptr), PACK(size, prev_alloc));
    PUT(FOOT(ptr), PACK(size, prev_alloc));
    void *nxt_ptr = NEXT_BLOCK(ptr);
    PUT(HEAD(nxt_ptr),
        PACK(GET_SIZE(HEAD(nxt_ptr)), GET_SELF_ALLOC(HEAD(nxt_ptr))));
#endif
    coalesce(ptr);
    dbg_printf("[free] exit \n");
}

/*reuse the old space if the new size is not larger, or malloc a new space */
void *realloc(void *oldptr, size_t size) {
    dbg_printf("[realloc] enter \n");
    size_t oldsize;
    void *newptr;
    /* If size == 0 then this is just free, and we return NULL. */
    if (size == 0) {
        free(oldptr);
        dbg_printf("[realloc] exit \n");
        return 0;
    }
    /* If oldptr is NULL, then this is just malloc. */
    if (oldptr == NULL) {
        dbg_printf("[realloc] exit \n");
        return malloc(size);
    }
    oldsize = GET_SIZE(HEAD(oldptr));
#ifndef OPT1
    size_t new_size = ALIGN(MAX(MINSIZE, size + 2 * WSIZE));
#else
    size_t new_size = ALIGN(MAX(MINSIZE, size + WSIZE));
#endif
    if (new_size <= oldsize) {
        place(oldptr, new_size);
        dbg_printf("[realloc] exit \n");
        return oldptr;
    } else {
        newptr = malloc(size);
        if (!newptr) {
            dbg_printf("[realloc] exit \n");
            return NULL;
        }
#ifndef OPT1
        memcpy(newptr, oldptr, oldsize - 2 * WSIZE);
#else
        memcpy(newptr, oldptr, oldsize - WSIZE);
#endif
        free(oldptr);
        dbg_printf("[realloc] exit \n");
        return newptr;
    }
}

/*
 * calloc - Allocate the block and set it to zero.
 */
void *calloc(size_t nmemb, size_t size) {
    dbg_printf("[calloc] enter \n");
    size_t bytes = nmemb * size;
    void *newptr;

    newptr = malloc(bytes);
    memset(newptr, 0, bytes);

    dbg_printf("[calloc] exit \n");
    return newptr;
}

/*
 * mm_checkheap - There are no bugs in my code, so I don't need to check,
 *      so nah!
 */
void mm_checkheap(int verbose) {
    /*Get gcc to be quiet. */
    verbose = verbose;
    int flag = 0;
    // check merge
    for (char *ptr = heap_listp; GET_SIZE(HEAD(ptr)) != 0;
    ptr = NEXT_BLOCK(ptr)) {
        if (GET_SELF_ALLOC(ptr) == 0) {
            if (!flag) {
                dbg_printf("[error] continuous free block \n");
            } else {
                flag = 1;
            }
        } else {
            flag = 0;
        }
    }

    // check link list
    for (char *bp = NEXT_BLANK_PTR(heap_listp);
         bp && (long long) bp >= (long long) heap_listp; bp = NEXT_BLANK_PTR(bp)) {
        if (GET_SELF_ALLOC(bp) != 0) {
            dbg_printf("[error] free block is not free, start at %lld \n",
                       (long long) bp);
        } else {
            if (NEXT_BLANK_PTR(bp) && PREV_BLANK_PTR(NEXT_BLANK_PTR(bp)) != bp) {
                dbg_printf("[error] free block is not linked, start at %lld \n",
                           (long long) bp);
            }
        }
    }
}