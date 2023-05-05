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
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "memlib.h"
#include "mm.h"

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
#define WSIZE 4
#define DSIZE 8
#define ALIGNMENT 8
#define CHUNKSIZE (456)
#define MINSIZE 24 // 4 + 8 + 8 + 4(保证了free一个块之后可以成为一个blank block)

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define SIZE_PTR(p) ((size_t *)(((char *)(p)) - SIZE_T_SIZE))

#define MAX(x, y) ((x) > (y) ? (x) : (y))

/*Pack a size and allocated bit into a word*/
#define PACK(size, alloc) ((size) | (alloc))

/*Read and write a word at address p*/
#define GET(p) ((p) ? *(uint *)(p) : 0)
#define GET_PTR(p) ((p) ? (void *)(*(size_t *)(p)) : 0)
#define PUT(p, val) ((p) ? *(uint *)(p) = (val) : 0)
#define PUT_PTR(p, ptr) ((p) ? *(size_t *)(p) = (size_t)(ptr) : 0)

/*Read the size and allocated fields from address p*/
/*
warning:
have to secure that p is pointing to the head
*/
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/*Given block ptr bp, compute address of its header and footer*/
#define HEAD(bp) ((char *)(bp)-WSIZE)
#define FOOT(bp) ((char *)(bp) + GET_SIZE(HEAD(bp)) - 2 * WSIZE)
/*for blank block*/
#define PREV_BLANK_POS(bp) ((char *)(bp))
#define NEXT_BLANK_POS(bp) ((bp) ? ((char *)(bp) + DSIZE) : (char *)0)
#define PREV_BLANK_PTR(bp) (GET_PTR(PREV_BLANK_POS(bp)))
#define NEXT_BLANK_PTR(bp) (GET_PTR(NEXT_BLANK_POS(bp)))

/*Given block ptr bp, compute address of next and previous blocks*/
#define PREV_BLOCK(bp) ((char *)(bp)-GET_SIZE(((char *)(bp)-2 * WSIZE)))
#define NEXT_BLOCK(bp) ((char *)(bp) + GET_SIZE(HEAD(bp)))

static char *heap_listp = 0;

/*to maintain the blank list*/
static void add_to_list(void *bp) {
  dbg_printf("[add_to_list] bp = %llx \n", (long long)(bp));
  void *last_bp = NEXT_BLANK_PTR(heap_listp);
  PUT_PTR(PREV_BLANK_POS(bp), heap_listp);
  PUT_PTR(NEXT_BLANK_POS(bp), last_bp);
  PUT_PTR(PREV_BLANK_POS(last_bp), bp);
  PUT_PTR(NEXT_BLANK_POS(heap_listp), bp);
}

static void remove_from_list(void *bp) {
  dbg_printf("[remove_from_list] bp = %llx \n", (long long)(bp));
  void *prev_bp = PREV_BLANK_PTR(bp);
  void *next_bp = NEXT_BLANK_PTR(bp);

  //  dbg_printf("[remove_from_list] bp = %lld; prev_bp = %lld; next_bp = %llx
  //  \n",(long long)(bp - 0x800000000), (long long)(prev_bp - 0x800000000),
  //  (long long)(next_bp));

  PUT_PTR(NEXT_BLANK_POS(prev_bp), next_bp);
  PUT_PTR(PREV_BLANK_POS(next_bp), prev_bp);
}

void *coalesce(void *bp) {

  dbg_printf("[coalesce] enter \n");

  size_t size = GET_SIZE(HEAD(bp));
  //  dbg_printf("[coalesce] bp = %lld; * 0X800000018 = %lld;
  //  FOOT(PREV_BLOCK(bp)) = %lld \n",(long long)(bp - 0x800000000), (long
  //  long)(GET(0X800000018)), (long long)((long long)(PREV_BLOCK(bp)) -
  //  0x800000000));

  // dbg_printf("[coalesce] bp = %llx; PREV_BLOCK(bp) = %llx; FOOT(PREV_BLOCK(bp)) = %llx;  \n ",(long long)(bp), (long long)(PREV_BLOCK(bp)), (long long)(FOOT(PREV_BLOCK(bp))));

  size_t prev_alloc = GET_ALLOC(FOOT(PREV_BLOCK(bp)));
  size_t next_alloc = GET_ALLOC(HEAD(NEXT_BLOCK(bp)));

  // dbg_printf("[coalesce] prev_alloc = %lld \n", (long long)prev_alloc);

  if (!prev_alloc) {
    void *prev_ptr = PREV_BLOCK(bp);
    remove_from_list(prev_ptr);
    size += GET_SIZE(HEAD(prev_ptr));
    PUT(HEAD(prev_ptr), PACK(size, 0));
    PUT(FOOT(bp), PACK(size, 0));
    bp = prev_ptr;
  }
  if (!next_alloc) {
    void *next_ptr = NEXT_BLOCK(bp);
    remove_from_list(next_ptr);
    size += GET_SIZE(HEAD(next_ptr));
    PUT(HEAD(bp), PACK(size, 0));
    PUT(FOOT(next_ptr), PACK(size, 0));
  }
  add_to_list(bp);

  dbg_printf("[coalesce] exit \n");
  return bp;
}

static void *find_fit(size_t asize) {
  void *bp;
  for (bp = NEXT_BLANK_PTR(heap_listp); bp; bp = NEXT_BLANK_PTR(bp)) {
    // dbg_printf("[find fit] bp = %d \n",(int)bp);
    if (asize <= GET_SIZE(HEAD(bp))) {
      return bp;
    }
  }
  return NULL;
}

static void place(void *bp, size_t asize) {
  dbg_printf("[place] enter \n");
  size_t csize = GET_SIZE(HEAD(bp));
  size_t bp_alloc = GET_ALLOC(HEAD(bp));
  if (!bp_alloc)
    remove_from_list(bp);
  if ((csize - asize) >= MINSIZE) {
    dbg_printf("[place] split, bp = %llx \n", (long long)(bp));
    PUT(HEAD(bp), PACK(asize, 1));
    PUT(FOOT(bp), PACK(asize, 1));
    bp = NEXT_BLOCK(bp);
    PUT(HEAD(bp), PACK(csize - asize, 0));
    PUT(FOOT(bp), PACK(csize - asize, 0));
    add_to_list(bp);
  } else {
    PUT(HEAD(bp), PACK(csize, 1));
    PUT(FOOT(bp), PACK(csize, 1));
  }
  dbg_printf("[place] exit \n");
}

static void *extend_heap(size_t size) {
  dbg_printf("[extend_heap] enter \n");

  char *bp;

  // dbg_printf("[extend_heap] GET(0X800000018) = %lld \n", (long
  // long)(GET(0X800000018)));
  /*Allocate an even number of words to maintain alignment*/
  if ((long)(bp = mem_sbrk(size)) == -1)
    return NULL;

  // dbg_printf("[extend_heap] GET(0X800000018) = %lld \n", (long
  // long)(GET(0X800000018)));
  /*Initialize free block header/footer and the epilogue header*/
  PUT(HEAD(bp), PACK(size, 0));          /*Free block header*/
  PUT(FOOT(bp), PACK(size, 0));          /*Free block footer*/
  PUT(HEAD(NEXT_BLOCK(bp)), PACK(0, 1)); /*New epilogue header*/

  // dbg_printf("[extend_heap] bp = %lld; size = %lld; HEAD(bp) = %lld; FOOT(bp)
  // = %lld; HEAD(NEXT_BLOCK(bp)) = %lld \n",(long long) (bp - 0x800000000),
  // (long long)size, (long long)(HEAD(bp) - 0x800000000), (long long)(FOOT(bp)
  // - 0x800000000), (long long)(HEAD(NEXT_BLOCK(bp)) - 0x800000000));

  // dbg_printf("[extend_heap] GET(0X800000018) = %lld \n", (long
  // long)(GET(0X800000018)));

  dbg_printf("[extend_heap] exit \n");

  /*Coalesce if the previous block was free*/
  return coalesce(bp);
}

/*
 * mm_init - Called when a new trace starts.
 */
int mm_init(void) {
  // freopen("log.txt", "w", stdout);
  dbg_printf("[mm_init] enter \n");
  heap_listp = mem_sbrk(8 * WSIZE);
  // dbg_printf("[mm_init] heap_listp = %llx \n",(long long) heap_listp);

  if (heap_listp == (void *)-1)
    return -1;

  PUT(heap_listp, 0);                                /* Alignment padding */
  PUT(heap_listp + (1 * WSIZE), PACK(6 * WSIZE, 1)); /* Prologue header */
  PUT_PTR(heap_listp + (2 * WSIZE), 0);              /* Blank prev pointer */
  PUT_PTR(heap_listp + (4 * WSIZE), 0);              /* Blank next pointer */
  PUT(heap_listp + (6 * WSIZE), PACK(6 * WSIZE, 1)); /* Prologue footer */
  // dbg_printf("[mm_init] heap_listp + (6 * WSIZE) = %llx \n",(long long)
  // (heap_listp + (6 * WSIZE))); dbg_printf("[mm_init] PACK(6 * WSIZE, 1) =
  // %lld \n",(long long) (PACK(6 * WSIZE, 1))); dbg_printf("[mm_init]
  // GET(heap_listp + (6 * WSIZE)) = %lld; GET(0X800000018) = %lld \n",(long
  // long) (GET(heap_listp + (6 * WSIZE))), (long long)(GET(0X800000018)));

  // dbg_printf("[mm_init] GET(0X800000018) = %lld \n", (long
  // long)(GET(0X800000018)));
  PUT(heap_listp + (7 * WSIZE), PACK(0, 1)); /* Epilogue header */
  // dbg_printf("[mm_init] GET(0X800000018) = %lld \n", (long
  // long)(GET(0X800000018)));
  heap_listp += (2 * WSIZE);
  // dbg_printf("[mm_init] GET(0X800000018) = %lld \n", (long
  // long)(GET(0X800000018)));

  dbg_printf("[mm_init] exit \n");
  return 0;
}

/*
 * malloc - Allocate a block by incrementing the brk pointer.
 *      Always allocate a block whose size is a multiple of the alignment.
 */

int malloc_cnt = 0;

void *malloc(size_t size) {
  // dbg_printf("[malloc] GET(0X800000018) = %lld \n", (long
  // long)(GET(0X800000018)));

  // malloc_cnt++;
  // if (malloc_cnt > 15)
  //   exit(0);

  dbg_printf("[malloc] enter \n");
  dbg_printf("[malloc] size = %lld \n", (long long)size);

  int newsize = ALIGN(MAX(MINSIZE, size + 2 * WSIZE));
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

dbg_printf("[malloc] bp = %llx; PREV_BLOCK(bp) = %llx; FOOT(PREV_BLOCK(bp)) = %llx; mem_sbrk(0) = %llx \n ",(long long)(target_bp), (long long)(PREV_BLOCK(target_bp)), (long long)(FOOT(PREV_BLOCK(target_bp))), (long long)mem_sbrk(0));


  dbg_printf("[malloc] exit \n");
  return target_bp;

  // unsigned char *p = mem_sbrk(newsize);
  // // dbg_printf("malloc %u => %p\n", size, p);

  // if ((long)p < 0)
  //   return NULL;
  // else {
  //   p += SIZE_T_SIZE;
  //   *SIZE_PTR(p) = size;
  //   return p;
  // }
}

/*
 * free - We don't know how to free a block.  So we ignore this call.
 *      Computers have big memories; surely it won't be a problem.
 */
void free(void *ptr) {
  /*Get gcc to be quiet */

  dbg_printf("[free] enter %lld\n", ((long long)ptr - 0X800000000));

  if (ptr == NULL || ptr < mem_heap_lo() || ptr > mem_heap_hi()) {
    dbg_printf("[free] wrong exit \n");
    return;
  }

  size_t size = GET_SIZE(HEAD(ptr));
  PUT(HEAD(ptr), PACK(size, 0));
  PUT(FOOT(ptr), PACK(size, 0));

  coalesce(ptr);
  dbg_printf("[free] exit \n");
}

/*
 * realloc - Change the size of the block by mallocing a new block,
 *      copying its data, and freeing the old block.  I'm too lazy
 *      to do better.
 */
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
  size_t new_size = ALIGN(MAX(MINSIZE, size + 2 * WSIZE));
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
    memcpy(newptr, oldptr, oldsize - 2 * WSIZE);
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
}
