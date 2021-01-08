#include <assert.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <stddef.h>
#include <unistd.h>
#include <stdbool.h>
#include <math.h>

#include "mm.h"
#include "memlib.h"

#ifdef DEBUG
#define debug(fmt, ...) printf("%s: " fmt "\n", __func__, __VA_ARGS__)
#define msg(...) printf(__VA_ARGS__)
#else
#define debug(fmt, ...)
#define msg(...)
#endif

#define __unused __attribute__((unused))

/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* !DRIVER */

typedef int32_t word_t; /* Heap is bascially an array of 4-byte words. */

typedef enum {
  FREE = 0,     /* Block is free */
  USED = 1,     /* Block is used */
  PREVFREE = 2, /* Previous block is free (optimized boundary tags) */
} bt_flags;

static word_t *heap_start; /* Address of the first block */
static word_t *last;       /* Points at last block */
static word_t *list_start; /* Points at the start of free blocks list */
static word_t *list_end;   /* Points at the end of free blocks list */

static inline word_t bt_size(word_t *bt) {
  return *bt & ~(USED | PREVFREE);
}

static inline int bt_used(word_t *bt) {
  return *bt & USED;
}

static inline int bt_free(word_t *bt) {
  return !(*bt & USED);
}

/* Given payload pointer returns an address of boundary tag. */
static inline word_t *bt_fromptr(void *ptr) {
  return (word_t *)ptr - 1;
}

static inline word_t *bt_footer_given_size(word_t *bt, size_t size) {
  if (bt_used(bt))
    return NULL;
  return (void *)bt + size - sizeof(word_t);
}

static inline bt_flags bt_get_prevfree(word_t *bt) {
  return *bt & PREVFREE;
}

static inline void bt_clr_prevfree(word_t *bt) {
  *bt &= ~PREVFREE;
}

static inline void bt_set_prevfree(word_t *bt) {
  *bt |= PREVFREE;
}

static inline word_t *bt_prev_footer(word_t *bt) {
  if (!bt_get_prevfree(bt))
    return NULL;
  return bt - 1;
}

static inline void *bt_payload(word_t *bt) {
  return bt + 1;
}

static inline word_t *bt_next(word_t *bt) {
  if (bt >= last)
    return NULL;
  return (void *)bt + bt_size(bt);
}

static inline word_t *bt_prev(word_t *bt) {
  if (bt == heap_start)
    return NULL;
  word_t *prev_footer = bt_prev_footer(bt);
  if (!prev_footer)
    return NULL;
  return (void *)bt - bt_size(prev_footer);
}

/* Get ptr where the value of the difference of pointers to the prev list elem
 * is stored.*/
static inline word_t *prev_list_block_ptr_diff_from_bt(word_t *bt) {
  return bt + 1;
}

static inline word_t *next_list_block_ptr_diff_from_bt(word_t *bt) {
  return bt + 2;
}

static inline word_t *get_prev_list_block(word_t *bt) {
  word_t *prev_block_diff = prev_list_block_ptr_diff_from_bt(bt);
  if (*prev_block_diff == 0)
    return NULL;
  return (void *)bt - *prev_block_diff;
}

static inline word_t *get_next_list_block(word_t *bt) {
  word_t *next_block_diff = next_list_block_ptr_diff_from_bt(bt);
  if (*next_block_diff == 0)
    return NULL;
  return (void *)bt + *next_block_diff;
}

static inline void add_to_free_list(word_t *bt) {
  /* Value 0 says that list ends/starts here. Nodes of the list keep a
   * difference of pointers neighbouring list elems. */
  if (!list_start) {
    list_start = bt;
    list_end = bt;
    *prev_list_block_ptr_diff_from_bt(bt) = 0;
    *next_list_block_ptr_diff_from_bt(bt) = 0;
  } else {
    int diff = (void *)bt - (void *)list_end;
    *next_list_block_ptr_diff_from_bt(list_end) = diff;
    list_end = bt;
    *prev_list_block_ptr_diff_from_bt(bt) = diff;
    *next_list_block_ptr_diff_from_bt(bt) = 0;
  }
}

static inline void remove_from_free_list(word_t *bt) {
  word_t *prev_list_block = get_prev_list_block(bt);
  word_t *next_list_block = get_next_list_block(bt);
  if (!prev_list_block && !next_list_block) {
    list_start = NULL;
    list_end = NULL;
  } else if (prev_list_block && !next_list_block) {
    /* Removing block from the end of the list. */
    *next_list_block_ptr_diff_from_bt(prev_list_block) = 0;
    list_end = prev_list_block;
  } else if (!prev_list_block && next_list_block) {
    /* Removing block from the beggining of the list. */
    *prev_list_block_ptr_diff_from_bt(next_list_block) = 0;
    list_start = next_list_block;
  } else if (prev_list_block && next_list_block) {
    int diff = (void *)next_list_block - (void *)prev_list_block;
    *next_list_block_ptr_diff_from_bt(prev_list_block) = diff;
    *prev_list_block_ptr_diff_from_bt(next_list_block) = diff;
  }
}

/* Sets up a block (sets up flags and corrects flags of next block). */
static inline void bt_make(word_t *bt, size_t size, short flags,
                           bool correct_next_block_flags) {
  *bt = size | flags;
  word_t *next = bt_next(bt);
  if (bt_free(bt)) {
    word_t *footer = bt_footer_given_size(bt, size);
    *footer = size | flags;
    if (correct_next_block_flags && next)
      bt_set_prevfree(next);
    add_to_free_list(bt);
  } else if (correct_next_block_flags && next)
    bt_clr_prevfree(next);
  if (bt > last || (void *)bt + size >= (void *)last + bt_size(last))
    last = bt;
}

static inline size_t round_up(size_t size) {
  return (size + ALIGNMENT - 1) & -ALIGNMENT;
}

/* Calculates block size incl. header, footer & payload,
 * and aligns it to block boundary (ALIGNMENT). */
static inline size_t blksz(size_t size) {
  return round_up(size + sizeof(word_t));
}

static void *morecore(size_t size) {
  void *ptr = mem_sbrk(size);
  if (ptr == (void *)-1)
    return NULL;
  return ptr;
}

static inline void bt_split(word_t *bt, size_t full_size, size_t desired_size) {
  word_t *next = (void *)bt + desired_size;
  bt_flags old_prevfree = bt_get_prevfree(bt);
  bt_make(bt, desired_size, USED | old_prevfree, false);
  bt_make(next, full_size - desired_size, FREE, true);
}

/* --=[ mm_init ]=---------------------------------------------------------- */
int mm_init(void) {
  void *ptr = morecore(ALIGNMENT - sizeof(word_t));
  if (!ptr)
    return -1;
  heap_start = NULL;
  last = NULL;
  list_start = NULL;
  list_end = NULL;
  return 0;
}

/* --=[ malloc ]=----------------------------------------------------------- */

static word_t *best_fit(size_t reqsz) {
  word_t *curr_block = list_start, *best = NULL;
  size_t min_val = 0;
  while (curr_block) {
    size_t curr_block_size = bt_size(curr_block);
    if (curr_block_size == reqsz)
      return curr_block;
    else if (curr_block_size > reqsz &&
             (!best || (best && curr_block_size < min_val))) {
      min_val = curr_block_size;
      best = curr_block;
    }
    curr_block = get_next_list_block(curr_block);
  }
  return best;
}

void *malloc(size_t size) {
  size_t reqsz = blksz(size);
  word_t *fit = NULL;
  void *ptr = NULL;
  if (heap_start) {
    fit = best_fit(reqsz);
    if (fit) {
      size_t fit_size = bt_size(fit);
      remove_from_free_list(fit);
      if (fit_size == reqsz) {
        bt_flags old_fit_prevfree = bt_get_prevfree(fit);
        bt_make(fit, reqsz, USED, true | old_fit_prevfree);
      } else
        bt_split(fit, fit_size, reqsz);
      return bt_payload(fit);
    }
  }
  if (last && bt_free(last)) {
    /* No need to extend heap by reqsz */
    size_t extra_memory_needed = reqsz - bt_size(last);
    ptr = morecore(extra_memory_needed);
    if (!ptr)
      return NULL;
    remove_from_free_list(last);
    bt_flags last_prevfree = bt_get_prevfree(last);
    bt_make(last, reqsz, USED | last_prevfree, false);
    fit = last;
  } else {
    ptr = morecore(reqsz);
    if (!ptr)
      return NULL;
    fit = (word_t *)ptr;
    bt_flags fit_prevfree = last && bt_free(last) ? PREVFREE : 0;
    bt_make(fit, reqsz, USED | fit_prevfree, false);
    last = fit;
  }
  if (!heap_start)
    heap_start = fit;
  return bt_payload(fit);
}

/* --=[ free ]=------------------------------------------------------------- */
void free(void *ptr) {
  if (!ptr)
    return;
  word_t *bt = bt_fromptr(ptr);
  if (bt_free(bt))
    return;
  word_t *prev = bt_prev(bt), *next = bt_next(bt);
  bool prev_free = prev ? bt_free(prev) : false;
  bool next_free = next ? bt_free(next) : false;
  size_t size = bt_size(bt);
  if (!prev_free && !next_free) {
    /* case 1 (according to the lecture notes and csapp) */
    bt_make(bt, size, FREE, true);
  } else if (!prev_free && next_free) {
    /* case 2 (according to the lecture notes and csapp) */
    remove_from_free_list(next);
    size += bt_size(next);
    bt_make(bt, size, FREE, true);
  } else if (prev_free && !next_free) {
    /* case 3 (according to the lecture notes and csapp) */
    remove_from_free_list(prev);
    size += bt_size(prev);
    bt_flags old_prev_prevfree = bt_get_prevfree(prev);
    bt_make(prev, size, FREE | old_prev_prevfree, true);
  } else if (prev_free && next_free) {
    /* case 4 (according to the lecture notes and csapp) */
    remove_from_free_list(prev);
    remove_from_free_list(next);
    size += bt_size(prev) + bt_size(next);
    bt_flags old_prev_prevfree = bt_get_prevfree(prev);
    bt_make(prev, size, FREE | old_prev_prevfree, true);
  }
}

/* --=[ realloc ]=---------------------------------------------------------- */
void *realloc(void *old_ptr, size_t size) {
  if (size == 0) {
    free(old_ptr);
    return NULL;
  }
  if (!old_ptr)
    return malloc(size);
  word_t *bt = bt_fromptr(old_ptr), *next = bt_next(bt);
  size_t reqsz = blksz(size), old_block_size = bt_size(bt);
  if (old_block_size == reqsz)
    return old_ptr;
  else if (reqsz < old_block_size) {
    size_t old_next_block_size = next ? bt_size(next) : -1;
    bt_split(bt, old_block_size, reqsz);
    if (next && bt_free(next) && old_next_block_size != -1) {
      /* Merge two free blocks. */
      word_t *new_bt_next_block = bt_next(bt);
      remove_from_free_list(new_bt_next_block);
      remove_from_free_list(next);
      size_t new_next_block_size =
        old_next_block_size + bt_size(new_bt_next_block);
      bt_make(new_bt_next_block, new_next_block_size, FREE, false);
    }
    return old_ptr;
  }
  if (next && bt_free(next)) {
    size_t combined_size = old_block_size + bt_size(next);
    if (combined_size == reqsz) {
      remove_from_free_list(next);
      bt_flags old_prev_prevfree = bt_get_prevfree(bt);
      bt_make(bt, reqsz, USED | old_prev_prevfree, true);
      return old_ptr;
    } else if (combined_size > reqsz) {
      remove_from_free_list(next);
      bt_split(bt, combined_size, reqsz);
      return old_ptr;
    } else if (next == last) {
      size_t extra_memory_needed = reqsz - combined_size;
      void *ptr = morecore(extra_memory_needed);
      if (ptr) {
        remove_from_free_list(last);
        bt_flags last_prevfree = bt_get_prevfree(last);
        bt_make(bt, reqsz, USED | last_prevfree, false);
        last = bt;
        return old_ptr;
      }
    }
  }
  void *new_ptr = malloc(size);
  if (new_ptr) {
    memcpy(new_ptr, old_ptr, old_block_size - sizeof(word_t));
    free(old_ptr);
  }
  return new_ptr;
}

/* --=[ calloc ]=----------------------------------------------------------- */
void *calloc(size_t nmemb, size_t size) {
  size_t bytes = nmemb * size;
  void *new_ptr = malloc(bytes);
  if (new_ptr) {
    memset(new_ptr, 0, bytes);
  }
  return new_ptr;
}

/* --=[ mm_checkheap ]=----------------------------------------------------- */
void mm_checkheap(int verbose) {
  word_t *curr_block = heap_start;
  while (curr_block) { /* For each block check if it's correct. */
    size_t size = bt_size(curr_block);
    word_t *footer = bt_footer_given_size(curr_block, size);
    if (bt_free(curr_block)) {
      if (!footer)
        printf("Heap is not correct! Footer is missing!\n");
      /* Check if header and footer have the same informations. */
      if (*curr_block != *footer)
        printf("Heap is not correct! footer != header!\n");
      /* Check if size is the same as header and footer say. */
      size_t calculated_size =
        (void *)footer - (void *)curr_block + sizeof(word_t);
      if (calculated_size != size)
        printf("Heap is not correct! calculated size != read size!\n");
      word_t *prev = bt_prev(curr_block);
      word_t *next = bt_next(curr_block);
      if (prev && bt_free(prev))
        printf("Heap is not correct! Previous block is free!\n");
      if (next) {
        if (bt_free(next))
          printf("Heap is not correct! Next block is free!\n");
        if (!bt_get_prevfree(next))
          printf(
            "Heap is not correct! Next block doesn't have PREVFREE flag!\n");
      }
    } else {
      if (footer)
        printf("Heap is not correct! Used block has footer!\n");
    }
    curr_block = bt_next(curr_block);
  }
}