/*
 * Maciej Pietrewicz
 * Indeks: 325022
 * Moje rozwiazanie uzywa dwukierunkowej implicit listy, zawierajacej dwa
 * boundary tagi, footer i header. Ostatni bit boudnary taga uzywam do
 * wyznaczania informacji czy blok jest zajety czy wolny. Iteruje sie poprzez
 * liste za pomoca rozmaru bloku zapisanego w headerze.(Rozmiar trzymany jest
 * rowniez w footerze) Uzylem optymalizacji boundary tagow gdzie footer jest
 * pamietany tylko wtedy gdy blok jest nieuzywany, a wiec w boundary tagu na
 * przedostantim bicie zapisuje informacje czy poprzedni blok jest uzywany czy
 * nie. Przy zwalnianiu pamieci uzywam coalescingu, aby zlaczac nieuzywane
 * bloki. Sprawdzam w tym celu odpowiedni bit w headerze, aby wiedziec czy
 * poprzedni blok jest zajety. Jak jest wolny to za pomoca footera poprzedniego
 * bloku przeskakuje do odpowiedniego adresu. Sprawdzam tez czy nastepny blok
 * jest zajety. Jesli jest wolny to tez go dolaczam tworzac jeden duzy blok.
 * Przy mallocu uzywam splitingu, aby nie marnowac nadmiaru pamieci jesli blok
 * byl zbyt duzy. Aby to zrobic ustawiam odpowiedni size nowego bloku, a z
 * pozostala czesc bloku ustawiam na wolny blok odpowiedniego rozmiaru.
 * Korzystam z niektorych funkcji z pliku mm-implicit.c. Pomysl opieram na
 * wykladzie z przedmiotu Systemy Operacyjne.
 *
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>
#include <stdint.h>
#include <stddef.h>
#include <unistd.h>

#include "mm.h"
#include "memlib.h"

/* If you want debugging output, use the following macro.  When you hand
 * in, remove the #define DEBUG line. */
#define DEBUG
#ifdef DEBUG
#define debug(...) printf(__VA_ARGS__)
#else
#define debug(...)
#endif

/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

typedef enum {
  USED = 1,     /* Block is used */
  PREVUSED = 2, /* Previous block is used (optimized boundary tags) */
} bt_flags;

typedef int32_t btag_t;

#define BLOCK_SIZE sizeof(block_t)

typedef struct {
  int32_t header;
  uint8_t payload[];

} block_t;

static block_t *first_block;
static void *heap_end;

static inline size_t round_up(size_t size) {
  return (size + ALIGNMENT - 1) & -ALIGNMENT;
}

static inline size_t get_size(btag_t btag) {
  return btag & -4;
}

static inline block_t *get_next_block(block_t *block) {
  return (void *)block + get_size(block->header);
}

static inline btag_t *prev_block_footer(block_t *block) {
  return (btag_t *)((void *)block - sizeof(btag_t));
}

static inline btag_t *get_footer(block_t *block) {
  return prev_block_footer(get_next_block(block));
}

static inline block_t *prev_block(block_t *block) {
  size_t size = get_size(*prev_block_footer(block));
  return (void *)block - size;
}

static inline void set_header(block_t *block, size_t size, bool prev_allocated,
                              bool allocated) {
  block->header = (size | allocated) | (prev_allocated << 1);
}

static inline void set_footer(block_t *block, size_t size, bool prev_allocated,
                              bool allocated) {
  btag_t *footer = get_footer(block);
  *footer = (size | allocated) | (prev_allocated << 1);
}

static inline void set_btags(block_t *block, size_t size, bool prev_allocated,
                             bool allocated) {
  set_header(block, size, prev_allocated, allocated);
  set_footer(block, size, prev_allocated, allocated);
}

static inline bool is_used(btag_t btag) {
  return btag & USED;
}

static inline bool is_prev_used(btag_t btag) {
  return btag & PREVUSED;
}

static inline bool nieghbours_block_free(block_t *block, block_t *neighbour) {
  return !is_used(block->header) && !is_used(neighbour->header);
}

static inline bool footer_match_header(block_t *block) {
  if (is_used(block->header))
    return true;

  return (get_size(block->header) == get_size(*get_footer(block))) &&
         (is_used(block->header) == is_used(*get_footer(block))) &&
         (is_prev_used(block->header) == is_prev_used(*get_footer(block)));
}

static inline void print_block_info(block_t *block) {
  debug("BLOCK_ADDRESS: %p HEADER_INFO, BLOCK_SIZE: %ld PREV_BLOCK_USED: %d "
        "BLOCK_USED: %d ",
        block, get_size(block->header), is_prev_used(block->header),
        is_used(block->header));
  if (!is_used(block->header))
    debug("FOOTER_INFO, BLOCK_SIZE: %ld PREV_BLOCK_USED: %d BLOCK_USED: %d ",
          get_size(*get_footer(block)), is_prev_used(*get_footer(block)),
          is_used(*get_footer(block)));
  debug("\n");
}

static inline void print_blocks() {
  debug("BLOCKS LIST STARTS\n");
  for (block_t *it = first_block; (void *)it <= heap_end;
       it = get_next_block(it)) {
    print_block_info(it);
  }
  debug("BLOCKS LIST ENDS\n");
}

static void *morecore(size_t size) {
  void *ptr = mem_sbrk(size);
  if (ptr == (void *)-1)
    return NULL;
  return ptr;
}

static inline bool prev_flag_properly_set(block_t *prev_block, block_t *block) {
  return is_used(prev_block->header) == is_prev_used(block->header);
}

/*
 * Jesli jest to mozliwe to dolaczam do zwalnianego bloku poprzedni i nastepny
 * blok. Blok moze byc dolaczony jesli jest wolny.
 */
static inline void coalesce(block_t *block) {
  size_t new_size = get_size(block->header);
  if (!is_prev_used(
        block->header)) { /* Dolaczanie poprzedniego jesli jest wolny */
    block = prev_block(block);
    new_size += get_size(block->header);
  }

  block_t *n_block = get_next_block(block);
  if ((void *)n_block <= heap_end) {
    if (!is_used(
          n_block->header)) { /* Dolaczanie nastepnego jesli jest wolny */
      new_size += get_size(n_block->header);
    }
  }

  set_btags(block, new_size, 1, 0);

  n_block = get_next_block(block);
  if ((void *)n_block <= heap_end) {
    set_header(n_block, get_size(n_block->header), 0, is_used(n_block->header));
  }
}

/*
 * Jesli ostatni blok jest wolny to rozszerza go do wymaganego rozmiaru.
 * Jesli ostatni blok nie jest wolny to powieksza heap o wymagany rozmiar i
 * tworzy nowy blok.
 */
static block_t *create_new_block(block_t *previous, size_t size) {
  block_t *new_block = NULL;

  if (is_used(previous->header)) { /* Zwieksza heap */

    new_block = morecore(size);
    heap_end = mem_heap_hi();

    set_header(new_block, size, is_used(previous->header), 1);
  } else { /* Rozszerza blok */
    size_t incr_size = size - get_size(previous->header);

    morecore(incr_size);
    heap_end = mem_heap_hi();

    set_header(previous, size, is_prev_used(previous->header), 1);
    new_block = previous;
  }

  return new_block;
}
/*
 * Znajduje pierwszy wolny blok, jesli takiego nie ma to zwraca nowy stworzony
 * blok.
 */
static inline block_t *first_fit(const size_t size) {

  block_t *it;
  block_t *previous_block = first_block;
  for (it = first_block; (void *)it <= heap_end; it = get_next_block(it)) {
    previous_block = it;
    if (!is_used(it->header) && get_size(it->header) >= size)
      return it;
  }

  return create_new_block(previous_block, size);
}

/*
 * Dzieli blok na zajety blok rozmiaru size oraz wolny blok pozostalego rozmiaru
 */
static inline block_t *split(block_t *block, size_t size) {
  size_t prev_size = get_size(block->header);
  set_header(block, size, 1, 1);

  set_btags(get_next_block(block), prev_size - size, 1, 0);

  return block;
}
/*
 * mm_init - Called when a new trace starts. Create init block.
 */
int mm_init(void) {
  /* Pad heap start so first payload is at ALIGNMENT. */
  if ((long)mem_sbrk(ALIGNMENT - offsetof(block_t, payload)) < 0)
    return -1;

  size_t init_size = round_up(BLOCK_SIZE);

  first_block = (block_t *)morecore(init_size);
  heap_end = mem_heap_hi();
  set_header(first_block, round_up(init_size), 1, 0);

  return 0;
}

/*
 * malloc - Allocate a block by incrementing the brk pointer.
 *      Always allocate a block whose size is a multiple of the alignment.
 *      Use first fit to find new block. Split if block is too big.
 */
void *malloc(size_t size) {
  size = round_up(BLOCK_SIZE + size);
  block_t *block = first_fit(size); /* zwraca znaleziony lub nowy blok */

  if (block != NULL) {
    if (get_size(block->header) >
        size) { /* Split gdy alokujemy mniejsza pamiec niz znaleziony blok */
      block = split(block, size);
    } else {
      block_t *next_block = get_next_block(block);
      if ((void *)next_block <= heap_end) { /* Odpowiednio ustawiamy bity w
                                            headerze nastepnego bloku */
        set_header(next_block, get_size(next_block->header), 1,
                   is_used(next_block->header));
      }
    }
    set_header(block, size, is_prev_used(block->header), 1);
  } else {
    return NULL;
  }

  return block->payload;
}

/*
 * free - free and coalesce
 */
void free(void *ptr) {
  if (!ptr)
    return;

  block_t *block = ptr - offsetof(block_t, payload);
  if (!is_used(block->header)) /* Jesli blok nie byl uzywany to nic nie robimy*/
    return;
  coalesce(block); /* Coalescing przy zwalnianiu*/
}

/*
 * realloc - Change the size of the block by mallocing a new block,
 *      copying its data, and freeing the old block.
 **/
void *realloc(void *old_ptr, size_t size) {
  /* If size == 0 then this is just free, and we return NULL. */
  if (size == 0) {
    free(old_ptr);
    return NULL;
  }

  /* If old_ptr is NULL, then this is just malloc. */
  if (!old_ptr)
    return malloc(size);

  void *new_ptr = malloc(size);

  /* If malloc() fails, the original block is left untouched. */
  if (!new_ptr)
    return NULL;

  /* Copy the old data. */
  block_t *block = old_ptr - offsetof(block_t, payload);
  size_t old_size = get_size(block->header);
  if (size < old_size)
    old_size = size;
  memcpy(new_ptr, old_ptr, old_size);

  /* Free the old block. */
  free(old_ptr);

  return new_ptr;
}

/*
 * calloc - Allocate the block and set it to zero.
 */
void *calloc(size_t nmemb, size_t size) {
  size_t bytes = nmemb * size;
  void *new_ptr = malloc(bytes);

  /* If malloc() fails, skip zeroing out the memory. */
  if (new_ptr)
    memset(new_ptr, 0, bytes);

  return new_ptr;
}

/*
 * Iteruje przez liste i sprawdzam:
 * 1. Czy nie ma wolnych blokow obok siebie.
 * 2. Czy dla wolnego bloku header jest rowny footerowi.
 * 3. Czy flaga wskazujaca czy poprzedni blok jest zajety jest poprawnie
 * ustawiona. Jesli, ktorys czynnik nie bedzie sie zgadzal to koncze dzialanie
 * programu.
 */
void mm_checkheap(int verbose) {
  block_t *block = first_block;

  if (!footer_match_header(block)) {
    if (verbose)
      print_blocks();
    assert(footer_match_header(block));
  }

  for (block_t *next_block = get_next_block(first_block);
       (void *)next_block <= heap_end;
       next_block = get_next_block(next_block)) {
    if (nieghbours_block_free(block, next_block)) {
      if (verbose)
        print_blocks();
      assert(!nieghbours_block_free(block, next_block));
    }
    if (!footer_match_header(next_block)) {
      if (verbose)
        print_blocks();
      assert(footer_match_header(next_block));
    } else if (!prev_flag_properly_set(block, next_block)) {
      if (verbose)
        print_blocks();
      assert(prev_flag_properly_set(block, next_block));
    }
    block = next_block;
  }
}
