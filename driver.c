#define assert(x) ((void) 0)


#include "page_alloc.c"

void *cn_aligned_alloc(size_t align, size_t size);
void *cn_malloc(unsigned long size);
void *cn_calloc(size_t num, size_t size);
void cn_print_u64(const char * x, unsigned long y);
void cn_print_nr_u64(int x, unsigned long y);
void cn_print_nr_owned_predicates(void);


s64 hyp_physvirt_offset;
 
struct hyp_pool *init(unsigned int nr_pages) 
/*@ accesses __hyp_vmemmap, hyp_physvirt_offset, cn_virt_ptr;
    ensures take H = Hyp_pool(return, __hyp_vmemmap, cn_virt_ptr, hyp_physvirt_offset); 
@*/
{
  hyp_physvirt_offset = 0x0;
  unsigned int reserved_pages = 0;
  u8 max_order = 10;

  void *start_virt = cn_aligned_alloc(PAGE_SIZE, PAGE_SIZE * nr_pages);
  phys_addr_t range_start = (phys_addr_t) __hyp_pa(start_virt);
  u64 pfn = hyp_phys_to_pfn(range_start);
  u64 npfn = 0-pfn;

  u64 vmemmap_size = sizeof(struct hyp_page) * nr_pages;
  void *start_of_owned_vmemmap = cn_malloc(vmemmap_size);
  __hyp_vmemmap = ((struct hyp_page *) start_of_owned_vmemmap) + npfn;


  struct hyp_pool *pool = cn_calloc(1, sizeof(struct hyp_pool));
  pool->range_start = range_start;
  pool->range_end = range_start + nr_pages * PAGE_SIZE;
  pool->max_order = max_order;

  hyp_pool_init(pool, hyp_phys_to_pfn(range_start), nr_pages, reserved_pages);

  return pool;
}




/*
int main(void)
{
  struct hyp_pool *pool = init();

  void *page1 = hyp_alloc_pages(pool, 2);
  if (page1) {
    ((char *)page1)[1234] = 1;
    hyp_get_page(pool, page1);
    hyp_get_page(pool, page1);
    hyp_put_page(pool, page1);
    cn_print_nr_u64(1, 1);
  }
  else {
    cn_print_nr_u64(2, 2);
  }
  return 0;
} 
*/

#define NR_PAGES 8

int main(void)
/*@ trusted; @*/
{
  struct hyp_pool *pool = init(NR_PAGES);

  void *pages[NR_PAGES];

  int i = 0;
  while (i < NR_PAGES) {
    pages[i] = hyp_alloc_pages(pool, 0);
    i++;
  }

  i = 0;
  while (i < NR_PAGES) {
    cn_print_nr_u64 (0, pages[i]?1:0);
    i++;
  }

  i = 0;
  while (i < NR_PAGES) {
    ((char *)pages[i])[1234] = 1;  
    i++;
  }

  i = 0;
  while (i < NR_PAGES) {
    hyp_put_page(pool, pages[i]);
    i++;
  }

  /* void *page = hyp_alloc_pages(pool, 2); */

  cn_print_nr_owned_predicates();
  return 0;
} 


