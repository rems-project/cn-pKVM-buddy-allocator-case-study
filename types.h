/* originally ./include/linux/types.h */

/* SPDX-License-Identifier: GPL-2.0 */

typedef __kernel_size_t		size_t;


typedef u64 phys_addr_t;

struct list_head {
	struct list_head *next, *prev;
};
