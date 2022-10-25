/* originally: ./include/linux/minmax.h */

/* SPDX-License-Identifier: GPL-2.0 */

#define __cmp(x, y, op)	((x) op (y) ? (x) : (y))



/* #define min(x, y)	__careful_cmp(x, y, <) */
#define min(x, y)	__cmp(x, y, <)
