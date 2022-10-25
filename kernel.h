/* originally: ./tools/virtio/linux/kernel.h */

/* SPDX-License-Identifier: GPL-2.0 */

/* originally: */
/* #define container_of(ptr, type, member) ({			\ */
/* 	const typeof( ((type *)0)->member ) *__mptr = (ptr);	\ */
/* 	(type *)( (char *)__mptr - offsetof(type,member) );}) */

#define container_of(ptr, type, member) \
	(type *)( (char *)(ptr) - offsetof(type,member) )
