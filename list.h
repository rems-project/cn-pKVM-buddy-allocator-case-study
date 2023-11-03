/* originally: ./include/linux/list.h */

/* SPDX-License-Identifier: GPL-2.0 */

#define list_entry(ptr, type, member) \
	container_of(ptr, type, member)
#define list_first_entry(ptr, type, member) \
	list_entry((ptr)->next, type, member)

static inline int list_empty(const struct list_head *head)
/*@ requires take O = Owned(head) @*/
/*@ ensures take OR = Owned(head) @*/
/*@ ensures O == OR @*/
/*@ ensures return == (((*head).next == head) ? 1 : 0) @*/
{
	/* return READ_ONCE(head->next) == head; */
	return head->next == head;
}

/* renamed list to llist to avoid clash with CN keyword list */
static inline void INIT_LIST_HEAD(struct list_head *llist)
/*@ requires take O = Owned(llist) @*/
/*@ ensures take OR = Owned(llist) @*/
/*@ ensures (*llist).next == llist; (*llist).prev == llist @*/
{
	/* WRITE_ONCE (llist->next, llist); */
	llist->next = llist;
	llist->prev = llist;
}

static inline bool __list_del_entry_valid(struct list_head *entry)
/*@ ensures return == 1 @*/
{
	return true;
}

static inline void __list_del(struct list_head * prev, struct list_head * next)
/*@ requires take O1 = Owned(prev) @*/
/*@ requires take O2 = O_struct_list_head(next, prev != next) @*/
/*@ ensures take O1R = Owned(prev) @*/
/*@ ensures take O2R = O_struct_list_head(next, prev != next) @*/
/*@ ensures (prev == next) || (O2.next == O2R.next) @*/
/*@ ensures (prev == next) || {(*prev).prev} unchanged @*/
/*@ ensures (*prev).next == next @*/
/*@ ensures (prev == next) || (O2R.prev == prev) @*/
/*@ ensures (prev != next) || ((*prev).prev == prev) @*/
{
        /*@ split_case prev != next @*/
        next->prev = prev;
        /* WRITE_ONCE (prev->next, next); */
        prev->next = next;
}

static inline void __list_del_entry(struct list_head *entry)
/*@ requires take O1 = Owned(entry) @*/
/*@ requires let prev = (*entry).prev; let next = (*entry).next @*/
/*@ requires take O2 = O_struct_list_head(prev, prev != entry) @*/
/*@ requires take O3 = O_struct_list_head(next, prev != next) @*/
/*@ requires (prev != entry) || (next == entry) @*/
/*@ ensures take O1R = Owned(entry) @*/
/*@ ensures {*entry} unchanged @*/
/*@ ensures take O2R = O_struct_list_head(prev, prev != entry) @*/
/*@ ensures take O3R = O_struct_list_head(next, prev != next) @*/
/*@ ensures (prev == next) || (O3.next == O3R.next) @*/
/*@ ensures (prev == next) || (O2.prev == O2R.prev) @*/
/*@ ensures (prev == entry) || (O2R.next == next) @*/
/*@ ensures (prev == next) || (O3R.prev == prev) @*/
/*@ ensures (prev != next) || ((prev == entry) || (O2R.prev == prev)) @*/
{
        /*@ split_case (*entry).prev != entry @*/
        /*@ split_case (*entry).prev != (*entry).next @*/
	if (!__list_del_entry_valid(entry))
		return;

	__list_del(entry->prev, entry->next);
}

static inline void list_del_init(struct list_head *entry)
/*@ requires take O1 = Owned(entry) @*/
/*@ requires let prev = (*entry).prev; let next = (*entry).next @*/
/*@ requires take O2 = Owned(prev) @*/
/*@ requires take O3 = O_struct_list_head(next, prev != next) @*/
/*@ requires (*entry).prev != entry @*/
/*@ ensures take O1R = Owned(entry) @*/
/*@ ensures (*entry).prev == entry; (*entry).next == entry @*/
/*@ ensures take O2R = Owned(prev) @*/
/*@ ensures take O3R = O_struct_list_head(next, prev != next) @*/
/*@ ensures (prev == next) || (O3.next == O3R.next) @*/
/*@ ensures (prev == next) || {(*prev).prev} unchanged @*/
/*@ ensures (*prev).next == next @*/
/*@ ensures (prev == next) || (O3R.prev == prev) @*/
/*@ ensures (prev != next) || ((*prev).prev == prev) @*/
{
        /*CN*/ if(entry->prev != entry);
        /*CN*/ if(entry->prev != entry->next);
	__list_del_entry(entry);
	INIT_LIST_HEAD(entry);
}

static inline bool __list_add_valid(struct list_head *new,
				struct list_head *prev,
				struct list_head *next)
/*@ ensures return == 1 @*/
{
	return true;
}


static inline void __list_add(struct list_head *new,
			      struct list_head *prev,
			      struct list_head *next)
/*@ requires take O1 = Owned(new); take O2 = Owned(prev); take O3 = O_struct_list_head(next, prev != next) @*/
/*@ ensures take O1R = Owned(new); take O2R = Owned(prev); take O3R = O_struct_list_head(next, prev != next) @*/
/*@ ensures (prev == next) || {(*prev).prev} unchanged @*/
/*@ ensures (prev == next) || (O3.next == O3R.next) @*/
/*@ ensures (*prev).next == new @*/
/*@ ensures (prev == next) || (O3R.prev == new) @*/
/*@ ensures (prev != next) || ((*prev).prev == new) @*/
/*@ ensures (*new).next == next; (*new).prev == prev @*/
{
	if (!__list_add_valid(new, prev, next))
		return;

        /*@ split_case prev != next @*/
	next->prev = new;
	new->next = next;
	new->prev = prev;
	/* WRITE_ONCE (prev->next, new); */
	prev->next = new;
}



static inline void list_add_tail(struct list_head *new, struct list_head *head)
/*@ requires take O1 = Owned(new) @*/
/*@ requires take O2 = Owned(head) @*/
/*@ requires let prev = (*head).prev; let next = head @*/
/*@ requires take O3 = O_struct_list_head(prev, prev != next) @*/
/*@ ensures take O1R = Owned(new); take O2R = Owned(head); take O3R = O_struct_list_head(prev, prev != next) @*/
/*@ ensures (prev == next) || (O3.prev == O3R.prev) @*/
/*@ ensures (prev == next) || {(*head).next} unchanged @*/
/*@ ensures (*head).prev == new @*/
/*@ ensures (prev == next) || (O3R.next == new) @*/
/*@ ensures (prev != next) || ((*head).next == new) @*/
/*@ ensures (*new).next == next; (*new).prev == prev @*/
{
        /*@ split_case (*head).prev != head @*/
	__list_add(new, head->prev, head);
}
