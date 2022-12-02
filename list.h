/* originally: ./include/linux/list.h */

/* SPDX-License-Identifier: GPL-2.0 */

#define list_entry(ptr, type, member) \
	container_of(ptr, type, member)
#define list_first_entry(ptr, type, member) \
	list_entry((ptr)->next, type, member)

static inline int list_empty(const struct list_head *head)
/*@ requires let O = Owned(head) @*/
/*@ ensures let OR = Owned(head) @*/
/*@ ensures {*head} unchanged @*/
/*@ ensures return == (((*head).next == head) ? 1 : 0) @*/
{
	/* return READ_ONCE(head->next) == head; */
	return head->next == head;
}

static inline void INIT_LIST_HEAD(struct list_head *list)
/*@ requires let O = Owned(list) @*/
/*@ ensures let OR = Owned(list) @*/
/*@ ensures (*list).next == list; (*list).prev == list @*/
{
	/* WRITE_ONCE (list->next, list); */
	list->next = list;
	list->prev = list;
}

static inline bool __list_del_entry_valid(struct list_head *entry)
/*@ ensures return == 1 @*/
{
	return true;
}

static inline void __list_del(struct list_head * prev, struct list_head * next)
/*@ requires let O1 = Owned(prev) @*/
/*@ requires let O2 = Owned(next) if prev != next @*/
/*@ ensures let O1R = Owned(prev) @*/
/*@ ensures let O2R = Owned(next) if prev != next @*/
/*@ ensures (prev == next) || {(*next).next} unchanged @*/
/*@ ensures (prev == next) || {(*prev).prev} unchanged @*/
/*@ ensures (*prev).next == next @*/
/*@ ensures (prev == next) || ((*next).prev == prev) @*/
/*@ ensures (prev != next) || ((*prev).prev == prev) @*/
{
        /*CN*/ if(prev != next);
        next->prev = prev;
        /* WRITE_ONCE (prev->next, next); */
        prev->next = next;
}

static inline void __list_del_entry(struct list_head *entry)
/*@ requires let O1 = Owned(entry) @*/
/*@ requires let prev = (*entry).prev; let next = (*entry).next @*/
/*@ requires let O2 = Owned(prev) if prev != entry @*/
/*@ requires let O3 = Owned(next) if prev != next @*/
/*@ requires (prev != entry) || (next == entry) @*/
/*@ ensures let O1R = Owned(entry) @*/
/*@ ensures {*entry} unchanged @*/
/*@ ensures let O2R = Owned(prev) if prev != entry @*/
/*@ ensures let O3R = Owned(next) if prev != next @*/
/*@ ensures (prev == next) || {(*next).next} unchanged @*/
/*@ ensures (prev == next) || {(*prev).prev} unchanged @*/
/*@ ensures (prev == entry) || ((*prev).next == next) @*/
/*@ ensures (prev == next) || ((*next).prev == prev) @*/
/*@ ensures (prev != next) || ((prev == entry) || ((*prev).prev == prev)) @*/
{
        /*CN*/ if(entry->prev != entry);
        /*CN*/ if(entry->prev != entry->next);
	if (!__list_del_entry_valid(entry))
		return;

	__list_del(entry->prev, entry->next);
}

static inline void list_del_init(struct list_head *entry)
/*@ requires let O1 = Owned(entry) @*/
/*@ requires let prev = (*entry).prev; let next = (*entry).next @*/
/*@ requires let O2 = Owned(prev) @*/
/*@ requires let O3 = Owned(next) if prev != next @*/
/*@ requires (*entry).prev != entry @*/
/*@ ensures let O1R = Owned(entry) @*/
/*@ ensures (*entry).prev == entry; (*entry).next == entry @*/
/*@ ensures let O2R = Owned(prev) @*/
/*@ ensures let O3R = Owned(next) if prev != next @*/
/*@ ensures (prev == next) || {(*next).next} unchanged @*/
/*@ ensures (prev == next) || {(*prev).prev} unchanged @*/
/*@ ensures (*prev).next == next @*/
/*@ ensures (prev == next) || ((*next).prev == prev) @*/
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
/*@ requires let O1 = Owned(new); let O2 = Owned(prev); let O3 = Owned(next) if prev != next @*/
/*@ ensures let O1R = Owned(new); let O2R = Owned(prev); let O3R = Owned(next) if prev != next @*/
/*@ ensures (prev == next) || {(*prev).prev} unchanged @*/
/*@ ensures (prev == next) || {(*next).next} unchanged @*/
/*@ ensures (*prev).next == new @*/
/*@ ensures (prev == next) || ((*next).prev == new) @*/
/*@ ensures (prev != next) || ((*prev).prev == new) @*/
/*@ ensures (*new).next == next; (*new).prev == prev @*/
{
	if (!__list_add_valid(new, prev, next))
		return;

        /*CN*/ if (prev != next);
	next->prev = new;
	new->next = next;
	new->prev = prev;
	/* WRITE_ONCE (prev->next, new); */
	prev->next = new;
}



static inline void list_add_tail(struct list_head *new, struct list_head *head)
/*@ requires let O1 = Owned(new) @*/
/*@ requires let O2 = Owned(head) @*/
/*@ requires let prev = (*head).prev; let next = head @*/
/*@ requires let O3 = Owned(prev) if prev != next @*/
/*@ ensures let O1R = Owned(new); let O2R = Owned(head); let O3R = Owned(prev) if prev != next @*/
/*@ ensures (prev == next) || {(*prev).prev} unchanged @*/
/*@ ensures (prev == next) || {(*head).next} unchanged @*/
/*@ ensures (*head).prev == new @*/
/*@ ensures (prev == next) || ((*prev).next == new) @*/
/*@ ensures (prev != next) || ((*head).next == new) @*/
/*@ ensures (*new).next == next; (*new).prev == prev @*/
{
        /*CN*/ if (head->prev != head);
	__list_add(new, head->prev, head);
}
