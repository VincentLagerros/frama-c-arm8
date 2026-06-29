typedef struct _singly_list {
  int elt;
  struct _singly_list* next;
} singly_list_t;

/*@
  @ type list<A> = Nul | Cons(A, list<A>);
  @ 
  @ 
*/

/*@
  @ inductive wf_singly_list{L}(singly_list_t* lst){
  @   case empty: \forall singly_list_t* lst; lst == \null ==> wf_singly_list(lst);
  @   case non_empty: \forall singly_list_t* lst; lst != \null ==> \valid(lst) ==> wf_singly_list(lst->next) ==> wf_singly_list(lst);
  @   }
  @   
  @ axiomatic wf_singly_list {   
  @ axiom wf_singly_list_inversion: \forall singly_list_t* lst; wf_singly_list(lst) ==>
  @  lst == \null ||
  @  (lst != \null && \valid(lst) && wf_singly_list(lst->next));
  @ }
  @ 
  @ 
*/

/*@
  @ inductive singly_list_length{L}(singly_list_t* lst, integer sz){
  @   case empty: \forall singly_list_t* lst; lst == \null ==> singly_list_length(lst, 0);
  @   case non_empty: \forall singly_list_t* lst; \forall integer sz; lst != \null ==> \valid(lst) ==> singly_list_length(lst->next, sz) ==> singly_list_length(lst, sz+1);
  @   }
  @   
  @ axiomatic singly_list_length {   
  @  axiom singly_list_length_inversion: \forall singly_list_t* lst; \forall integer sz; singly_list_length(lst, sz) ==>
  @  (lst == \null && sz == 0) ||
  @  (\exists integer sz2; lst != \null && \valid(lst) && singly_list_length(lst->next, sz2) && sz == sz2+1);
  @ }
  @ 
*/


/*@
  @ inductive reachable{L}(singly_list_t *lst1, singly_list_t *lst2, integer n){
  @ case reachable1: \forall singly_list_t *lst; reachable(lst, lst, 0);
  @ case reachable2: \forall singly_list_t *lst1, *lst2; \forall integer n1, n2; lst1 != \null ==> \valid(lst1) ==> n2 == n1 + 1 ==> reachable(lst1->next, lst2, n1) ==> reachable(lst1, lst2, n2);
  @ }
  @ 
  @  
  @ 
*/

/*@  
  @ axiomatic reachable {
  @  axiom reachable_inversion: \forall singly_list_t *lst1, *lst2; \forall integer n; reachable(lst1, lst2, n) ==>
  @  (lst1 == lst2 && n == 0) || (n > 0 && lst1 != \null && \valid(lst1) && reachable(lst1->next, lst2, n - 1));
  @  axiom reachable_trans: \forall singly_list_t *lst1, *lst2, *lst3; \forall integer n1, n2, n3; n3 == n1 + n2 ==> reachable(lst1, lst2, n1) ==> reachable(lst2, lst3, n2) ==> reachable(lst1, lst3, n3);
  @  // fora now as axioms ...
  @  // axiom reachable_lhs_next: \forall singly_list_t *lst; lst != \null && \valid(lst) ==> reachable(lst, lst->next, 1);
  @  axiom reachable_rhs_next: \forall singly_list_t *lst1, *lst2; \forall integer n; reachable(lst1, lst2, n) && lst2 != \null && \valid(lst2) ==> reachable(lst1, lst2->next, n + 1);
  @ }
  @ 
  @ 
  @ 
  @ predicate circular_singly_list{L}(singly_list_t *lst) = \exists singly_list_t* lst2; \exists integer n; 
  @    reachable(lst, lst2, n) && (\exists integer m; m >0 && reachable (lst2, lst2, m));
  @    
  @ axiomatic circular_singly_list {
  @ // this should be a lemma ...
  @ axiom null_reachable_non_circular: \forall singly_list_t *lst; \forall integer n; reachable(lst, \null, n) ==> !circular_singly_list(lst);
  @ }
  @ 
  @
*/

/*@ // algorithm for detecting circular list
  @ requires wf_singly_list(lst);
  @ ensures wf_singly_list(lst);
  @ assigns \nothing;
  @ ensures \result == 0;
  @*/

int is_circular_singly_list(singly_list_t* lst) {
    return 0; 
}
