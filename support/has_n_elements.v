(** %\subsection*{ support :  has\_n\_elements.v }%*)
Set Implicit Arguments.
Require Export cast_between_subsets.
Require Export distinct_facts.

(** - There are n elements in a set whenever we can make a seq of n elements
 of that set, being all different, which form the full set

 %\label{hasnelements}% *)

Definition has_n_elements := 
 [n:Nat;A:Setoid](EXT v:(seq n A) | (full A)='(seq_set v) /\ (distinct v)).

Lemma has_n_elements_comp : (A:Setoid;n,m:Nat;B,C:(part_set A))
 (has_n_elements n B) -> B='C -> n='m -> (has_n_elements m C).
Intros.
Generalize H0;Generalize H1;Clear H1 H0;Intros H0 H1.
Red.
Rewrite H0 in H.
Red in H.
Inversion_clear H.
Exists (Map_to_equal_subsets H1 x).
Inversion_clear H2.
Split.
Simpl.
Red.
Split;Intros.
Simpl.
Unfold subtype_image_equal.
Simpl in H1.
Red in H1.
NewDestruct x0.
Rename subtype_elt into a.
Rename subtype_prf into sp.
Generalize (H1 a).
Intro.
Inversion_clear H4.
Generalize (H6 sp).
Intro.
LetTac a':=(Build_subtype H4).
Simpl in H;Red in H.
Generalize (H a').
Intro.
Inversion_clear H7.
Generalize (H8 I);Intro.
Simpl in H7.
Inversion_clear H7.
Rename x0 into i.
Exists i.
(Apply Trans with (subtype_elt a');Auto with algebra).
Simpl.
Red in H10.
(Apply Trans with (subtype_elt (x i));Auto with algebra).
Simpl.
Auto.
Red.
Intros.
Red in H3;Intro;(Apply (H3 i j);Auto with algebra).
Simpl.
Simpl in H4.
Red.
Red in H4.
(Apply Trans with  (subtype_elt (Map_to_equal_subsets H1 x i));Auto with algebra).
(Apply Trans with (subtype_elt (Map_to_equal_subsets H1 x j));Auto with algebra).
Qed.

(** - These are trivial results but for the one level of subset-ness: *)

Lemma n_element_subset_sequence : (A:Setoid;n:Nat;B:(part_set A))
 (has_n_elements n B) -> (EXT v:(seq n A) | B='(seq_set v)/\(distinct v)).
Intros.
Red in H.
Inversion_clear H.
Inversion_clear H0.
Exists (Map_embed x).
Simpl in H.
Red in H.
Simpl in H.
Split;Simpl.
Red.
Simpl.
Intro a;Split;Intros.
Generalize (H (Build_subtype H0));Clear H;Intros (p,q);Generalize (p I);Clear p q;Intro.
Inversion_clear H.
Red in H2.
Exists x0.
Simpl in H2.
Auto.
Inversion_clear H0.
(Apply in_part_comp_l with (subtype_elt (x x0));Auto with algebra).
(Apply Map_embed_preserves_distinct;Auto with algebra).
Qed.

Lemma seq_set_n_element_subset : (A:Setoid;n:Nat;B:(part_set A))
 (EXT v:(seq n A) | B='(seq_set v)/\(distinct v)) -> (has_n_elements n B).
Intros.
Red.
Inversion_clear H.
Inversion_clear H0.
Assert (i:(fin n))(in_part (x i) B).
Intro.
Simpl in H.
Red in H.
Generalize (H (x i)).
Intros (p,q).
Apply q.
Simpl.
Exists i;Apply Refl.
Exists (cast_map_to_subset H0).
Split.
Simpl.
Red.
Split;Intro.
Simpl.
Unfold subtype_image_equal.
Simpl in H;Red in H;Simpl in H.
Generalize (H (subtype_elt x0)).
Intros (p,q).
Assert (in_part (subtype_elt x0) B);Auto with algebra.
Generalize (p H3);Intro.
Inversion_clear H4.
Exists x1.
(Apply Trans with (x x1);Auto with algebra).
Simpl.
Auto with algebra.
Red;Intros;Red in H1;Red in H1.
Intro.
Apply (H1 ?? H2).
Simpl in H3.
Red in H3;Simpl in H3.
NewDestruct x.
Simpl in H3.
Simpl.
Auto.
Qed.

Lemma has_zero_elements_then_empty : (A:Setoid;B:(part_set A))
 (has_n_elements O B) -> B='(empty A).
Intros.
Generalize (n_element_subset_sequence H).
Intros (v,(E,D)).
(Apply Trans with (seq_set v);Auto with algebra).
Qed.

Lemma empty_then_has_zero_elements : (A:Setoid;B:(part_set A))
 B='(empty A) -> (has_n_elements O B).
Intros.
(Apply seq_set_n_element_subset;Auto with algebra).
Exists (empty_seq A).
Split.
(Apply Trans with (empty A);Auto with algebra).
Red.
Intros.
(Apply False_ind;Auto with algebra).
Qed.

Hints Resolve has_zero_elements_then_empty empty_then_has_zero_elements : algebra.

Lemma full_preserves_has_n_elements : (A:Setoid;n:Nat)
 (has_n_elements n A) -> (has_n_elements n (full A)).
Intros.
Inversion_clear H.
Inversion_clear H0.
(Apply seq_set_n_element_subset;Auto with algebra).
Exists x.
Tauto.
Qed.

Lemma has_n_elements_inj : (A:Setoid;n:Nat;B:(part_set A))
 (has_n_elements n B) ->
   (m:Nat;C:(part_set A)) (has_n_elements m C) -> B='C ->
     n='m.

NewInduction n.
Intros.
NewDestruct m;Simpl.
Auto.

Inversion_clear H0.
LetTac c:=(head x).
Assert B='(empty A).
Generalize (n_element_subset_sequence H);Intro p.
Inversion_clear p.
Inversion_clear H0.
(Apply Trans with (seq_set x0);Auto with algebra).
Simpl in H1;Red in H1.
Elim (H1 (C c)).
Intros.
Assert (in_part (subtype_elt c) C);Auto with algebra.
Generalize (H4 H5).
Intros.
Assert (in_part (C c) (empty A)).
(Apply in_part_comp_r with B;Auto with algebra).
Simpl in H7.
Contradiction.

Intros B HB.
NewInduction m.
Intros.
Inversion_clear HB.
LetTac b:=(head x).
Assert C='(empty A).
Generalize (n_element_subset_sequence H);Intro p.
Inversion_clear p.
Inversion_clear H2.
(Apply Trans with (seq_set x0);Auto with algebra).
Simpl in H0;Red in H0.
Elim (H0 (B b)).
Intros.
Assert (in_part (subtype_elt b) B);Auto with algebra.
Generalize (H3 H5).
Intros.
Assert (in_part (B b) (empty A)).
(Apply in_part_comp_r with C;Auto with algebra).
Simpl in H7.
Contradiction.

Generalize (n_element_subset_sequence HB);Intro p.
Inversion_clear p.
LetTac B':=(seq_set (Seqtl x)).
Assert (distinct (Seqtl x)).
Inversion_clear H.
(Apply Seqtl_preserves_distinct;Auto with algebra).

Assert (has_n_elements n B').
Apply seq_set_n_element_subset.
Exists (Seqtl x);Auto with algebra.
Intros.
Simpl in H3.
Red in H3.
Elim (H3 (head x)).
Intros.
Assert (in_part (head x) B).
Clear H3 H4 H5;Inversion_clear H.
Simpl in H3.
Red in H3.
Simpl in H3.
Elim (H3 (head x));Intros.
Unfold head.
(Apply H5;Auto with algebra).
Exists (Build_finiteT (lt_O_Sn n)).
Unfold head;Auto with algebra.
Generalize (H4 H6).
Intro.
Clear H4 H5 H6.
Rename H3 into HBC.
Generalize (n_element_subset_sequence H2).
Intro p;Inversion_clear p.
Inversion_clear H3.
Assert (in_part (head x) (seq_set x0)).
(Apply in_part_comp_r with C;Auto with algebra).
Simpl in H3.
Inversion_clear H3.
LetTac C':=(seq_set (omit x0 x1)).
Assert (has_n_elements m C').
Apply seq_set_n_element_subset.
Exists (omit x0 x1);Split;Auto with algebra.
Generalize omit_preserves_distinct.
Intro p.
Apply (p??x0 H5 x1).
Simpl.
(Apply f_equal with f:=S;Auto with algebra).
Apply (IHn ?H1?? H3).

Assert (seq_set x)='(seq_set x0).
Inversion_clear H.
(Apply Trans with B;Auto with algebra).
(Apply Trans with C;Auto with algebra).
Unfold B' C'.
Inversion_clear H.
Clear H3 C' H4 HBC H7 H2 C H1 H0 B' H9 IHm HB B IHn.
Move H10 after x1.
Rename x1 into i.

Change (eq_part (seq_set (Seqtl x)) (seq_set (omit x0 i))).
Red.
Intro a;Split;Intros.
Assert ~(a='(x0 i)).
Assert ~(a='(head x)).
Simpl in H.
Inversion_clear H.
NewDestruct x1.
Intro.
Unfold head in H.
Assert (x (Build_finiteT (lt_O_Sn n)))='(x (Build_finiteT (lt_n_S index n in_range_prf))).
(Apply Trans with a;Auto with algebra).
Red in H10.
Red in H10.
(Apply H10 with (Build_finiteT (lt_O_Sn n))(Build_finiteT (lt_n_S index n in_range_prf));Auto with algebra).
Simpl.
Auto.
Intro;Red in H0;(Apply H0;Auto with algebra).
(Apply Trans with (x0 i);Auto with algebra).

Assert (in_part a (seq_set x0)).
Assert (in_part a (seq_set x)).
Simpl in H.
Inversion_clear H.
NewDestruct x1.
(Apply in_part_comp_l with (x (Build_finiteT (lt_n_S index n in_range_prf)));Auto with algebra).
Simpl.
Exists (Build_finiteT (lt_n_S index n in_range_prf));Auto with algebra.
(Apply in_part_comp_r with (seq_set x);Auto with algebra).
Simpl in H1.
Inversion_clear H1.
Rename x1 into q.
Assert ~i='q in (fin?).
Intro;Red in H0;Apply H0.
(Apply Trans with (x0 q);Auto with algebra).
Elim (omit_removes' x0 H1).
Intros.
(Apply in_part_comp_l with (x0 q);Auto with algebra).
(Apply in_part_comp_l with (omit x0 i x1);Auto with algebra).
Simpl;Exists x1;Auto with algebra.

Opaque omit.
Simpl in H.
Inversion_clear H.
Rename x1 into q.
Assert ~a='(x0 i).
Intro.
Generalize (distinct_omit_removes_all H5 5!i 6!q);Intro p;Red in p.
Apply p.
(Apply Trans with a;Auto with algebra).
Assert ~a='(head x).
Red in H;Intro;Apply H.
(Apply Trans with (head x);Auto with algebra).
Assert (in_part a (seq_set x0)).
(Apply in_part_comp_l with (omit x0 i q);Auto with algebra).
(Apply omit_seq_in_seq_set;Auto with algebra).
Assert (in_part a (seq_set x)).
(Apply in_part_comp_r with (seq_set x0);Auto with algebra).
Simpl in H3;Simpl.
Inversion_clear H3.
NewDestruct x1.
NewDestruct index.
(Apply False_ind;Auto with algebra).
Red in H1;Apply H1.
Unfold head;(Apply Trans with (x (Build_finiteT in_range_prf));Auto with algebra);Simpl.
Exists (Build_finiteT (lt_S_n??in_range_prf)).
(Apply Trans with (x (Build_finiteT in_range_prf));Auto with algebra).
Qed.

Lemma has_extra_element: (A:Setoid;B,C:(part_set A);m,n:Nat) 
 (has_n_elements n B) -> (has_n_elements m C) -> (lt m n) ->
   (EXT a:A | (in_part a B)/\~(in_part a C)).
Intros.
Assert (EXT i:Nat | n='(plus (S i) m)).
Clear H H0.
Induction H1.
Exists O;Simpl;Auto.
Inversion_clear HrecH1.
Exists (S x).
Simpl.
Apply f_equal with f:=S.
Auto.
Inversion_clear H2.
Rename x into d.
Generalize B C n H H0 H1 d H3.
Clear H3 d H1 H0 H n C B.
NewInduction m.
Intros.
NewDestruct n.
Inversion_clear H1.
Generalize (n_element_subset_sequence H);Intro p;Inversion_clear p.
Exists (x (Build_finiteT H1)).
Inversion_clear H2.
Split.
(Apply in_part_comp_r with (seq_set x);Auto with algebra).
Simpl.
Exists (Build_finiteT H1);Auto with algebra.
Generalize (n_element_subset_sequence H0);Intro p;Inversion_clear p.
Inversion_clear H2.
Intro.
Assert (in_part (x (Build_finiteT H1)) (empty A)).
(Apply in_part_comp_r with (seq_set x0);Auto with algebra).
(Apply in_part_comp_r with C;Auto with algebra).
Simpl in H8.
Auto.
Intros.
Generalize (n_element_subset_sequence H0);Intro p;Inversion_clear p.
Inversion_clear H2.
Case (classic (in_part (head x) B)).
NewDestruct n.
Inversion_clear H1.
Generalize (n_element_subset_sequence H);Intro p;Inversion_clear p.
Inversion_clear H2.
Intro.
Assert (in_part (head x) (seq_set x0)).
(Apply in_part_comp_r with B;Auto with algebra).
Simpl in H8.
Inversion_clear H8.
Rename x1 into i.
Rename x0 into Bseq.
LetTac B':=(seq_set (omit Bseq i)).
LetTac C':=(seq_set (Seqtl x)).
Generalize (IHm B' C' n).
Assert (has_n_elements n B').
(Apply seq_set_n_element_subset;Auto with algebra).
Exists (omit Bseq i).
Split;Auto with algebra.
(Apply omit_preserves_distinct with i:=i;Auto with algebra).
Intro q;Generalize (q H8);Clear H8 q;Intro.
Assert (has_n_elements m C').
(Apply seq_set_n_element_subset;Auto with algebra).
Exists (Seqtl x);Split;Auto with algebra.
(Apply Seqtl_preserves_distinct with v:=x;Auto with algebra).
Assert (lt m n);Auto with arith.
Assert n=(plus (S d) m).
(Apply eq_add_S;Auto with algebra).
Transitivity (plus (S d) (S m)).
Auto.
Symmetry.
Transitivity (plus (S (S d)) m);Auto.
Apply plus_Snm_nSm.
Generalize (H8 H10 H11 d H12);Clear H12 H11 H10 H8;Intro.
Inversion_clear H8.
Rename x0 into a;Exists a.
Inversion_clear H10.
Split.
Unfold B' in H8.
Change (EXT j:(fin?) | a='(omit Bseq i j)) in H8.
Inversion_clear H8.
Rename x0 into j.
(Apply in_part_comp_l with (omit Bseq i j);Auto with algebra).
(Apply in_part_comp_r with (seq_set Bseq);Auto with algebra).
(Apply omit_seq_in_seq_set;Auto with algebra).
(Apply not_inpart_comp_r with (seq_set x);Auto with algebra).
Simpl.
Intro.
Inversion_clear H10.
NewDestruct x0.
Rename index into xi.
NewDestruct xi.
Assert a='(head x).
(Apply Trans with (x (Build_finiteT in_range_prf));Auto with algebra);Unfold head;Simpl.
Generalize distinct_omit_removes_all;Intro q;Red in q.
Unfold B' in H8.
Change (EXT j:(fin?) | a='(omit Bseq i j)) in H8.
Inversion_clear H8.
Rename x0 into j.
Apply (q ???H7 i j).
(Apply Trans with a;Auto with algebra).
(Apply Trans with (head x);Auto with algebra).
Assert (in_part a C').
Simpl.
Exists (Build_finiteT (lt_S_n ?? in_range_prf)).
(Apply Trans with (x (Build_finiteT in_range_prf));Auto with algebra).
(Apply H11;Auto with algebra).

(***********)

Intro.
LetTac C':=(seq_set (Seqtl x)).
Generalize (IHm B C' n H).
Assert (has_n_elements m C').
(Apply seq_set_n_element_subset;Auto with algebra).
Exists (Seqtl x);Split;Auto with algebra.
(Apply Seqtl_preserves_distinct with v:=x;Auto with algebra).
Assert (lt m n);Auto with arith.
Intro.
Generalize (H8 H6  H7);Clear H8;Intro.
Simpl in n;Assert n=(plus (S (S d)) m).
Simpl;Transitivity (plus (S d) (S m));Auto.
Symmetry.
Replace (S (S (plus d m))) with (plus (S (S d)) m);Auto with arith.
Apply plus_Snm_nSm.
Generalize (H8?H9);Clear H9 H8 H7;Intro.
Inversion_clear H7.
Rename x0 into a.
Inversion_clear H8.
Exists a;Split;Auto.
(Apply not_inpart_comp_r with (seq_set x);Auto with algebra).
Simpl.
Intro.
Inversion_clear H8.
NewDestruct x0.
Rename index into xi.
NewDestruct xi.
Assert a='(head x).
(Apply Trans with (x (Build_finiteT in_range_prf));Auto with algebra);Unfold head;Simpl.
(Apply H2;Auto with algebra).
(Apply in_part_comp_l with a;Auto with algebra).
(Apply H9;Auto with algebra).
Simpl.
Exists (Build_finiteT (lt_S_n??in_range_prf)).
(Apply Trans with (x (Build_finiteT in_range_prf));Auto with algebra).
Qed.

Lemma inject_subsets_preserves_has_n_elements :
 (A:Setoid;B:(part_set A);C:(part_set B);n:Nat)
   (has_n_elements n C) -> (has_n_elements n (inject_subsets C)).
Intros.
Red in H.
Inversion_clear H.
Rename x into cseq.
Inversion_clear H0.
Red.
Exists (comp_map_map (Build_Map (inject_subsetsify_comp 3!C)) cseq).
Split.
Simpl.
Red.
Intro c;Split;Intros.
Simpl.
Unfold subtype_image_equal.
Simpl.
Simpl in H;Red in H;Simpl in H.
NewDestruct c.
Rename subtype_elt into c''.
Rename subtype_prf into Hc''.
Simpl in Hc''.
Elim Hc''.
Intros c' Hc'.
Elim (H c').
Intros.
Generalize (H2 I);Clear H2 H3;Intros.
Inversion_clear H2.
Rename x into i.
Exists i.
Simpl;Red in H3.
(Apply Trans with (subtype_elt (subtype_elt c'));Auto with algebra).
Simpl.
Auto.

Simpl.
Unfold subtype_image_equal.
Simpl.
Red;Intros;Intro.
Red in H1;(Apply (H1 i j);Auto with algebra).
Qed.

Lemma inject_subsets_respects_has_n_elements :
 (A:Setoid;B:(part_set A);C:(part_set B);n:Nat)
   (has_n_elements n (inject_subsets C)) -> (has_n_elements n C).
Intros.
Red;Red in H.
Inversion_clear H.
Inversion_clear H0.
Rename x into isCseq.
Exists (comp_map_map (Build_Map (uninject_subsetsify_comp 3!C)) isCseq).
Split.
Simpl.
Red.
Intros.
Simpl.
Intuition.
Unfold subtype_image_equal.
Clear H0;Simpl in H;Red in H;Simpl in H.
Elim (H (inject_subsetsify x)).
Intros.
Generalize (H0 I);Clear H0 H2;Intro.
Inversion_clear H0.
Rename x into c.
Rename x0 into i.
Exists i.
Red in H2.
Simpl in H2.
(Apply Trans with (subtype_elt (isCseq i));Auto with algebra).
Unfold uninject_subsetsify.
Case (isCseq i).
Simpl.
Auto with algebra.
Red.
Simpl.
Unfold subtype_image_equal.
Unfold uninject_subsetsify.
Intros.
Generalize (H1 i j H0);Clear H1.
Case (isCseq i);Case (isCseq j).
Simpl.
Unfold subtype_image_equal.
Simpl.
Auto with algebra.
Qed.
