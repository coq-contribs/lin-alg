(** %\subsection*{ support :  finite\_subsets.v }%*)
Set Implicit Arguments.
Require Export Diff.
Require Export Singleton.
Require Export cast_between_subsets.
Require Export empty.
Require Export Classical_Prop.

(** - A set is finite if we can list its elements (possibly with duplicates in the list)

 %\label{isfiniteset}% *)

Definition is_finite_set [A:Setoid]
  := (EXT n:Nat | (EXT v:(seq n A) | (full A)='(seq_set v))).

(** - For subsets, the following notion is more useful as it removes one
   one layer of taking subsets: *)
Definition is_finite_subset [A:Setoid;B:(part_set A)]
  := (EXT n:Nat | (EXT v:(seq n A) | B='(seq_set v))).


Lemma is_finite_subset_comp : (A:Setoid;B,C:(part_set A))
  B='C -> (is_finite_subset B)->(is_finite_subset C).
Red.
Intros.
Red in H0.
Inversion H0.
Inversion H1.
Exists x.
Exists x0.
(Apply Trans with B;Auto with algebra).
Qed.

(** - There is no corresponding is_finite_set_comp, for there is no 'master' setoid 
 wherein two Setoids can be compared. *)

Hints Resolve is_finite_subset_comp : algebra.


Lemma is_finite_subset_then_is_finite : (A:Setoid;B:(part_set A))
  (is_finite_subset B) -> (is_finite_set B).
Intros.
Red; Red in H.
Inversion_clear H;Inversion_clear H0.
Exists x.
Assert (i:(fin x))(in_part (x0 i) B).
Simpl in H;Red in H;Simpl in H.
Intros.
Elim (H (x0 i)).
Intros p q;(Apply q;Auto with algebra).
Exists i;Auto with algebra.
Exists (cast_map_to_subset H0).
Simpl;Red;Simpl;Split;Intro;Auto.
Unfold subtype_image_equal.
Simpl in H;Red in H;Simpl in H.
Elim (H (subtype_elt x1)).
Intros.
Assert (in_part (subtype_elt x1) B).
Auto with algebra.
Elim (H2 H4).
Intros.
Exists x2.
(Apply Trans with (x0 x2);Auto with algebra).
Qed.

Lemma is_finite_set_then_is_finite_subset : (A:Setoid;B:(part_set A))
  (is_finite_set B) -> (is_finite_subset B).
Intros;Red;Red in H.
Inversion_clear H;Inversion_clear H0.
Exists x;Exists (Map_embed x0).
NewDestruct x0;Simpl in H;Red in H;Simpl in H;Simpl;Red;Simpl.
Split;Intros.
Red in H0;Elim (H (Build_subtype H0)).
Intros p _;Generalize (p I);Clear p; Intro.
Inversion_clear H1.
Red in H2.
Exists x1.
Simpl in H2.
Auto.
Inversion_clear H0.
(Apply in_part_comp_l with (subtype_elt (Ap x1));Auto with algebra).
Qed.

Lemma seq_set_is_finite_subset : (A:Setoid;n:Nat;v:(seq n A))
  (is_finite_subset (seq_set v)).
Intros.
Red.
Exists n.
Exists v.
Auto with algebra.
Qed.

(** - This one is surprisingly hard to prove (or did I not think hard enough?) *)

Lemma included_reflects_is_finite_subset : (A:Setoid;B,C:(part_set A))
 (is_finite_subset C) -> (included B C) -> (is_finite_subset B).
Intros.
Red in H.
Inversion_clear H.
Generalize B C H0 H1.
Clear  H1 H0 C B.
Induction x.
Intros.
Inversion_clear H1.
Assert C='(empty A).
(Apply Trans with (seq_set x);Auto with algebra).
Clear H x.
Assert (included B (empty A)).
(Apply included_comp with B C;Auto with algebra).
Red in H.
Red.
Exists O;Exists (empty_seq A).
(Apply Trans with (empty A);Auto with algebra).
Split.
Intro;Auto.
Intro p;Simpl in p;Contradiction.

Intros.
Inversion_clear H1.
Assert (in_part (head x0) B)\/~(in_part (head x0) B);Try Apply classic.
Inversion_clear H1.
Assert (included (diff B (single (head x0))) (seq_set (Seqtl x0))).
Red.
Intros.
Simpl in H1.
Inversion_clear H1.
Red in H0.
Generalize (H0 x1 H3).
Intro.
Assert (in_part x1 (seq_set x0)).
(Apply in_part_comp_r with C;Auto with algebra).
Simpl in H5.
Inversion_clear H5.
Assert ~x2='(Build_finiteT (lt_O_Sn x)) in (fin (S x)).
Unfold head in H4.
Red;Red in H4;Intro;Apply H4.
(Apply Trans with (x0 x2);Auto with algebra).
Assert (EXT i:(fin x) | x2 =' (Cases i of (Build_finiteT n Hn) => (Build_finiteT (lt_n_S??Hn)) end) in (fin (S x))).
Clear H6 H1 H4 H3 x1 H2 H x0 H0 C B Hrecx A.
NewDestruct x2.
Simpl in H5.
Simpl.
Assert (EXT n:Nat | index=(S n)).
NewDestruct index.
Absurd O=O;Auto.
Exists n.
Auto.
Inversion_clear H.
Rewrite H0 in in_range_prf.
Exists (Build_finiteT (lt_S_n??in_range_prf)).
Simpl.
Auto.
Inversion_clear H7.
NewDestruct x3.
(Apply in_part_comp_l with (x0 (Build_finiteT (lt_n_S??in_range_prf)));Auto with algebra).
Simpl.
Exists (Build_finiteT in_range_prf).
Auto with algebra.
(Apply Trans with (x0 x2);Auto with algebra).

Generalize (Hrecx??H1).
Intros.
Assert (EXT v:(seq x A) | (seq_set (Seqtl x0)) =' (seq_set v)).
Exists (Seqtl x0).
Auto with algebra.
Generalize (H3 H4);Clear H4 H3;Intros.
Red in H3.
Inversion_clear H3.
Inversion_clear H4.
Red.
Exists (S x1).
Exists (head x0);;x2.
Assert (x:A)(in_part x B)->(x='(head x0)\/(in_part x (diff B (single (head x0))))).
Simpl.
Intros.
Case (classic x3='(head x0));Intro.
Left;Auto.
Right;Auto.
Simpl.
Red.
Intros.
Split.
Intro.
Generalize (H4 x3 H5);Clear H4;Intros.
Simpl.
Case H4;Clear H4;Intros.
Exists (Build_finiteT (lt_O_Sn x1)).
Auto.
Simpl in H3;Red in H3.
Generalize (H3 x3);Clear H3;Intros.
Inversion_clear H3.
Generalize (H6 H4);Clear H6;Intros.
Simpl in H3.
Inversion_clear H3.
NewDestruct x4.
Exists (Build_finiteT (lt_n_S??in_range_prf)).
(Apply Trans with (x2 (Build_finiteT in_range_prf));Auto with algebra). 
Intros.
Simpl in H5.
Inversion_clear H5.
NewDestruct x4.
NewDestruct index.
(Apply in_part_comp_l with (head x0);Auto with algebra).
Assert (included (diff B (single (head x0))) B).
Red.
Intros.
Simpl in H5.
Inversion_clear H5;Auto.
Red in H5.
(Apply H5;Auto with algebra).
(Apply in_part_comp_r with (seq_set x2);Auto with algebra).
Simpl.
Exists (Build_finiteT (lt_S_n n x1 in_range_prf)).
Auto.

Assert (included B (seq_set (Seqtl x0))).
Red.
Intros.
Red in H0.
Generalize (H0 ? H1).
Intro.
Assert (in_part x1 (seq_set x0)).
(Apply in_part_comp_r with C;Auto with algebra).
Clear H3;Simpl in H4.
Inversion_clear H4.
Assert ~x2='(Build_finiteT (lt_O_Sn x))in(fin (S x)).
Red;Red in H2;Intro;Apply H2.
(Apply in_part_comp_l with x1;Auto with algebra).
(Apply Trans with (x0 x2);Auto with algebra).
Simpl.
Assert (EXT i:(fin x) | x2 =' (Cases i of (Build_finiteT n Hn) => (Build_finiteT (lt_n_S??Hn)) end) in (fin (S x))).
NewDestruct x2.
NewDestruct index.
Simpl in H4.
Absurd O=O;Auto.
Clear H4.
Exists (Build_finiteT (lt_S_n??in_range_prf)).
Simpl.
Auto.
Inversion_clear H5.
Exists x3.
NewDestruct x3.
(Apply Trans with (x0 x2);Auto with algebra).
(Apply (Hrecx??H1);Auto with algebra).
Exists (Seqtl x0);Auto with algebra.
Qed.


