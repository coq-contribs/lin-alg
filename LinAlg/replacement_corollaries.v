(** * replacement_corollaries.v *)
Set Implicit Arguments.
Require Export replacement_theorem.
Require Export counting_elements.

Section MAIN.
Variable F:field.
Variable V:(vectorspace F).
(** - %\intoc{Corollary 1 to 1.10}% *)
Lemma finite_bases_always_equally_big : (n:Nat;beta:(basis V))
  (has_n_elements n beta) ->
    (Sset:(part_set V)) (lin_indep Sset) -> (has_n_elements n Sset) ->
      (is_basis Sset).
Intros.
Generalize replacement_theorem.
Intro p.
Generalize (p????H);Clear p;Intro p.
Assert (le n n);Auto.
Generalize (p?H0?H2 H1).
Clear p.
Intro.
Inversion_clear H3.
Inversion_clear H4.
Assert x='(empty beta).
Red in H3.
Inversion_clear H3.
Inversion_clear H4.
Simpl.
Red.
Split;Intros.
Simpl.
Simpl in H3.
Red in H3.
Simpl in H3.
Generalize (H3 (Build_subtype H4)).
Clear H3;Intro H3;Inversion_clear H3.
Generalize (H7 I);Clear H7 H8;Intro H3;Inversion_clear H3.
Generalize (minus_n_n n);Intro.
Generalize (cast_fin x2 (sym_eq ???H3)).
Auto with algebra.
Simpl in H4.
Contradiction.
Red.
Split.
2:Auto.
(Apply generates_comp with (union Sset (inject_subsets x)) (full V);Auto with algebra).
(Apply Trans with (union Sset (inject_subsets (empty beta)));Auto with algebra).
(Apply Trans with (union Sset (empty V));Auto with algebra).
(Apply union_comp;Auto with algebra).
Simpl.
Red.
Split;Intro.
2:Simpl in H6;Contradiction.
Simpl in H6.
Inversion_clear H6.
Inversion_clear x1.
Simpl in subtype_prf.
Contradiction.
Qed.

(** - %\intoc{Corollary 2 to 1.10}% (partly) *)
Lemma finite_basis_bounds_lin_indep_set_size :(n:Nat;beta:(basis V))
    (has_n_elements n beta) -> 
    (Sset:(part_set V))(has_at_least_n_elements (S n) Sset) ->
      (lin_dep Sset).
Intros.
Apply NNPP;Intro.

Inversion_clear H0.
Assert (EXT S1:(part_set V) | (included S1 Sset)/\(has_n_elements n S1)).
LetTac S1:= (seq_set (Map_embed (Seqtl x))).
Exists S1.
Split.
Red.
Intros.
Rename x0 into v.
Inversion_clear H0.
(Apply in_part_comp_l with (Map_embed (Seqtl x) x0);Auto with algebra).
Simpl.
NewDestruct x0.
Auto with algebra.
Red.
Exists (seq_set_seq (Map_embed (Seqtl x))).
Split.
Simpl;Red;Simpl.
Intros;Split;Intro;Auto.
Unfold subtype_image_equal.
Simpl.
NewDestruct x0.
Rename subtype_elt into v.
Rename subtype_prf into Hv.
Simpl in Hv.
Inversion_clear Hv.
Exists x0.
NewDestruct x0.
Simpl.
Auto.
Red.
Intros.
Simpl.
Unfold subtype_image_equal.
Simpl.
NewDestruct i;NewDestruct j;Simpl.
Intro.
(Apply (H2(Build_finiteT (lt_n_S index n in_range_prf))(Build_finiteT (lt_n_S index0 n in_range_prf0)));Auto with algebra).
Simpl.
Simpl in H0.
Auto with arith.
Inversion_clear H0.
Rename x0 into S1.
Inversion_clear H3.

Generalize (finite_bases_always_equally_big H).
Intro p.
Assert (lin_indep S1).
(Apply lin_indep_include with Sset;Auto with algebra).
Generalize (p?H3 H4).
Clear p;Intro.
Rename x into Sseq.
Assert (EXT x:V | (in_part x Sset) /\ ~(in_part x S1)).
(Apply has_extra_element_strong with n (S n);Auto with algebra).
Red.
Exists Sseq;Auto.
Inversion_clear H6.
Inversion_clear H7.
Assert (in_part x (span S1)).
Inversion_clear H5.
Red in H7.
(Apply in_part_comp_r with (full V);Auto with algebra).

Assert (lin_dep (union S1 (single x))).
Elim (lin_dep_vs_span_lemma H3 H8).
Intros.
(Apply H10;Auto with algebra).

Assert (included (union S1 (single x)) Sset).
Red.
Intros v H13.
Simpl in H13.
Inversion_clear H13.
Auto with algebra.
(Apply in_part_comp_l with x;Auto with algebra).

Assert (lin_dep Sset).
(Apply lin_dep_include with (union S1 (single x));Auto with algebra).
(Apply H1;Auto with algebra).
Qed.

(** - Corollary 2 to 1.10 (the rest): *)
Lemma finite_basis_bounds_lin_indep_set_size' :(n:Nat;beta:(basis V))
    (has_n_elements n beta) -> (Sset:(part_set V)) (lin_indep Sset) ->
      (has_at_most_n_elements n Sset).
Intros.
Generalize (finite_basis_bounds_lin_indep_set_size H).
Intro p;Generalize (p Sset);Clear p;Intro p.
(Apply not_at_least_then_at_most;Auto with algebra).
Qed.

(** - %\intoc{Corollary 3 to 1.10}% *)

Lemma all_finite_bases_equally_big : (n:Nat;beta:(basis V))
  (has_n_elements n beta) -> (Sset:(basis V))(has_n_elements n Sset).
Intros.
Generalize (finite_basis_bounds_lin_indep_set_size H).
Intro p;Generalize (p Sset);Clear p;Intro p.
Inversion H.
Assert (has_at_most_n_elements n Sset).
(Apply not_at_least_then_at_most;Auto with algebra).
Intro.
Generalize (p H1).
Elim (is_basis_prf Sset);Auto with algebra.

Inversion_clear H1.
Rename x0 into m.
Inversion_clear H2.
Elim (is_basis_prf beta);Intros.
Generalize (finite_basis_bounds_lin_indep_set_size' H3 H4).
Intros.
Inversion_clear H5.
Inversion_clear H6.

Assert x0=n.
Generalize has_n_elements_inj.
Intros.
(Apply (H6???H7??H);Auto with algebra).

Assert m=n.
Rewrite H6 in H7.
(Apply le_antisym;Auto with algebra).
Rewrite <- H6.
Auto.
Rewrite <- H8.
Auto.
Qed.

End MAIN.