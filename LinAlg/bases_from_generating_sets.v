(** * bases_from_generating_sets.v *)
Set Implicit Arguments.
Require Export bases.
Require Export finite_subsets.
Require Export lin_dep_facts.

Section MAIN.
Variable F:field.
Variable V:(vectorspace F).
Variable W0:(part_set V).
Variable H:(is_finite_subset W0).
Variable H0:(generates W0 (full V)).
(** - %\intoc{\bf Theorem 1.9}% in various flavours: *)
Lemma every_finite_generating_set_has_a_subset_that_is_a_basis :
    (EXT W:(part_set W0) | (is_basis (inject_subsets W))).
Inversion_clear H.
Inversion_clear H1.
Assert (EXT k:Nat | (EXT v:(seq k V) | (is_subseq v x0)/\(max_lin_indep (seq_set v) (seq_set x0)))).
(Apply seq_has_max_lin_indep_subseq;Auto with algebra).
Inversion_clear H1.
Inversion_clear H2.
Inversion_clear H1.
Assert (i:(fin x1))(in_part (x2 i) W0).
Intro.
(Apply in_part_comp_r with (seq_set x0);Auto with algebra).
Simpl.
Change  (EXT i0:(fin x) | (x2 i) =' (x0 i0)).
(Apply subseq_has_right_elements;Auto with algebra).
Exists (seq_set (cast_map_to_subset H1)).
Red.
Split.
Red.
Red in H0.
(Apply Trans with ((span W0)::(part_set V));Auto with algebra).
(Apply Trans with ((span (seq_set x0))::(part_set V));Auto with algebra).
Apply Trans with ((span (seq_set x2))::(part_set V)).
(Apply span_comp;Auto with algebra).
Unfold inject_subsets.
Simpl.
Red.
Simpl.
Split;Intros.
Inversion_clear H4.
NewDestruct x4.
Simpl in H5.
Generalize subtype_elt subtype_prf H5;Clear H5  subtype_prf subtype_elt. 
Intros w wp H5.
Inversion_clear wp.
Exists x4.
(Apply Trans with (subtype_elt w);Auto with algebra).
(Apply Trans with (subtype_elt (cast_map_to_subset H1 x4));Auto with algebra).

Inversion_clear H4.
Generalize (H1 x4);Intro.
Red in H4.
Assert (in_part ((Build_subtype H4)::W0) (seq_set (cast_map_to_subset H1))).
Simpl.
Exists x4.
Red.
Simpl.
Unfold cast_to_subset_fun.
Unfold Map_rect.
NewDestruct x2.
Simpl.
Auto with algebra.
Red in H6.
Exists (Build_subtype H6).
Simpl.
Auto with algebra.

Apply Sym.
(Apply max_lin_indep_subset_has_same_span;Auto with algebra).
Inversion_clear H3.
Inversion_clear H5.
(Apply lin_indep_comp with (seq_set x2);Auto with algebra).
Apply Sym.
Unfold inject_subsets.
Simpl.
Red.
Simpl.
Split;Intros.
Inversion_clear H5.
NewDestruct x4.
Simpl in H7.
Generalize subtype_elt subtype_prf H7;Clear H7 subtype_prf subtype_elt. 
Intros w wp H7.
Inversion_clear wp.
Exists x4.
(Apply Trans with (subtype_elt w);Auto with algebra).
(Apply Trans with (subtype_elt (cast_map_to_subset H1 x4));Auto with algebra).

Inversion_clear H5.
Generalize (H1 x4);Intro.
Red in H5.
Assert (in_part ((Build_subtype H5)::W0) (seq_set (cast_map_to_subset H1))).
Simpl.
Exists x4.
Red.
Simpl.
Unfold cast_to_subset_fun.
Unfold Map_rect.
NewDestruct x2.
Simpl.
Auto with algebra.
Red in H8.
Exists (Build_subtype H8).
Simpl.
Auto with algebra.
Qed.

Lemma every_finite_generating_set_includes_a_basis : 
  (EXT W:(basis V) | (included W W0)).
Elim every_finite_generating_set_has_a_subset_that_is_a_basis;Auto with algebra.
Intros.
Exists (Build_basis H1).
Simpl.
Red;Simpl.
Intros.
Inversion_clear H2.
(Apply in_part_comp_l with (subtype_elt (subtype_elt x1));Auto with algebra).
Qed.

Lemma every_finitely_generated_vectorspace_has_a_finite_basis :
  (EXT W:(part_set V) | (is_finite_subset W)/\(is_basis W)).
Intros.
Assert (EXT W:(part_set W0) | (is_basis (inject_subsets W))).
(Apply every_finite_generating_set_has_a_subset_that_is_a_basis;Auto with algebra).
Inversion_clear H1.
Exists (inject_subsets x).
Split;Auto.
(Apply included_reflects_is_finite_subset with W0;Auto with algebra).
Qed.
End MAIN.