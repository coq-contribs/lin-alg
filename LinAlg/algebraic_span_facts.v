(** * algebraic_span_facts.v *)
Set Implicit Arguments.
Require Export spans.
Require Export Inter.

Section MAIN.
Variable F:field.
Variable V:(vectorspace F).

Lemma span_idempotent: (S:(part_set V))
  (span S) =' (span (span S)) in (part_set V).
Simpl.
Red.
Split;Intro.
(Apply in_part_comp_r with ((span_ind (span S))::(part_set V));Auto with algebra).
Change (Pred_fun (span S) x) in H.
Simpl.
Exists (Immediately (Build_subtype H)).
Simpl.
Apply Refl.
(Apply Trans with ((span (span S))::(part_set V));Auto with algebra).

Assert (in_part x (span_ind (span S))).
(Apply in_part_comp_r with ((span (span S))::(part_set V));Auto with algebra).
Elim H0.
Intro.
Generalize x.
Elim x0.
Simpl.
Intros.
Red.
Exists O.
Exists (empty_seq F).
Exists (empty_seq S).
Simpl.
Auto.

Simpl.
Intro.
Elim c.
Intros c0 cp.
Elim cp.
Intros x1 H1.
Inversion H1.
Inversion H2.
Intros.
Red.
Exists x1.
Exists x2.
Exists x3.
(Apply Trans with c0;Auto with algebra).

Intros.
Clear H0 H x x0.
Simpl in H3.
Simpl.
Red.
Generalize (H1 (span_ind_injection s) (Refl ?)).
Generalize (H2 (span_ind_injection s0) (Refl ?)).
Intros.
Clear H1 H2.
Simpl in H H0.
Red in H H0.
Inversion H.
Inversion H0.
Exists (plus x0 x).
Inversion H1.
Inversion H2.
Exists x3++x2.
Inversion H4.
Inversion H5.
Exists x5++x4.
Apply Trans with (sum (mult_by_scalars x3 (Map_embed x5)))+'(sum (mult_by_scalars x2 (Map_embed x4))).
(Apply Trans with (span_ind_injection s)+'(span_ind_injection s0);Auto with algebra).
Apply Trans with (sum (mult_by_scalars x3 (Map_embed x5))++(mult_by_scalars x2 (Map_embed x4))).
Apply Sym.
(Apply sum_concat;Auto with algebra).
Apply Trans with (sum (mult_by_scalars x3++x2 (Map_embed x5)++(Map_embed x4))).
Unfold mult_by_scalars.
(Apply sum_comp;Auto with algebra).
Unfold mult_by_scalars.
Apply sum_comp.
Apply toMap.
(Apply pointwise_comp;Auto with algebra).
Intros.
Clear x0 H0 H x.
Simpl in H2.
Generalize (H1 (span_ind_injection s) (Refl?)).
Simpl. 
Unfold is_lin_comb.
Intro.
Inversion H.
Inversion H0.
Inversion H3.
Exists x.
Exists (pointwise (uncurry (RING_comp 1!F)) (const_seq x c) x0).
Exists x2.
(Apply Trans with (c mX (span_ind_injection s));Auto with algebra).
(Apply Trans with (c mX (sum (mult_by_scalars x0 (Map_embed x2))));Auto with algebra).
(Apply Trans with (sum (mult_by_scalars (const_seq x c) (mult_by_scalars x0 (Map_embed x2))));Auto with algebra).
Qed.

Lemma span_preserves_inclusion : (S,S':(part_set V))
  (included S S') -> (included (span S) (span S')).
Intros.
Red.
Intros.
Simpl in H0.
Red in H0.
Elim H0;Intros.
Elim H1;Intros.
Elim H2;Intro.
Simpl.
Red.
Exists x0.
Exists x1.
Exists (Map_include_map ? H x2).
(Apply Trans with (sum (mult_by_scalars x1 (Map_embed x2)));Auto with algebra).
Qed.

Hints Resolve span_preserves_inclusion : algebra.

Lemma span_of_union : (S,S':(part_set V))
  (span (union S S')) =' (span (union (span S) (span S'))) in (part_set V).
Intros.
Apply included_antisym.
(Apply span_smallest_subspace_containing_subset;Auto with algebra).
(Apply included2_union;Auto with algebra).
(Apply included_trans with (union (span S) (span S'));Auto with algebra).
(Apply included_trans with ((span S)::(part_set V));Auto with algebra).
(Apply included_trans with (union (span S) (span S'));Auto with algebra).
(Apply included_trans with ((span S')::(part_set V));Auto with algebra).
(Apply span_smallest_subspace_containing_subset;Auto with algebra).
Qed.

Lemma inclusion_generates : (S,S':(part_set V))
  (included S S') -> (generates S (full V))->(generates S' (full V)).
Intros.
Red in H0.
Red.
(Apply Trans with ((span S)::(part_set?));Auto with algebra).
(Apply included_antisym;Auto with algebra).
(Apply included_trans with (full V);Auto with algebra).
Qed.

Lemma subspace_span_characterisation : (W:(part_set V))
  (is_subspace W) <-> (span W)='W in (part_set V).
Intro.
Split.

Intros.
(Apply Trans with ((span_ind W)::(part_set V));Auto with algebra).
Simpl.
Red.
Split.
Intro.
Red in H.
Inversion_clear H.
Inversion_clear H2.
Simpl in H0.
Inversion_clear H0.
Generalize H2.
Generalize x.
Clear H2.
NewInduction x0.
Simpl.
Intros.
(Apply in_part_comp_l with (zero V);Auto with algebra).
Simpl.
Intros.
(Apply in_part_comp_l with (subtype_elt c);Auto with algebra).
Simpl.
Intros.
(Apply in_part_comp_l with (span_ind_injection x1) +' (span_ind_injection x2);Auto with algebra).
Intros.
Simpl in H2.
(Apply in_part_comp_l with (c mX (span_ind_injection x0));Auto with algebra).

Intro.
Simpl.
Red in H0.
Exists (Immediately (Build_subtype H0)).
Simpl.
Apply Refl.

Intro.
(Apply is_subspace_comp with ((span W)::(part_set V));Auto with algebra).
(Apply span_is_subspace;Auto with algebra).
Qed.

Lemma subspace_contains_all_lin_combs : (W:(subspace V);x:V)
  (is_lin_comb x W) -> (in_part x W).
Intros.
Assert (in_part x (span W)).
Simpl.
Auto.
Apply in_part_comp_r with ((span W)::(part_set V)).
Auto.
Elim (subspace_span_characterisation W).
Intros.
Apply H1.
Apply is_subspace_OK.
Qed.

Lemma span_intersect : (S,S':(part_set V))
  (included  (span (inter S S'))  (inter (span S) (span S'))).
Intros.
Red.
Intros.
Simpl in H.
Red in H.
Inversion_clear H.
Inversion_clear H0.
Inversion_clear H.
Simpl.
Split.
Red.
Exists x0.
Exists x1.
Assert (included (inter S S') S);Auto with algebra.
Exists (Map_include_map ? H x2).
(Apply Trans with (sum (mult_by_scalars x1 (Map_embed x2)));Auto with algebra).
Red.
Exists x0.
Exists x1.
Assert (included (inter S S') S');Auto with algebra.
Exists (Map_include_map ? H x2).
(Apply Trans with (sum (mult_by_scalars x1 (Map_embed x2)));Auto with algebra).
Qed.

End MAIN.