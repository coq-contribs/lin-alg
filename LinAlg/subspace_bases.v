(** * subspace_bases.v *)
Set Implicit Arguments.
Require Export bases.
Require Export subspace_dim.

Lemma generates_inject_subsets : 
(F:field;V:(vectorspace F);W:(subspace V);S,X:(part_set W))
  (generates S X) -> (generates (inject_subsets S) (inject_subsets X)).
Intros.
Red;Red in H.
Apply Trans with ((span_ind (inject_subsets S))::(part_set V));Auto with algebra.
Assert X='(span_ind S) in (part_set W).
Apply Trans with ((span S)::(part_set W));Auto with algebra.
Split;Intros.
Simpl in H1.
Inversion_clear H1.
Simpl.
Clear H.
Simpl in H0.
Red in H0.
LetTac x0S:=(span_ind_uninject x0).
LetTac xW:=(span_ind_injection x0S).
Elim (H0 xW).
Intros.
Cut (in_part xW (span_ind_set 2!W S)).
Intro.
Generalize Dependent (H1 H3);Intro p;Red in p.
Exists (Build_subtype p).
Simpl.
Unfold xW x0S.
Apply Trans with (span_ind_injection x0);Auto with algebra.
Apply span_ind_uninject_prop.
Simpl.
Exists x0S.
Red.
Unfold xW x0S.
Auto with algebra.

Simpl in H1.
Inversion_clear H1.
Simpl.
Clear H.
Elim (H0 (subtype_elt x0)).
Intros.
Assert (in_part (subtype_elt x0) X);Auto with algebra.
Generalize Dependent (H H3);Intro.
Simpl in H4.
Inversion_clear H4.
Clear H H1 H3.
Red in H5.
Generalize Dependent x0.
Generalize Dependent x.
NewInduction x1;Intros.

Exists (Zerovector (inject_subsets S)).
Apply Trans with (subtype_elt (subtype_elt x0));Auto with algebra.

Exists (Immediately (inject_subsetsify c)).
Apply Trans with (subtype_elt (subtype_elt x0));Auto with algebra.

LetTac x0V:=(subtype_elt (span_ind_injection x0)).
Elim (H0 (span_ind_injection x0));Intros.
Assert (in_part (span_ind_injection x0) (span_ind 2!W S)).
Simpl.
Exists x0.
Red;Auto with algebra.
Generalize Dependent (H1 H3);Intro p;Red in p.
Generalize Dependent (IHx0 x0V (Build_subtype p)).
Intro.
Cut x0V='(subtype_elt (subtype_elt (Build_subtype p))).
Intro q;Generalize Dependent (H4 q);Clear H4 q;Intro H4.
Cut (subtype_elt (subtype_elt (Build_subtype p))) =' x0V.
Intro q;Generalize Dependent (H4 q);Clear H4 q;Intro H4.
Inversion_clear H4.
Clear p H3 H1 H.

LetTac x2V:=(subtype_elt (span_ind_injection x2)).
Elim (H0 (span_ind_injection x2));Intros.
Assert (in_part (span_ind_injection x2) (span_ind 2!W S)).
Simpl.
Exists x2.
Red;Auto with algebra.
Generalize Dependent (H1 H3);Intro p;Red in p.
Generalize Dependent (IHx2 x2V (Build_subtype p)).
Intro.
Cut x2V='(subtype_elt (subtype_elt (Build_subtype p))).
Intro q;Generalize Dependent (H4 q);Clear H4 q;Intro H4.
Cut (subtype_elt (subtype_elt (Build_subtype p))) =' x2V.
Intro q;Generalize Dependent (H4 q);Clear H4 q;Intro H4.
Inversion_clear H4.
Clear p H3 H1 H.
Exists (Plusvector x3 x4).
Apply Trans with (subtype_elt (subtype_elt x1));Auto with algebra.
Apply Trans with(subtype_elt (span_ind_injection (Plusvector x0 x2)));Auto with algebra.
(* Simpl. takes too much time *)
Apply Trans with (subtype_elt (span_ind_injection x0)+'(span_ind_injection x2));[Apply subtype_elt_comp;Simpl;Red;Apply Refl|Idtac].
Apply Trans with (span_ind_injection x3)+'(span_ind_injection x4);[Idtac|Simpl;Red;Apply Refl].
Apply Trans with (subtype_elt (span_ind_injection x0))+'(subtype_elt (span_ind_injection x2)).
Simpl.
Apply Refl.
Fold x0V.
Fold x2V.
Apply SGROUP_comp;Auto with algebra.
Simpl.
Apply Refl.
Simpl;Apply Refl.
Simpl;Apply Refl.
Simpl;Apply Refl.

LetTac x1V:=(subtype_elt (span_ind_injection x1)).
Elim (H0 (span_ind_injection x1));Intros.
Assert (in_part (span_ind_injection x1) (span_ind 2!W S)).
Simpl.
Exists x1.
Red;Auto with algebra.
Generalize Dependent (H1 H3);Intro p;Red in p.
Generalize Dependent (IHx1 x1V (Build_subtype p)).
Intro.
Cut x1V='(subtype_elt (subtype_elt (Build_subtype p))).
Intro q;Generalize Dependent (H4 q);Clear H4 q;Intro H4.
Cut (subtype_elt (subtype_elt (Build_subtype p))) =' x1V.
Intro q;Generalize Dependent (H4 q);Clear H4 q;Intro H4.
Inversion_clear H4.
Clear p H3 H1 H.
Exists (Multvector c x2).
Apply Trans with (subtype_elt (subtype_elt x0));Auto with algebra.
Apply Trans with (subtype_elt (span_ind_injection (Multvector c x1)));Auto with algebra.
Simpl.
Apply MODULE_comp;Auto with algebra.
Simpl.
Apply Refl.
Simpl;Apply Refl.
Qed.

Lemma bases_equal_then_subspace_equal :
  (F:field;V:(vectorspace F);W1,W2:(subspace V);b1:(basis W1);b2:(basis W2))
    (inject_subsets b1)='(inject_subsets b2) -> W1='W2 in (part_set V).
Intros.
NewDestruct b1;NewDestruct b2.
Rename basis_carrier into b1.
Rename basis_carrier0 into b2.
Simpl in H.
Inversion_clear is_basis_prf;Inversion_clear is_basis_prf0.

Assert (generates (inject_subsets b1) W1).
Apply generates_comp with (inject_subsets b1) (inject_subsets (full W1));Auto with algebra.
Apply (inject_subsets_full_inv W1).
Apply generates_inject_subsets.
Auto.

Assert (generates (inject_subsets b2) W2).
Apply generates_comp with (inject_subsets b2) (inject_subsets (full W2));Auto with algebra.
Apply (inject_subsets_full_inv W2).
Apply generates_inject_subsets.
Auto.

Split;Intro.
Generalize Dependent is_lin_comb_from_generates.
Intro.

Red in H5.
Elim (H5 x);Intros.
Apply H8.
Simpl.

Apply H7 with (W1::(part_set V));Auto with algebra.
Apply generates_comp with (inject_subsets b1) (W1::(part_set V));Auto with algebra.

Generalize Dependent is_lin_comb_from_generates.
Intro.

Red in H4.
Elim (H4 x);Intros.
Apply H8.
Simpl.

Apply H7 with (W2::(part_set V));Auto with algebra.
Apply generates_comp with (inject_subsets b2) (W2::(part_set V));Auto with algebra.
Qed.

