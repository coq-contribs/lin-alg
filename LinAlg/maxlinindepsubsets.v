(** * maxlinindepsubsets.v *)
Set Implicit Arguments.
(** - This file would be the book's chapter 1.7. It doesn't have the last place in the
 dependency graph (and hence in the coqdoc-generated documentation you may be reading
 now): the ``finite'' stuff of 1.6 isn't needed. Finiteness is usually harder to do in
 type theory than more general number-agnostic stuff---and this file goes to show, I
 guess... *)
Require Export bases.
Require Export lin_dep_facts.

Section defs.
Variable X:Setoid.
(** - ``B properly contains A'' means $A\subset B$ and $A\neq B$, so ``no member of F
 properly contains A'' is $\not\exists B\in F. A\subset B\wedge A\neq B$: *)
Definition maximal [F:(part_set (part_set X));A:(part_set X)] :=
  (in_part A F) /\ ~(EXT B:(part_set X) | (in_part B F)/\(included A B)/\~A='B).

Definition is_chain [F:(part_set (part_set X))] := (A,B:(part_set X))
  (in_part A F) -> (in_part B F) -> (included A B)\/(included B A).

(** - Quoting the Maximal Principle from page 50:

 Let $\cal F$ be a family of sets. If for each chain $\cal C\subset \cal F$ there
 exists a member of $\cal F$ that contains each member of $\cal C$, then $\cal F$
 contains a maximal element.*)

(** %\tocdef{MAXIMAL\_PRINCIPLE}% *)
Axiom MAXIMAL_PRINCIPLE : (F:(part_set (part_set X)))
    ( (C:(part_set (part_set X))) (is_chain C) -> (included C F) ->
      (EXT A:(part_set X) | (in_part A F) /\ 
             (B:(part_set X))(in_part B C)->(included B A)) )
 ->
    (EXT A:(part_set X) | (maximal F A)).
End defs.


(** - %\intoc{\bf Theorem 1.12}% says every maximally linearly independent subset of
 any generating set is a basis *)
Lemma max_lin_indep_subsets_of_generating_sets_are_bases :
  (F:field;V:(vectorspace F);W:(part_set V))
    (generates W (full V))-> (beta:(part_set V)) (max_lin_indep beta W) ->
      (is_basis beta).

Intros.
Red.
Assert (lin_indep beta).
Red in H0.
Inversion_clear H0.
Inversion_clear H2;Auto.
Split;Auto.

Cut (included W ((span beta)::(part_set?))).
Intro.
Red.
Red in H.
(Apply included_antisym;Auto with algebra).
(Apply included_comp with ((span W)::(part_set?)) ((span beta)::(part_set?));Auto with algebra).
(Apply span_smallest_subspace_containing_subset;Auto with algebra).

Apply NNPP;Intro.
Assert (EXT x:W | ~(in_part (W x) ((span beta)::(part_set?)))).
Apply NNPP;Intro;Apply H2.
Red.
Intros.
Apply NNPP;Intro.
Apply H3.
Red in H4;Exists (Build_subtype H4).
Intro;Apply H5.
Simpl in H6.
Simpl.
Auto.

Inversion_clear H3.
Assert ~(in_part (W x) beta).
Intro;Apply H4.
(Apply set_included_in_its_span;Auto with algebra).
Assert (lin_indep (union beta (single (W x)))).
Elim (lin_dep_vs_span_lemma H1 H3).
Intros.
Intro.
(Apply H4;Auto with algebra).

Red in H0.
Inversion_clear H0.
Inversion_clear H7.
(Apply H5;Auto with algebra).
(Apply H8;Auto with algebra).
(Apply in_part_comp_l with (subtype_elt x);Auto with algebra).
Qed.

(** - %\intoc{Corollary to 1.12}%: *)
Lemma basis_iff_max_lin_indep : (F:field;V:(vectorspace F);beta:(part_set V))
  (is_basis beta) <-> (max_lin_indep beta (full V)).
Split.
2:(Apply max_lin_indep_subsets_of_generating_sets_are_bases;Auto with algebra).
2:Red.
2:(Apply included_antisym;Auto with algebra).
Intro.
Red.
Split.
Red.
Simpl.
Auto.
Split.
Red in H.
Inversion_clear H.
Auto.
Red in H.
Inversion_clear H.
Intros.
Elim (lin_dep_vs_span_lemma H1 H2).
Intros.
(Apply H4;Auto with algebra).
Red in H0.
(Apply in_part_comp_r with (full V);Auto with algebra).
Qed.

Lemma basis_is_max_lin_indep : (F:field;V:(vectorspace F);beta:(basis V))
  (max_lin_indep beta (full V)).
Intros.
Elim (basis_iff_max_lin_indep beta).
Intros.
(Apply H;Auto with algebra).
Exact (is_basis_prf beta).
Qed.

(** - %\intoc{\bf Theorem 1.13}%: *)
Lemma max_lin_indep_subset_generated : (F:field;V:(vectorspace F);W:(part_set V))
  (lin_indep W) ->
    (EXT W':(part_set V) | (max_lin_indep W' (full V))/\(included W W')).
Intros.
Assert (pred_compatible [X:(part_set V)](included W X)/\(lin_indep X)).
Red.
Intros.
Inversion_clear H0.
Split.
(Apply included_comp with W x;Auto with algebra).
(Apply lin_indep_comp with x;Auto with algebra).
LetTac FF:=((Build_Predicate H0)::(part_set (part_set V))).
Cut (EXT W':(part_set V) | (maximal FF W')).
Intros.
Inversion_clear H1.
Rename x into W';Exists W'.
Red in H2.
Inversion_clear H2.
Simpl in H1.
Inversion_clear H1.
Split;Auto.
Red.
Split.
Red.
Simpl.
Auto.
Split.
Auto.
Intros.
Simpl in H3.
Apply NNPP;Intro;Apply H3.
Exists (union W' (single y)).
Split;Split.
Red.
Simpl.
Red in H2.
Intros.
Left;Auto.
Auto.
Red;Simpl;Auto.
Intro.
Red in H7.
(Apply H5;Auto with algebra).
Elim (H7 y).
Intros.
(Apply H9;Auto with algebra).

(Apply MAXIMAL_PRINCIPLE;Auto with algebra).
Intros.
Case (classic C='(empty?)).
Intro.
Exists W.
Split.
Simpl.
Split;Auto.
Red.
Auto.
Intros.
Assert (in_part B (empty?)).
(Apply in_part_comp_r with C;Auto with algebra).
Simpl in H5.
Contradiction.

Exists (union_part C).
Split.
2:Auto with algebra.
Simpl.
Split.
Assert (B:(part_set V))(in_part B C)->(included W B).
Intros.
Generalize (H2?H4).
Intros.
Simpl in H5.
Inversion_clear H5;Auto.
Assert (EXT A:(part_set V)| (in_part A C)).
Apply NNPP;Intro.
Apply H3.
Simpl.
Red.
Simpl.
Split;Intro.
Apply H5.
Exists x;Auto.
Contradiction.
Inversion_clear H5.
Rename x into A.
Generalize (H2?H6).
Intro.
Red.
Intros.
Simpl.
Exists A.
Split;Auto.
Simpl in H5.
Inversion_clear H5.
(Apply H8;Auto with algebra).

LetTac U:=(union_part C).
Elim (lin_dep_defs_eqv U).
Intros.
Apply H5.
Clear H4 H5.
Red.
Intros.
Intro;Apply H5.
Rename a into c.
Rename v into u.

Assert (EXT A:C | (i:(fin?))(in_part (U (u i)) (C A))).
Clear H6 H5 H4 c H2 H.
Generalize u;Clear u.
NewInduction n;Intro.
Assert (EXT A:C | (in_part (U (head u)) (C A))).
LetTac u1:=(head u).
NewDestruct u1.
Simpl in subtype_prf.
Inversion_clear subtype_prf.
Inversion_clear H.
Red in H2.
Exists (Build_subtype H2).
Simpl.
Auto.
Inversion_clear H.
Rename x into A.
Exists A.
Intro.
(Apply in_part_comp_l with (U (head u));Auto with algebra).
Simpl.
(Apply subtype_elt_comp;Auto with algebra).

Assert (EXT A:C | (in_part (U (head u)) (C A))).
LetTac u1:=(head u).
NewDestruct u1.
Simpl in subtype_prf.
Inversion_clear subtype_prf.
Inversion_clear H.
Red in H2.
Exists (Build_subtype H2).
Simpl.
Auto.
Inversion_clear H.
Rename x into A1.
Generalize (IHn (Seqtl u));Intro p;Inversion_clear p.
Rename x into A2345n.
Red in H1.
Assert (in_part (C A1) C)/\(in_part (C A2345n) C).
Split;Simpl;Auto with algebra.
Inversion_clear H4.
Generalize (H1??H5 H6).
Intro p.
Inversion_clear p.
Exists A2345n.
Assert (in_part (U (head u)) (C A2345n)).
(Apply H4;Auto with algebra).
Intro.
Clear H4 H5 H6.
NewDestruct i.
Clear IHn H3 H1 FF H0 W H2.
Generalize Dependent n.
NewDestruct index.
Intros.
(Apply in_part_comp_l with (U (head u));Auto with algebra).
Simpl;(Apply subtype_elt_comp;Auto with algebra).
Unfold head.
Intros.
(Apply in_part_comp_l with (U (Seqtl u (Build_finiteT (lt_S_n??in_range_prf))));Auto with algebra).
Simpl;(Apply subtype_elt_comp;Auto with algebra).
Exists A1.
Assert (i:(fin (S n)))(in_part (U (Seqtl u i)) (C A1)).
Intro;(Apply H4;Auto with algebra).
Intro.
Clear H4 H5 H6 H.
NewDestruct i.
Clear IHn H3 H1 FF H0 W.
Generalize Dependent n.
NewDestruct index.
Intros.
(Apply in_part_comp_l with (U (head u));Auto with algebra).
Simpl;(Apply subtype_elt_comp;Auto with algebra).
Unfold head.
Intros.
(Apply in_part_comp_l with (U (Seqtl u (Build_finiteT (lt_S_n??in_range_prf))));Auto with algebra).
Simpl;(Apply subtype_elt_comp;Auto with algebra).

Inversion_clear H7.
Rename x into A.
Assert (lin_indep (C A)).
NewDestruct A.
Assert (Pred_fun FF subtype_elt).
(Apply H2;Auto with algebra).
Simpl in H7.
Simpl.
Tauto.

Assert (i:(fin (S n)))(in_part (Map_embed u i) (C A)).
Intro;Simpl.
Simpl in H8;(Apply H8;Auto with algebra).
LetTac u':=((cast_map_to_subset H9)::(seq??)).
Cut (sum (mult_by_scalars c (Map_embed u'))) =' (zero V).
Cut (distinct u').
Cut (lin_indep' (C A)).
Intros.
Red in H10.
Generalize (H10?c?H11).
Intro.
Apply NNPP;Intro;(Apply H13;Auto with algebra).
Elim (lin_dep_defs_eqv (C A));Tauto.
Red;Red in H4.
Unfold u';Intros.
Intro.
Red in H4;(Apply (H4??H10);Auto with algebra).
(Apply Trans with  (sum (mult_by_scalars c (Map_embed u)));Auto with algebra).
Qed.

(** - %\intoc{Corollary to 1.13}% *)
Lemma every_vecsp_has_a_basis : (F:field;V:(vectorspace F))
  (EXT beta:(part_set V) | (is_basis beta)).
Intros.
Cut (EXT beta:(part_set V) | (max_lin_indep beta (full V))).
Intro.
Inversion_clear H.
Exists x.
Elim (basis_iff_max_lin_indep x);Auto.
Assert (lin_indep (empty V)).
(Apply empty_lin_indep;Auto with algebra).
Elim (max_lin_indep_subset_generated H).
Intros;Exists x;Tauto.
Qed.
