(** * spans.v *)
Set Implicit Arguments.
(** - Spans can be defined in two ways: (1) the span of a subset $S\subset V$ is
 the subspace of all linear combinations of $S$ or (2) it is the set defined
 inductively by
  -- $0\in span(S)$
  -- $v\in S\to v\in span(S)$
  -- $v,v'\in S\to v+v'\in span(S)$
  -- $v\in S, c\in F\to cv\in span(S)$

 These definitions are proved equivalent. Notice how we must first define the formal
 expressions for these vectors and then inject them into the final set.

 Also $span(S)$ is the smallest subspace containing $S$ and some other easy lemmas *)

Require Export lin_combinations.
Require Export subspaces.

Section spans.
Variable F:field.
Variable V:(vectorspace F).
Definition span_set :(part_set V)->(part_set V) := [S](is_lin_comb_pred S).

(** %\tocdef{span}% *)
Definition span : (part_set V)->(subspace V).
Intro S.
Apply alt_Build_subspace with (span_set S).
Red;Split;Try Split.
Simpl.
Red.
Exists O.
Exists (empty_seq F).
Exists (empty_seq S).
Simpl.
Auto with algebra.
Intros;Simpl in H H0;Simpl;Red in H H0;Red.
Inversion_clear H;Inversion_clear H0;Inversion_clear H;Inversion_clear H1;Inversion_clear H0;Inversion_clear H.
Exists (plus x0 x1).
Exists x3++x2.
Exists x5++x4.
(Apply Trans with (sum (mult_by_scalars x3 (Map_embed x5)))+'(sum (mult_by_scalars x2 (Map_embed x4)));Auto with algebra).
(Apply Trans with (sum (mult_by_scalars x3 (Map_embed x5))++(mult_by_scalars x2 (Map_embed x4)));Auto with algebra).
(Apply Trans with (sum (mult_by_scalars x3++x2 (Map_embed x5)++(Map_embed x4)));Auto with algebra).
Intros.
Red;Red in H.
Simpl;Simpl in H.
Red;Red in H.
Inversion_clear H;Inversion_clear H0;Inversion_clear H.
Exists x0;Exists (pointwise (uncurry (RING_comp 1!F)) (const_seq x0 c) x1);Exists x2.
(Apply Trans with (sum (mult_by_scalars (const_seq x0 c) (mult_by_scalars x1 (Map_embed x2))));Auto with algebra).
(Apply Trans with (c mX (sum (mult_by_scalars x1 (Map_embed x2))));Auto with algebra).
Defined.

Lemma span_comp: (S,S':(part_set V))S='S'->(span S)='(span S')in(part_set V).
Intros.
Simpl.
Red.
Simpl.
Intro.
Split.
Intro.
(Apply is_lin_comb_comp with x S;Auto with algebra).
Intro.
(Apply is_lin_comb_comp with x S';Auto with algebra).
Qed.

(** - %\intoc{\bf Theorem 1.5}% *)
Lemma span_is_subspace : (S:(part_set V)) (is_subspace (span S)).
Intro;Apply is_subspace_OK.
Qed.
End spans.

Hints Resolve span_comp : algebra.

Section spans_inductively_defined.
Variable F:field.
Variable V:(vectorspace F).
Variable S:(part_set V).
(** - The type of formal expressions *)
Inductive span_ind_formal : Type :=
  Zerovector : span_ind_formal
| Immediately : S -> span_ind_formal
| Plusvector : span_ind_formal -> span_ind_formal -> span_ind_formal
| Multvector : F -> span_ind_formal -> span_ind_formal.

(** - The injection into the `inductively defined' span *)
Fixpoint span_ind_injection [X:span_ind_formal]: V:=
Cases X of
  Zerovector => (zero V)
| (Immediately s) => (subtype_elt s)
| (Plusvector x y) => (span_ind_injection x) +' (span_ind_injection y)
| (Multvector a x) => a mX (span_ind_injection x)
end.

Definition span_ind_set : (part_set V).
Simpl.
Apply (Build_Predicate 2!([v:V](EXT X:span_ind_formal | v='(span_ind_injection X)))).
Red.
Intros.
Inversion H.
Exists x0.
(Apply Trans with x;Auto with algebra).
Defined.

(** %\tocdef{span\_ind}% *)
Definition span_ind : (subspace V).
(Apply alt_Build_subspace with span_ind_set;Auto with algebra).
Red.
Split;Try Split;Simpl.
Exists Zerovector.
Simpl.
Auto with algebra.
Intros.
Inversion_clear H;Inversion_clear H0.
Exists (Plusvector x0 x1).
Simpl.
Auto with algebra.
Intros.
Inversion_clear H.
Exists (Multvector c x0).
Simpl.
Auto with algebra.
Defined.

Definition lin_comb_ind  [v:V]: Prop := (in_part v span_ind).
End spans_inductively_defined.

Section spans_eqv.

Variable F:field.
Variable V:(vectorspace F).

Lemma span_ind_eqv_span : (S:(part_set V))
 ((v:V)( (is_lin_comb v S)<->(lin_comb_ind S v) )).
Intros.
Split.
Intro.
Inversion_clear H.
Generalize H0;Clear H0.
Generalize v.
Induction x.
Intros v0 H0.
Inversion_clear H0.
Inversion_clear H.
Simpl in H0.
Unfold lin_comb_ind.
Simpl.
Exists (Zerovector S).
Simpl.
Assumption.
(* Induction step *)
Intros.
Inversion_clear H0.
Inversion_clear H.
Unfold lin_comb_ind.
Simpl.
(********)
LetTac x0_0 := (head x0).
LetTac x1_0 := (head x1). 
LetTac vhd:=(x0_0 mX (S (x1_0))).
LetTac vtl:=((mult_by_scalars (Seqtl x0) (Map_embed (Seqtl x1)))::(seq x V)). 
Cut v0 =' vhd +' (sum vtl).
Intro.
Generalize (Hrecx (sum vtl)).
Intro.
Cut (EXT a:(seq x F) | (EXT w:(seq x S) | (sum vtl)=' (sum (mult_by_scalars a (Map_embed w))))).
Intro.
Generalize (H1 H2).
Intro.
Unfold lin_comb_ind in H3.
Simpl in H3.
Inversion H3.
Exists (Plusvector (Multvector x0_0 (Immediately x1_0)) x2).
Simpl.
(Apply Trans with (x0_0 mX (S x1_0))+'(sum vtl);Auto with algebra).
(* that was the real work *)
Exists (Seqtl x0).
Exists (Seqtl x1).
Unfold vtl.
(Apply sum_comp;Auto with algebra).
(**)
Unfold vhd vtl x0_0 x1_0.
(Apply Trans with (sum (mult_by_scalars x0 (Map_embed x1)));Auto with algebra).
Apply Trans with (sum (mult_by_scalars (hdtl x0) (Map_embed (hdtl x1)))).
Unfold mult_by_scalars.
Apply sum_comp.
Apply toMap.
(Apply pointwise_comp;Auto with algebra).
Unfold hdtl.
Unfold mult_by_scalars.
(Apply Trans with (sum ((uncurry (MODULE_comp 1!(F) 2!V)) (couple (head x0) (S (head x1))));;(pointwise (uncurry (MODULE_comp 1!(F) 2!V))(Seqtl x0)(Map_embed (Seqtl x1))));Auto with algebra).
Intros.
Inversion_clear H.
Generalize H0;Clear H0.
Generalize v;Clear v.
Elim x.
Intros.
Unfold is_lin_comb.
Exists O.
Exists (const_seq O (zero F)).
Simpl.
Exists (empty_seq S).
Assumption.
Intros.
Unfold is_lin_comb.
Exists (1).
Exists (const_seq (1) one::F).
Exists (const_seq (1) c).
Simpl.
(Apply Trans with (subtype_elt c);Auto with algebra).
(Apply Trans with (one mX (subtype_elt c));Auto with algebra).
Unfold is_lin_comb.
Intros.
Generalize (H ? (Refl (span_ind_injection s))).
Generalize (H0 ? (Refl (span_ind_injection s0))).
Clear H H0.
Intros.
Inversion_clear H0.
Inversion_clear H2.
Inversion_clear H0.
Inversion_clear H.
Inversion_clear H0.
Inversion_clear H.
Exists (plus x0 x3).
Exists x1++x4.
Exists x2++x5.
(Apply Trans with (span_ind_injection s)+'(span_ind_injection s0);Auto with algebra).
(Apply Trans with (sum (mult_by_scalars x1 (Map_embed x2)))+'(span_ind_injection s0);Auto with algebra).
(Apply Trans with (sum (mult_by_scalars x1 (Map_embed x2)))+'(sum (mult_by_scalars x4 (Map_embed x5)));Auto with algebra).
(Apply Trans with (sum (mult_by_scalars x1 (Map_embed x2))++(mult_by_scalars x4 (Map_embed x5)));Auto with algebra).
Unfold mult_by_scalars.
(Apply sum_comp;Auto with algebra).
(Apply Trans with (pointwise (uncurry (MODULE_comp 1!F 2!V)) x1++x4 (Map_embed x2)++(Map_embed x5));Auto with algebra).

Intros.
Generalize (H ? (Refl (span_ind_injection s))).
Unfold is_lin_comb.
Intro.
Inversion_clear H1.
Inversion_clear H2.
Inversion_clear H1.
Exists x0.
Exists (pointwise (uncurry (RING_comp 1!F)) (const_seq x0 c) x1).
Exists x2.
Simpl in H0.
(Apply Trans with c mX (span_ind_injection s);Auto with algebra).
(Apply Trans with c mX (sum (mult_by_scalars x1 (Map_embed x2)));Auto with algebra).
(Apply Trans with (sum (mult_by_scalars (const_seq x0 c) (mult_by_scalars x1 (Map_embed x2))));Auto with algebra).
Qed.

Lemma span_is_span_ind : (S:(part_set V)) (span S) =' (span_ind S) in (part_set V).
Intro.
Simpl.
Red.
Simpl.
Intro.
Generalize (span_ind_eqv_span S x).
Intro.
Unfold lin_comb_ind in H.
Simpl in H.
Unfold iff in H.
Auto.
Qed.

Lemma span_ind_comp : (S,S':(part_set V))
 S='S' -> (span_ind S) =' (span_ind S') in (part_set V).
Intros.
(Apply Trans with ((span S)::(part_set V));Auto with algebra).
Apply Sym;(Apply span_is_span_ind;Auto with algebra).
(Apply Trans with ((span S')::(part_set V));Auto with algebra).
(Apply span_is_span_ind;Auto with algebra).
Qed.

End spans_eqv.

Hints Resolve span_is_span_ind span_ind_comp: algebra.

Section a_nice_fact_on_spans.
(** - %\intoc{Theorem 1.5 (cont'd)}% *)
Lemma span_smallest_subspace_containing_subset :
 (F:field;V:(vectorspace F);W:(subspace V);S:(part_set V))
   (included S W)->(included (span S) W).
Intros.
Red.
Simpl.
Red in H.
Intros.
Generalize (span_ind_eqv_span S x).
Unfold iff.
Intros (LC1,LC2).
Generalize (LC1 H0).
Intro.
Inversion H1.
Generalize H2;Clear H2.
Cut (is_subspace W).
Unfold is_subspace.
Intros (W1,(W2,W3)).
2:(Apply is_subspace_OK;Auto with algebra).
Clear H0 H1 LC1 LC2.
Generalize x.
Clear x.
Elim x0.
Simpl.
Intros.
(Apply in_part_comp_l with (zero V);Auto with algebra).
Simpl.
Intros.
(Apply in_part_comp_l with (subtype_elt c);Auto with algebra).
Intros.
Simpl in H2.
(Apply in_part_comp_l with (span_ind_injection s)+'(span_ind_injection s0);Auto with algebra).
Intros.
Simpl in H2.
(Apply in_part_comp_l with c mX (span_ind_injection s);Auto with algebra).
Qed.

(* and of course the obvious *)
Lemma set_included_in_its_span : (F:field;V:(vectorspace F);S:(part_set V))
  (included S (span S)).
Intros.
Red.
Intros.
(Apply in_part_comp_r with ((span_ind S)::(part_set V));Auto with algebra).
Simpl.
Exists (Immediately (Build_subtype H)).
Simpl.
Apply Refl.
Qed.

End a_nice_fact_on_spans.

Hints Resolve set_included_in_its_span : algebra.


(** %\tocdef{generates}% *)
Definition generates [F:field;V:(vectorspace F);S,W:(part_set V)] :=
  (span S) =' W in (part_set V).

Lemma generates_comp : (F:field;V:(vectorspace F);S,S',W,W':(part_set V))
  S='S' -> W='W' -> (generates S W)->(generates S' W').
Intros.
Red;Red in H1.
(Apply Trans with ((span S)::(part_set V));Auto with algebra).
Apply Trans with (W::(part_set V));Auto with algebra.
Qed.

Lemma generated_subsets_are_subspaces : (F:field;V:(vectorspace F);S,W:(part_set V))
  (generates S W) -> (is_subspace W).
Intros.
Red in H.
Apply is_subspace_comp with ((span S)::(part_set V));Auto.
Apply is_subspace_OK.
Qed.

Lemma is_lin_comb_from_generates : (F:field;V:(vectorspace F);S,W:(part_set V))
  (generates S W) -> (x:V)(in_part x W)->(is_lin_comb x S).
Intros.
Red in H.
Simpl in H.
Red in H.
Generalize (H x);Intro.
Inversion_clear H1.
Simpl in H3.
Auto.
Qed.

Lemma generates_then_is_lin_comb : (F:field;V:(vectorspace F);S,W:(part_set V))
  (generates S W) -> (x:V)(in_part x W)->(is_lin_comb x S).
Exact is_lin_comb_from_generates.
Qed.

Lemma is_lin_comb_from_generates' :
  (F:field;V:(vectorspace F);S:(part_set V);W:(subspace V))
    (generates S W) -> (x:W)(is_lin_comb (subtype_elt x) S).
Intros.
Apply is_lin_comb_from_generates with (W::(part_set V));Auto with algebra.
Qed.