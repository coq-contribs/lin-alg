(** * bases.v *)
Set Implicit Arguments.
Require Export lin_dependence.
Require Export spans.
Require Export random_facts.

Section MAIN.
Variable F:field.
Variable V:(vectorspace F).

Section Defs.
(** %\tocdef{is\_basis}% *)
Definition is_basis [X:(part_set V)] : Prop := (generates X (full V)) /\ (lin_indep X).

Lemma is_basis_comp : (X,Y:(part_set V)) X='Y->(is_basis X)->(is_basis Y).
Intros.
Red;Red in H0.
Inversion_clear H0;Split.
(Apply generates_comp with X (full V);Auto with algebra).
(Apply lin_indep_comp with X;Auto with algebra).
Qed.

(** %\tocdef{basis}% *)
Record basis : Type :=
{ basis_carrier :> (Predicate V)
; is_basis_prf  : (is_basis basis_carrier) }.
End Defs.

Lemma basis_prop : (X:basis;x:V)(is_lin_comb x X).
Intros.
Red.
Elim X.
Clear X.
Intros X H.
Red in H.
Inversion_clear H.
Red in H0.
Unfold span in H0.
Unfold is_lin_comb in H0.
Simpl in H0.
Red in H0.
Simpl in H0.
Generalize (H0 x).
Clear H0.
Unfold is_lin_comb.
Intros (H',H0).
(Apply H0;Auto with algebra).
Qed.

Lemma basis_prop_strong : (n:Nat;v:(seq n V))
  (is_basis (seq_set v))->
    (x:V)(EXT a:(seq n F) | (sum (mult_by_scalars a v))=' x).
Intros.
Generalize (basis_prop (Build_basis H) x).
Intro.
Generalize (span_ind_eqv_span (seq_set v) x).
Intros.
Inversion_clear H1.
Generalize (H2 H0).
Clear H0 H2 H3;Intro H'.
Inversion_clear H'.
Generalize H0;Clear H0.
Generalize x;Clear x.
Elim x0.
Intros.
Exists (const_seq n (zero F)).
Simpl in H0.
(Apply Trans with (zero V);Auto with algebra).
Apply sum_of_zeros;Intro;Simpl;Auto with algebra arith.
Intro c.
Simpl in c.
Elim c.
Simpl.
Intros.
Inversion_clear subtype_prf.
Generalize H1;Clear H1.
Elim x1.
Intros x2 y H1.
Exists (Basisvec_Fn F y).
(Apply Trans with subtype_elt;Auto with algebra).
(Apply Trans with (v (Build_finiteT y));Auto with algebra).
Apply Sym.
Apply projection_via_mult_by_scalars.
Intros.
Generalize (H0 (span_ind_injection s) (Refl (span_ind_injection s))).
Generalize (H1 (span_ind_injection s0) (Refl (span_ind_injection s0))).
Intros.
Clear H0 H1.
Inversion_clear H3.
Inversion_clear H4.
Exists (pointwise (sgroup_law_map F)::(Map??) x1 x2).
Simpl in H2.
Apply Trans with (sum (pointwise (sgroup_law_map V) (mult_by_scalars x1 v) (mult_by_scalars x2 v))).
Apply sum_comp.
Simpl.
Red.
Intro.
Simpl.
(Apply Trans with ((x1 x3)+'(x2 x3)) mX (v x3);Auto with algebra).
(Apply Trans with ((x1 x3) mX (v x3))+'((x2 x3) mX (v x3));Auto with algebra).
Apply Trans with (sum (mult_by_scalars x1 v))+' (sum (mult_by_scalars x2 v)).
Generalize sum_of_sums.
Intro.
Generalize (H3 n V (mult_by_scalars x1 v) (mult_by_scalars x2 v)).
Intros.
Simpl in H4.
Apply H4.
(Apply Trans with (span_ind_injection s0)+'(span_ind_injection s);Auto with algebra).
(Apply Trans with (span_ind_injection s)+'(span_ind_injection s0);Auto with algebra).
Intros.
Generalize (H0 (span_ind_injection s) (Refl (span_ind_injection s))).
Intro.
Clear H0.
Inversion_clear H2.
Exists (pointwise (uncurry (!RING_comp F)) (const_seq n c) x1).
Apply Trans with (sum (mult_by_scalars (const_seq n c) (mult_by_scalars x1 v))).
Apply sum_comp.
Simpl.
Red.
Intro.
Simpl.
Auto with algebra.
(Apply Trans with  c mX (sum (mult_by_scalars x1 v));Auto with algebra).
Simpl in H1.
(Apply Trans with (c mX (span_ind_injection s));Auto with algebra).
Qed.

Section Nice_basis_properties.

Variable x:V.
Variable n:Nat.
Variable b:(seq n V).
Variable Db:(distinct b).
Variable Bb:(is_basis (seq_set b)).

Local difference_seq : (G:group;a,a':(seq n G))(seq n G).
Intros.
(Apply (Build_Map 3![i:(fin n)]((a i)+'(min (a' i))));Auto with algebra).
Red.
Intros.
(Apply SGROUP_comp;Auto with algebra).
Defined.

(** - %\intoc{\bf Theorem 1.7}% *)
Lemma basis_expansion_uniqueness : (a,a':(seq n F)) 
  (sum (mult_by_scalars a b))='x -> (sum (mult_by_scalars a' b))='x ->
    a='a'.
Intros.
Cut (sum (mult_by_scalars (difference_seq a a') b))='(zero V).
Intro.
Cut (i:(fin n))(a i)+'(min (a' i))='(zero F).
Intro.
Cut (i:(fin n))(a i)='(a' i).
Simpl.
Red.
Auto.
Intro.
(Apply min_inj;Auto with algebra).
Unfold is_basis in Bb.
Inversion_clear Bb.
Generalize (lin_indep_prop Db H3 H1).
Auto.
(Apply Trans with x+'(min x);Auto with algebra).
(Apply Trans with (sum (mult_by_scalars a b))+'(min (sum (mult_by_scalars a' b)));Auto with algebra).
Apply Trans with (sum (mult_by_scalars a b))+'((min one)mX(sum (mult_by_scalars a' b))).
Apply Trans with (sum (mult_by_scalars a b))+'(sum (mult_by_scalars (const_seq ? (min one)) (mult_by_scalars a' b))).
Apply Trans with (sum (pointwise (sgroup_law_map V) (mult_by_scalars a b)(mult_by_scalars (const_seq ? (min one)) (mult_by_scalars a' b)))).
Apply sum_comp.
Simpl.
Red.
Simpl.
Intro.
(Apply Trans with ((a x0)mX(b x0))+'((min one)mX((a' x0)mX(b x0)));Auto with algebra).
(Apply Trans with ((a x0)mX(b x0))+'(((min one)rX(a' x0))mX(b x0));Auto with algebra).
(Apply Trans with ((a x0)+'((min one)rX(a' x0))) mX (b x0);Auto with algebra).
(Apply Trans with ((a x0)+'(min (a' x0))) mX (b x0);Auto with algebra).
(Apply MODULE_comp;Auto with algebra).
(Apply SGROUP_comp;Auto with algebra).
(Apply Trans with (min (one rX (a' x0)));Auto with algebra).
(Apply (!sum_of_sums n V (mult_by_scalars a b) (mult_by_scalars (const_seq n (min one)) (mult_by_scalars a' b)));Auto with algebra).
(Apply SGROUP_comp;Auto with algebra).
(Apply SGROUP_comp;Auto with algebra).
(Apply Trans with (min (one mX (sum (mult_by_scalars a' b))));Auto with algebra).
Qed.

End Nice_basis_properties.

(* Alas, we may not make a function, eating a vector and a basis, and returning the *)
(* associated scalars of the expansion :-( The reason being: we only know that *)
(* such a sequence EXTsists, ie we only have a noninformative proof of the fact *)
(* and we may not make an informative object (sequence) from the proof :-( :-( :'-( *)

End MAIN.