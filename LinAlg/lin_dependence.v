(** * lin_dependence.v *)
Set Implicit Arguments.
Section MAIN.
Require Export Union.
Require Export subspaces.
Require Export cast_between_subsets.
Require Export mult_by_scalars.
Require Export sums.
Require Export seq_set_seq.
Require Export distinct.
Require Export const.

Section defs.
Variable F:field.
Variable V:(vectorspace F).

(** %\tocdef{lin\_{\em[in]}dep}% *)
Definition lin_dep := [X:(part_set V)]
  (EXT n:Nat | (EXT a:(seq (S n) F) | (EXT v:(seq (S n) X) |
    (distinct v)
      /\ ~a='(const_seq (S n) (zero F))
        /\(sum (mult_by_scalars a (Map_embed v)))=' (zero V)))).

Definition lin_indep [X:(part_set V)] := ~(lin_dep X).

Definition lin_indep' [X:(part_set V)] :=
  (n:Nat;a:(seq (S n) F);v:(seq (S n) X))
    (distinct v)
      -> ~a='(const_seq (S n) (zero F))
        -> ~(sum (mult_by_scalars a (Map_embed v))) =' (zero V).

Lemma lin_dep_comp : (X,Y:(part_set V))
  X='Y -> (lin_dep X)->(lin_dep Y).
Intros.
Red.
Red in H0.
Inversion_clear H0.
Exists x.
Inversion_clear H1.
Exists x0.
Inversion_clear H0.
Exists (Map_to_equal_subsets H x1).
Split.
Inversion_clear H1.
Repeat Red in H0.
Repeat Red.
Intros.
(Apply (H0 i j);Auto with algebra).
Simpl.
Red.
Simpl in H3.
Red in H3.
(Apply Trans with (subtype_elt (x1 i));Auto with algebra).
(Apply Trans with (subtype_elt (Map_to_equal_subsets H x1 i));Auto with algebra). 
(Apply Trans with (subtype_elt (x1 j));Auto with algebra).
(Apply Trans with (subtype_elt (Map_to_equal_subsets H x1 j));Auto with algebra). 
Split.
Inversion_clear H1.
Inversion_clear H2.
Auto.
Inversion_clear H1.
Inversion_clear H2.
(Apply Trans with (sum (mult_by_scalars x0 (Map_embed x1)));Auto with algebra). 
Qed.

Lemma lin_indep_comp : (X,Y:(part_set V))
  X='Y -> (lin_indep X)->(lin_indep Y).
Intros.
Red.
Red.
Red in H0.
Red in H0.
Intro.
Apply H0.
(Apply lin_dep_comp with Y;Auto with algebra).
Qed.

Lemma lin_dep_defs_eqv : (X:(part_set V))(lin_indep X)<->(lin_indep' X).
Unfold lin_indep.
Unfold lin_indep'.
Unfold lin_dep.
Split.
Unfold not.
Intros.
Apply H.
Exists n.
Exists a.
Exists v.
Split.
Assumption.
Split.
Assumption.
Assumption.
Unfold not.
Intros.
Inversion_clear H0.
Inversion_clear H1.
Inversion_clear H0.
Apply (H x x0 x1).
Inversion_clear H1.
Assumption.
Inversion_clear H1.
Inversion_clear H2.
Assumption.
Inversion_clear H1.
Inversion_clear H2.
Assumption.
Qed.
End defs.

Section unexpected_true_results.

Lemma zero_imp_lin_dep : (F:field;V:(vectorspace F);X:(part_set V))
  (in_part (zero V) X)->(lin_dep X).
Intros.
Unfold lin_dep.
Exists (0).
Exists (const_seq (1) (ring_unit F)).
Red in H.
Exists (const_seq (1) (Build_subtype H)::X).
Split.
Red.
Intros i j.
Generalize fin_S_O_unique.
Intros.
Absurd i='j;Auto.
Split.
Cut ~(Equal one (zero F)).
Unfold not.
Intros.
Apply H0.
Simpl in H1.
Red in H1.
Simpl in H1.
Apply H1.
Exact (Build_finiteT (lt_O_Sn O)).
Exact (field_unit_non_zero F).
Simpl.
(Apply Trans with (zero V)+'(zero V);Auto with algebra).
Qed.

Lemma empty_lin_indep : (F:field; V:(vectorspace F))(lin_indep (empty V)).
Intros.
Unfold empty.
Red.
Red.
Unfold lin_dep.
Intro.
Inversion_clear H.
Inversion_clear H0.
Inversion_clear H.
LetTac h:=(head x1).
Case h.
Simpl.
Auto.
Qed.
End unexpected_true_results.

Section more.
Variable F:field.
Variable V:(vectorspace F).

(** - %\intoc{\bf Theorem 1.6}% *)
Lemma lin_dep_include : (S1,S2:(part_set V))
  (included S1 S2)->(lin_dep S1)->(lin_dep S2).
Unfold lin_dep.
Intros.
Inversion_clear H0.
Exists x.
Inversion_clear H1.
Exists x0.
Inversion_clear H0.
Exists (Map_include_map ? H x1).
Split.
Red.
Inversion_clear H1.
Inversion_clear H2.
Red in H0.
Unfold not.
Intros.
Unfold not in H0.
(Apply (H0 i j);Auto with algebra).
Split.
Inversion_clear H1.
Inversion_clear H2.
Assumption.
Inversion_clear H1.
Inversion_clear H2.
(Apply Trans with (sum (mult_by_scalars x0 (Map_embed x1)));Auto with algebra).
Qed.

(** - %\intoc{Corollary to theorem 1.6}% *)
Lemma lin_indep_include : (S1,S2:(part_set V))
  (included S1 S2)->(lin_indep S2)->(lin_indep S1).
Intros S1 S2 H.
Unfold lin_indep.
Unfold not.
Intros.
Apply H0.
Apply (lin_dep_include H).
Assumption.
Qed.

(** For this we need $\neg\neg P\to P$: *)
Lemma lin_indep_prop : (n:Nat;a:(seq n F);v:(seq n V))
  (distinct v)
    ->(lin_indep (seq_set v))
      ->(sum (mult_by_scalars a v))='(zero V)
        ->a='(const_seq n (zero F)).
Intro n;Case n.
Intros.
Simpl.
Red.
Intro.
Inversion x.
Inversion in_range_prf.
Intros.
Elim (lin_dep_defs_eqv (seq_set v)).
Intros.
Generalize (H2 H0);Clear H3 H2 H0.
Intro.
Unfold lin_indep' in H0.
Generalize (H0 ? a (seq_set_seq v)).
Intro;Clear H0.
Cut (distinct (seq_set_seq v));Auto.
Intro.
Generalize (H2 H0).
Clear H2 H0.
Intro.
Apply NNPP.
Unfold not;Intros.
Unfold not in H0.
Apply H0.
Auto.
(Apply Trans with (sum (mult_by_scalars a v));Auto with algebra).
Qed.

Lemma lin_indep_doesn't_contain_zero : 
  (X:(part_set V)) (lin_indep X)->~(in_part (zero V) X).
Intros;Red;Red in H;Intro.
Red in H;(Apply H;Auto with algebra).
(Apply zero_imp_lin_dep;Auto with algebra).
Qed.

Lemma inject_subsets_lin_dep : (W:(subspace V);X:(part_set W))
  (lin_dep X)<->(lin_dep (inject_subsets X)).
Split;Intros.
Red;Red in H.
Inversion_clear H;Inversion_clear H0;Inversion_clear H;Inversion_clear H0;Inversion_clear H1.
Exists x;Exists x0.
Exists (comp_map_map (Build_Map (inject_subsetsify_comp 3!X))::(MAP??) x1).
Split;Try Split.
2:Auto.
Red;Red in H.
Intros.
Simpl.
Intro;Red in H3.
Red in H;(Apply (H ?? H1);Auto with algebra).
Clear H0 H.
(Apply Trans with (subtype_elt (zero W));Auto with algebra).
(Apply Trans with (subtype_elt (sum (mult_by_scalars x0 (Map_embed x1))));Auto with algebra).
(Apply Trans with (sum (Map_embed (mult_by_scalars x0 (Map_embed x1))));Auto with algebra).
Generalize (mult_by_scalars x0 (Map_embed x1)).
Generalize (S x).
Intros.
NewInduction n.
Simpl.
Auto with algebra.
(Apply Trans with (head (Map_embed c))+'(sum (Seqtl (Map_embed c)));Auto with algebra).
Apply Trans with (subtype_elt (head c)+'(sum (Seqtl c))).
(Apply Trans with (subtype_elt (head c))+'(subtype_elt (sum (Seqtl c)));Auto with algebra).
(Apply Trans with ((head (Map_embed c)) +' (sum (Map_embed (Seqtl c))));Auto with algebra).
(Apply SGROUP_comp;Auto with algebra).
(Apply sum_comp;Auto with algebra).
(Apply Sym;Auto with algebra).
Generalize Map_embed_Seqtl.
Intro p.
Apply (p ??? (c::(seq??))).
Apply subtype_elt_comp.
(Apply Sym;Auto with algebra).

Red;Red in H.
Inversion_clear H;Inversion_clear H0;Inversion_clear H;Inversion_clear H0;Inversion_clear H1.
Exists x;Exists x0.
Exists (comp_map_map (Build_Map (uninject_subsetsify_comp 3!X))::(MAP??) x1).
Split;Try Split.
2:Auto.
Red;Red in H.
Intros.
Simpl.
Generalize (H??H1).
Case (x1 i);Case (x1 j).
Simpl.
Unfold subtype_image_equal.
Simpl.
Auto with algebra.
Clear H0 H.
Simpl.
Red.
(Apply Trans with (zero V);Auto with algebra).
Apply Trans with (subtype_elt (sum (mult_by_scalars x0 (Map_embed (comp_map_map (Build_Map (uninject_subsetsify_comp 1!V 2!W 3!X))::(Map??) x1))::(Map?W)))).

Simpl.
(Apply SGROUP_comp;Auto with algebra).
(Apply Trans with(sum (mult_by_scalars x0 (Map_embed x1)));Auto with algebra). 
Apply Trans with (sum (Map_embed (mult_by_scalars x0 (Map_embed (comp_map_map (Build_Map (uninject_subsetsify_comp 1!V 2!W 3!X))::(Map??) x1))::(Map?W)))).
Generalize 
(mult_by_scalars x0
         (Map_embed
           (comp_map_map
             (Build_Map (uninject_subsetsify_comp 1!V 2!W 3!X)) x1))::(Map?W)).
Generalize (S x).
Intros.
(Apply Sym;Auto with algebra).
NewInduction n.
Simpl.
Auto with algebra.
(Apply Trans with (head (Map_embed c))+'(sum (Seqtl (Map_embed c)));Auto with algebra).
Apply Trans with (subtype_elt (head c)+'(sum (Seqtl c))).
(Apply Trans with (subtype_elt (head c))+'(subtype_elt (sum (Seqtl c)));Auto with algebra).
(Apply Trans with ((head (Map_embed c)) +' (sum (Map_embed (Seqtl c))));Auto with algebra).
(Apply SGROUP_comp;Auto with algebra).
(Apply sum_comp;Auto with algebra).
(Apply Sym;Auto with algebra).
Generalize Map_embed_Seqtl.
Intro p.
Apply (p ??? (c::(seq??))).
Apply subtype_elt_comp.
(Apply Sym;Auto with algebra).
Apply sum_comp.
Simpl;Red;Simpl.
Intro.
(Apply MODULE_comp;Auto with algebra).
Unfold  uninject_subsetsify.
Case (x1 x2).
Simpl.
Auto with algebra.
Qed.
End more.

(** - The following definition is a reformulation of the book's definition on page 50 *)
(** %\tocdef{max\_lin\_indep}% *)
Definition max_lin_indep := [F:field;V:(vectorspace F);X,Y:(part_set V)]
  (included X Y)/\(lin_indep X)/\(y:V) (in_part y Y)
    -> ~(in_part y X) -> (lin_dep (union X (single y))).

End MAIN.
