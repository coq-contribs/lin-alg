(** * bases_finite_dim.v *)
Set Implicit Arguments.
Require Export bases_from_generating_sets.
Require Export replacement_corollaries.

(** %\tocdef{is\_{\em[in]}finite\_dimensional}% *)
Definition is_finite_dimensional [F:field;V:(vectorspace F)] :=
  (EXT beta:(basis V) | (EXT n:Nat | (has_n_elements n beta))).

Definition is_infinite_dimensional [F:field;V:(vectorspace F)] :=
  (beta:(basis V);n:Nat) ~(has_n_elements n beta).

(** %\tocdef{has\_dim}% *)
Definition has_dim [F:field;n:Nat;V:(vectorspace F)] :=
  (EXT beta:(basis V) | (has_n_elements n beta)).

Lemma finite_dim_vecsp_has_dim : (F:field;V:(vectorspace F))
  (is_finite_dimensional V) -> (EXT n:Nat | (has_dim n V)).
Intros.
Inversion_clear H.
Rename x into beta.
Inversion_clear H0.
Inversion_clear H.
Rename x into n.
Exists n.
Red.
Exists beta;Auto.
Red.
Exists x0;Auto.
Qed.

Lemma has_dim_inj : (F:field;V:(vectorspace F);n,m:Nat)
  (has_dim n V) -> (has_dim m V) -> n='m.
Intros.
Inversion_clear H.
Inversion_clear H0.
Assert (has_n_elements m x).
(Apply all_finite_bases_equally_big with x0;Auto with algebra).
Generalize has_n_elements_inj;Intro p.
(Apply (p???H1??H0);Auto with algebra).
Qed.

Lemma has_dim_easy : (F:field;V:(vectorspace F);b:(part_set V))
  (is_basis b) -> (n:nat)(has_n_elements n b) -> (has_dim n V).
Intros.
Red.
Exists (Build_basis H).
Simpl.
Auto.
Qed.

Section Part_3.
(** - %\intoc{Corollary 4 to 1.10}% *)
Lemma dimension_bounds_generating_set_size : (F:field;V:(vectorspace F);n:Nat)
 (has_dim n V) -> (S:(part_set V)) (generates S (full V)) -> (has_at_most_n_elements n S) ->
   (is_basis S)/\(has_n_elements n S).
Intros.
Generalize (every_finite_generating_set_has_a_subset_that_is_a_basis 3!S).
Intro p.
Assert (is_finite_subset S).
Red.
Red in H1.
Inversion_clear H1.
Inversion_clear H2.
Exists x.
Generalize (n_element_subset_sequence H3).
Intro.
Inversion_clear H2.
Inversion_clear H4.
Exists x0;Auto.
Generalize (p H2 H0);Clear p;Intro p.
Inversion_clear p.
Rename x into S1.
Red in H.
Inversion_clear H.
Rename x into beta.
Generalize (all_finite_bases_equally_big H4 (Build_basis H3)).
Intro.
Assert (has_n_elements n S1).
(Apply inject_subsets_respects_has_n_elements;Auto with algebra).
Assert (has_at_least_n_elements n S).
(Apply subset_bounds_set_size_from_below with S1;Auto with algebra).
Assert (has_n_elements n S).
(Apply has_n_elements_by_at_least_at_most;Auto with algebra).
Split;Auto.
(Apply is_basis_comp with (inject_subsets S1);Auto with algebra).
Assert S1='(full S).
(Apply subset_also_has_n_elements_then_it_is_full with n;Auto with algebra).
(Apply Trans with (inject_subsets (full S));Auto with algebra).
Qed.

(** - %\intoc{Corollary 5 to 1.10}%: *)
Lemma every_lin_indep_set_can_be_extended_to_a_basis : (F:field;V:(vectorspace F))
  (is_finite_dimensional V) -> (beta:(basis V);Sset:(part_set V)) (lin_indep Sset) ->
    (EXT S1:(part_set V) | (included S1 beta)/\(is_basis (union Sset S1))).
Intros.
Generalize (finite_dim_vecsp_has_dim H);Intro p.
Inversion_clear p.
Rename x into n.
Generalize H1;Intro HH2.
Red in H1.
Inversion_clear H1.
Rename x into beta'.
Assert (has_n_elements n beta).
(Apply all_finite_bases_equally_big with beta';Auto with algebra).
Clear H2 beta'.
Assert (EXT m:Nat | (has_n_elements m Sset)/\(le m n)).
Generalize (finite_basis_bounds_lin_indep_set_size' H1 H0);Intros.
Red in H2.
Inversion_clear H2.
Rename x into m.
Exists m;Intuition.

Inversion_clear H2.
Rename x into m.
Inversion_clear H3.
Generalize (replacement_theorem H1 H0 H4 H2);Intro.
Inversion_clear H3.
Rename x into S1'.
LetTac S1:=(inject_subsets S1').
Inversion_clear H5.

Assert (has_at_most_n_elements n (union Sset S1)).
(Apply has_at_most_n_elements_comp with (plus m (minus n m)) (union Sset S1);Auto with algebra).
2:Auto with arith.
(Apply union_has_at_most_n_plus_m_elements;Auto with algebra).
Unfold S1.
(Apply inject_subsets_preserves_has_n_elements;Auto with algebra).
Simpl;Auto with arith.

Exists S1.
Generalize (dimension_bounds_generating_set_size HH2 H6 H5).
Split;Intuition.
Unfold S1.
Apply inject_subsets_of_part_set_included.
Qed.

Lemma has_dim_zero_then_trivial : (F:field;V:(vectorspace F))
  (has_dim O V) -> (full V)='(single(zero V)).
Intros.
Red in H.
Inversion_clear H.
Rename x into beta.
Generalize (is_basis_prf beta).
Intro.
Inversion_clear H.
Red in H1.
(Apply Trans with ((span beta)::(part_set?));Auto with algebra).
(Apply Trans with ((span_ind beta)::(part_set?));Auto with algebra).
Apply Trans with ((span_ind (empty V))::(part_set?)).
(Apply span_ind_comp;Auto with algebra).
Simpl.
Red.
Split;Simpl;Intro.
Inversion_clear H.
Generalize Dependent x.
NewInduction x0;Intros.
Simpl in H3.
Auto.
NewDestruct c.
Simpl in subtype_prf.
Contradiction.
Simpl in H3.
(Apply Trans with ((span_ind_injection x1) +' (span_ind_injection x2));Auto with algebra).
(Apply Trans with ((span_ind_injection x1) +' (zero V));Auto with algebra).
(Apply Trans with (span_ind_injection (Multvector c x0));Auto with algebra).
Simpl.
(Apply Trans with (c mX (zero V));Auto with algebra).
Exists (Zerovector (empty V)).
Simpl.
Auto.
Qed.

End Part_3.

(** %\tocdef{findimvecsp}% *)
Record findimvecsp [F:field] :Type :=
{ the_dim : nat
; the_vectorspace :> (module F)
      (* Strangely, I cannot coerce to (vectorspace F) since other coercions *)
      (* stop being inferenced: e.g. W:(part_set V) will no longer be allowed... *)
; dim_prf : (has_dim the_dim the_vectorspace) }.