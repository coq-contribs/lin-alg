(** * Linear_Algebra_by_Friedberg_Insel_Spence.v *)
Set Implicit Arguments.

(** - This file summarizes how I formalised Friedberg, Insel and Spence's book 
 LINEAR ALGEBRA, 2nd ed., ISBN 0-13-536855-3, (c) Prentice-Hall, Inc. *)

(** - Note for coqdoc documentation readers: please read this file by itself as well: 
 coqdoc leaves out a great deal of useful information. The file itself will tell you
 which Coq lemmas  correspond to which theorems, corollaries, etc.; most proofs of
 this file  consist of a single line saying "Exact lemmaname". Also the definitions
 of many defined constants are shown in the comments. *)

Section SECTION_1_2.




(* The definition of "vectorspace" I have not done in the way of section 1.2 on p.6. *)
(* In fact, since I use Loic Pottier's Algebra contribution, I defined that a *)
(* vectorspace be a module (which is a defined notion in that contribution), *)
(* the scalars of which are a field. *)

Require Export vecspaces_verybasic.

(* Coq < Print vectorspace.
vectorspace = [F:field](MODULE F)
     : field->Type *)

(* We will prove that from this definition one can prove the 8 vectorspace *)
(* axioms as listed in the definition on p6. *)


(* Equality inside Setoids is a very basic notion, and it is very convenient *)
(* to introduce the notation =' for it. *)

(* Since (almost) all semigroups we will be working with are additive (ie. having *)
(* their multiplications commutative), we introduced the notation +' for them. *)

(* Vectorspaces are semigroups as well, and hence we can use +' to add vectors. *)
(* The vectorspace axioms now take the following form : *)

Variable F:field.
Variable V:(vectorspace F).

Definition VS1 : (x,y:V)(x +' y) =' (y +' x).
  Exact (ABELIAN_SGROUP_com 1!V).
  Qed.

Definition VS2 : (x,y,z:V)((x +' y) +' z) =' (x +' (y +' z)).
  Exact (SGROUP_assoc 1!V).
  Qed.

(* Any vectorspace V is an (abelian) monoid. Monoids always have unit elements *)
(* and since (almost) all monoids we are working with are additive, we use the *)
(* (inherited) notation +' for the multiplication (ie. addition) and (zero M) *)
(* for (monoid_unit M), ie. the monoid unit. The monoid unit of a vectorspace *)
(* then is the zero vector, so we get (zero V) as a notation for that. *)
(* Nonetheless, for expository purposes we'll define explicitly: *)

Definition VS3 : (EXT zerovector:V | (x:V) x +' zerovector =' x).
  Exists (zero V);Auto with algebra.
  Qed.

(* Now any vectorspace V is a group, and in groups, inverses are always defined. *)
(* In fact, Loic Pottier has added the group operation group_inverse for them. *)
(* We will use the shorthand (min v) for the inverse of v; again because our *)
(* groups are (almost) always commutative. Nonetheless: *)

Definition VS4 : (x:V)(EXT y:V | x +' y =' (zero V)).
  Intro;Exists (min x);Auto with algebra.
  Qed.

(* For rings, we introduced the shorthand "one" for Loic Pottier's (ring_unit ?) *)
(* by making a Syntactic Definition. The ? will be automaticly inferred. *)

(* In everyday maths one has the same notation for multiplication of two *)
(* scalars (giving another scalar) and multiplication of a vector by a scalar *)
(* (giving another vector). In Coq we cannot do so. Therefore we use rX for *)
(* the former and mX for the latter *)

Definition VS5 : (x:V) one mX x =' x.
  Intro;Exact (MODULE_unit_l x).
  Qed.

(* Note the distinction between mX and rX: *)

Definition VS6 : (a,b:F;x:V) (a rX b) mX x =' a mX (b mX x).
  Intros;Exact (MODULE_assoc a b x).
  Qed.

Definition VS7 : (a:F;x,y:V) a mX (x +' y) =' (a mX x) +' (a mX y).
  Intros;Exact (MODULE_dist_l a x y).
  Qed.

(* Of course, fields are also semigroups, using the +' notation: *)

Definition VS8 : (a,b:F;x:V) (a +' b) mX x =' (a mX x) +' (b mX x).
  Intros;Exact (MODULE_dist_r a b x).
  Qed.

Definition Proposition_1_1 : (x,y,z:V) x+'z='y+'z -> x='y.
  Exact (vector_cancellation 2!V).
  Qed.

Definition Proposition_1_2a : (x:V) (zero F)mX x =' (zero V).
  Exact (Zero_times_a_vector_gives_zero 2!V).
  Qed.

Definition Proposition_1_2b1 : (a:F;x:V)(min a) mX x =' (min (a mX x)).
  Exact (Mince_minus1 2!V).
  Qed.

Definition Proposition_1_2b2 : (a:F;x:V)(min (a mX x)) =' a mX (min x).
  Exact (Mince_minus2 2!V).
  Qed.

Definition Proposition_1_2b3 : (a:F;x:V)(min a) mX x ='a mX (min x).
  Exact (Mince_minus3 2!V).
  Qed.

Definition Proposition_1_2c : (a:F) a mX (zero V) =' (zero V).
  Exact (a_scalar_times_zero_gives_zero V).
  Qed.

End SECTION_1_2.






Section SECTION_1_3.

Require Export subspaces.

(* A subspace is defined as just a submodule of a vectorspace *)
(* We have a coercion from subspaces to part_sets *)

(* Note the slightly funny phrasing necessitated by Coq's type system: *)

Definition Theorem_1_3 : (F:field; V:(vectorspace F); Ws:(part_set V))
   (in_part (zero V) Ws)
   /\((x,y:V)(in_part x Ws)->(in_part y Ws)->(in_part (x +' y) Ws))
     /\((c:F; x:V)(in_part x Ws)->(in_part (c mX x) Ws))
   <->(EXT W:(subspace V) | W =' Ws in (part_set V)).
  Exact subspace_alt_characterization.
Qed.

(* Hence the following definition: 
Coq < Print is_subspace.
is_subspace = 
[W:(part_set V)]
 (in_part (zero V) W)
 /\((x,y:V)(in_part x W)->(in_part y W)->(in_part (x +' y) W))
   /\((c:F; x:V)(in_part x W)->(in_part (c mX x) W))
     : (part_set V)->Prop*)

Definition Theorem_1_4 : (F:field; V:(vectorspace F); f:(part_set (Set_of_subspaces V)))
  (is_subspace (intersection (inject_subsets f))).
  Exact Set_of_subspaces_closed_under_intersection.
  Qed.

Require Export direct_sum.

(*Coq < Print sum_set.
sum_set = 
[F:field; V:(vectorspace F); S1,S2:(part_set V)]
 (Build_Predicate
   [x,y:V;
    H:(EXT s1|(EXT s2|x='(subtype_elt s1)+'(subtype_elt s2) in V));
    H0:(y='x in V)]
    [H1:=<(EXT s1|(EXT s2|y='(subtype_elt s1)+'(subtype_elt s2) in V))>
           Cases H of
             (exT_intro x0 H1) => 
              [H:=<(EXT s1|(EXT s2|y
                                     ='(subtype_elt s1)
                                         +'(subtype_elt s2) in V))>
                    Cases H1 of
                      (exT_intro x1 H) => 
                       (exT_intro S1
                         [s1:S1]
                          (EXT s2|y='(subtype_elt s1)+'(subtype_elt s2)
                                    in V) x0
                         (exT_intro S2
                           [s2:S2]
                            y='(subtype_elt x0)+'(subtype_elt s2) in V
                           x1
                           (Trans 1!V 2!y 3!x
                             4!(subtype_elt x0)+'(subtype_elt x1) H0 H)))
                    end]H
           end]H1)
     : (F:field; V:(vectorspace F))
        (part_set V)->(part_set V)->(part_set V)

Coq < Print form_direct_sum.
form_direct_sum = 
[F:field; V:(vectorspace F); W1,W2:(subspace V)]
 (inter W1 W2)='(single 1!V (zero V)) in (part_set V)
   /\(sum_set 2!V W1 W2)='(full V) in (part_set V)
     : (F:field; V:(vectorspace F))(subspace V)->(subspace V)->Prop*)

End SECTION_1_3.






Section SECTION_1_4.

Require Export lin_combinations.

(* The property of x being a linear combiNation of some subset S of V is *)
(* defined straightforwardly if one knows that mult_by_scalars multiplies *)
(* a sequence of scalars pointwise with a sequence of vectors, so that *)
(* below (sum (mult_by_scalars a v)) means a1v1+a2v2+...+anvn - and the *)
(* Map_embed has to do with the fact that we want to view v as a sequence *)
(* of vectors from V instead of S *)


(* Coq < Print is_lin_comb_prop.
is_lin_comb_prop = 
[F:field; V:(vectorspace F); x:V; S:(part_set V)]
 (EXT n:Nat |
      (EXT a:(seq n F) |
           (EXT v:(seq n S) |
                x =' (sum (mult_by_scalars a (Map_embed v))))))
     : (F:field; V:(vectorspace F))V->(part_set V)->Prop
Positions [1; 2] are implicit *)

Require Export spans.

(* Before proving theorem 1.5, we define the notion of span. In fact, in the *)
(* book it says "the subspace W described in theorem 1.5 is called the span of S" *)
(* as a definition. Below, is_lin_comb is a "Predicate", coercing to is_lin_comb_prop *)

(* Coq < Print span_set.
span_set = 
[F:field; V:(vectorspace F); S:(part_set V)](is_lin_comb S)
     : (F:field; V:(vectorspace F))(part_set V)->(part_set V)
Positions [1; 2] are implicit *)

(* This is the underlying set, upon which we build a (sub)module structure *)
(* which is, then, the span as a subspace of V: *)

(* Coq < Check span.
span
     : (F:field; V:(vectorspace F))(part_set V)->(subspace V) *)

(* The actual definition of span is rather large: 70 lines *)
(* But, of course, feel free to tell Coq to "Print span" *)

Definition Theorem_1_5a : (F:field; V:(vectorspace F);S:(part_set V))
  (is_subspace (span S)).
  Exact span_is_subspace.
  Qed.

(* The "Moreover..." bit now reads: "Moreover, span(S) is the smallest subspace of V *)
(* containing S in the sense that span(S) is a subset of any subspace of V that *)
(* contains S" - or rather: *)

Definition Theorem_1_5b : (F:field;V:(vectorspace F);W:(subspace V);S:(part_set V))
  (included S W)->(included (span S) W).
  Exact span_smallest_subspace_containing_subset.
  Qed.

(* "generating" is defined as: *)

(* Coq < Print generates.
generates = 
[F:field; V:(vectorspace F); S:(part_set V)](span S) =' (full V)
     : (F:field; V:(vectorspace F))(part_set V)->Prop
Positions [1; 2] are implicit *)

End SECTION_1_4.






Section SECTION_1_5.

Require Export lin_dependence.

(* "distinct" says the entries of a sequence are all different; "const_seq" *)
(* makes the constant sequences of given length filled with the given element *)

(* Coq < Print lin_dep.
lin_dep = 
[F:field; V:(vectorspace F); X:(part_set V)]
 (EXT n:Nat |
      (EXT a:(seq (S n) F) |
           (EXT v:(seq (S n) X) |
                (distinct v)
                /\~a =' (const_seq (S n) (zero F))
                  /\(sum (mult_by_scalars a (Map_embed v))) =' (zero V))))
     : (F:field; V:(vectorspace F))(part_set V)->Prop
Positions [1; 2] are implicit *)

(* And of course lin_indep is ~lin_dep *)

(* I've also written this out is a new definition: *)
(* Coq < Print lin_indep'.
lin_indep' = 
[F:field; V:(vectorspace F); X:(part_set V)]
 (n:Nat; a:(seq (S n) F); v:(seq (S n) X))
  (distinct v)
  ->~a =' (const_seq (S n) (zero F))
  ->~(sum (mult_by_scalars a (Map_embed v))) =' (zero V)
     : (F:field; V:(vectorspace F))(part_set V)->Prop
Positions [1; 2] are implicit *)

Definition Theorem_1_6 : (F:field; V:(vectorspace F); S1,S2:(part_set V))
        (included S1 S2)->(lin_dep S1)->(lin_dep S2).
  Exact lin_dep_include.
  Qed.

Definition Corollary_to_1_6 : (F:field; V:(vectorspace F); S1,S2:(part_set V))
        (included S1 S2)->(lin_indep S2)->(lin_indep S1).
  Exact lin_indep_include.
  Qed.

End SECTION_1_5.






Section SECTION_1_6.

Require Export bases.

(* Coq < Print is_basis.
is_basis = 
[F:field; V:(vectorspace F); X:(part_set V)]
 (generates X)/\(lin_indep X)
     : (F:field; V:(vectorspace F))(part_set V)->Prop
Positions [1; 2] are implicit *)

(* Coq < Print basis.
Inductive basis [F : field; V : (vectorspace F)]  : Type :=
      Build_basis : (basis_carrier:(Predicate V))
                     (is_basis basis_carrier)->(basis V)
For basis: Position [1] is implicit
For Build_basis: Positions [1; 2; 3] are implicit *)

(* Using a record structure for the definition of basis, we can use basis_carrier as *)
(* a coercion from X:(basis V) to X:(part_set V) (which Predicate V also coerces to) *)

Variable F:field.
Variable V:(vectorspace F).
Variable x:V.
Variable n:Nat.

Variable b:(seq n V).
Variable Hb:(distinct b).
Variable Hb2:(is_basis (seq_set b)).

Definition Theorem_1_7 : (a,a':(seq n F))
  (sum (mult_by_scalars a b))='x -> (sum (mult_by_scalars a' b))='x ->
    a='a'.
  Exact (basis_expansion_uniqueness Hb Hb2).
  Qed.

Require Export lin_dep_facts.

Definition Theorem_1_8 :  (s:(part_set V)) (lin_indep s) -> ~(in_part x s)->
  ((lin_dep (union s (single x)))<->(in_part x (span s))   ). 
  Intros.
  Exact (lin_dep_vs_span_lemma H H0).
  Qed.

Require Export bases_finite_dim.

Definition Theorem_1_9 : (W0:(part_set V))
  (is_finite_subset W0) -> (generates W0 (full V)) ->
    (EXT W:(part_set W0) | (is_basis (inject_subsets W))).
  Exact (every_finite_generating_set_has_a_subset_that_is_a_basis 2!V).
  Qed.

Require Export replacement_theorem.

Definition Theorem_1_10 :   (beta:(basis V);n:Nat)
  (has_n_elements n beta) ->
  (Sset:(part_set V)) (lin_indep Sset) ->
  (m:Nat) (le m n) -> (has_n_elements m Sset) ->

  (EXT S1:(part_set beta) | (has_n_elements (minus n m) S1) /\ 
                            (generates (union Sset (inject_subsets S1)) (full V))).
  Exact (replacement_theorem 2!V).
  Qed.

Definition Corollary_1_to_1_10 : (n:Nat;beta:(basis V))
  (has_n_elements n beta)->
  (Sset:(part_set V)) (lin_indep Sset) -> (has_n_elements n Sset) ->
    (is_basis Sset).
  Exact (finite_bases_always_equally_big 2!V).
  Qed.

Definition Corollary_2_to_1_10 : (n:Nat;beta:(basis V))
  (has_n_elements n beta)->
  (Sset:(part_set V)) (has_at_least_n_elements (S n) Sset) ->
    (lin_dep Sset).
  Exact (finite_basis_bounds_lin_indep_set_size 2!V).
  Qed.

Definition Corollary_2_to_1_10_conversely : (n:Nat;beta:(basis V))
  (has_n_elements n beta)->
  (Sset:(part_set V)) (lin_indep Sset) ->
    (has_at_most_n_elements n Sset).
  Exact (finite_basis_bounds_lin_indep_set_size' 2!V).
  Qed.

Definition Corollary_3_to_1_10 : (n:Nat;beta:(basis V))
  (has_n_elements n beta) -> (Sset:(basis V)) (has_n_elements n Sset).
  Exact (all_finite_bases_equally_big 2!V).
  Qed.

Definition Corollary_4_to_1_10 :  (n:Nat)
  (has_dim n V)->
  (S:(part_set V)) (generates S (full V)) -> (has_at_most_n_elements n S) ->
    (is_basis S)/\(has_n_elements n S).
  Exact (dimension_bounds_generating_set_size 2!V).
  Qed.

Definition Corollary_5_to_1_10 :  (is_finite_dimensional V) ->
  (beta:(basis V);Sset:(part_set V)) (lin_indep Sset) ->
    (EXT S1:(part_set V) | (included S1 beta)/\(is_basis (union Sset S1))).
  Exact (every_lin_indep_set_can_be_extended_to_a_basis 2!V).
  Qed.

Require Export subspace_dim.
Definition Theorem_1_11 : (V:(findimvecsp F);W:(subspace V))
  (sigT nat [m] (le m (the_dim V))/\ (has_dim m W)).
  Exact (subspace_preserves_findimvecsp 1!F).
  Qed.
End SECTION_1_6.




Section SECTION_1_7.
Require Export maxlinindepsubsets.
(* Coq < Print maximal.
maximal = 
[X:Setoid; F:(part_set (part_set X)); A:(part_set X)]
 (in_part A F)
 /\~(EXT B:(part_set X) | (in_part B F)/\(included A B)/\~A =' B)
     : (X:Setoid)(part_set (part_set X))->(part_set X)->Prop
Position [1] is implicit *)

(* Coq < Print is_chain.
is_chain = 
[X:Setoid; F:(part_set (part_set X))]
 (A,B:(part_set X))
  (in_part A F)->(in_part B F)->(included A B)\/(included B A)
     : (X:Setoid)(part_set (part_set X))->Prop
Position [1] is implicit *)

(* The Maximal Principle is an axiom. It is equivalent to the Axiom of Choice *)

(* Coq < Print MAXIMAL_PRINCIPLE.
*** [ MAXIMAL_PRINCIPLE : 
(X:Setoid; F:(part_set (part_set X)))
 ((C:(part_set (part_set X)))
   (is_chain C)
   ->(included C F)
   ->(EXT A:(part_set X) |
          (in_part A F)
          /\((B:(part_set X))(in_part B C)->(included B A))))
 ->(EXT A:(part_set X) | (maximal F A)) ]
Positions [1; 2] are implicit *)

(* I formalized maximal linear independence slightly different, because in fact *)
(* I used it earlier as an auxiliary notion - but this definition should be *)
(* nice enough too! (max_lin_indep X Y) says that X is maximally linearly *)
(* independent with respect to Y: X is contained in Y, X is linearly independent *)
(* and adding any vector from Y\X to X yields it linearly dependent: *)

(* Coq < Print max_lin_indep.
max_lin_indep = 
[F:field; V:(vectorspace F); X,Y:(part_set V)]
 (included X Y)
 /\(lin_indep X)
   /\((y:V)
       (in_part y Y)->~(in_part y X)->(lin_dep (union X (single y))))
     : (F:field; V:(vectorspace F))(part_set V)->(part_set V)->Prop
Positions [1; 2] are implicit *)

Require Export maxlinindepsubsets.
Definition Theorem_1_12 : (F:field;V:(vectorspace F);W:(part_set V))
  (generates W (full V)) -> (beta:(part_set V)) (max_lin_indep beta W) ->
    (is_basis beta).
  Exact max_lin_indep_subsets_of_generating_sets_are_bases.
  Qed.

Definition Corollary_to_1_12 : (F:field;V:(vectorspace F);beta:(part_set V))
  (is_basis beta)<->(max_lin_indep beta (full V)).
  Exact basis_iff_max_lin_indep.
  Qed.

Definition Theorem_1_13 : (F:field;V:(vectorspace F);W:(part_set V))
  (lin_indep W) ->
    (EXT W':(part_set V) | (max_lin_indep W' (full V))/\(included W W')).
  Exact max_lin_indep_subset_generated.
  Qed.

Definition Corollary_to_1_13 : (F:field;V:(vectorspace F))
  (EXT beta:(part_set V) | (is_basis beta)).
  Exact every_vecsp_has_a_basis.
  Qed.

End SECTION_1_7.