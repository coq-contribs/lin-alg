(** %\subsection*{ support :  cast\_between\_subsets.v }%*)
Set Implicit Arguments.
Require Export Map_embed.
Require Export algebra_omissions.

(** - Various casting functions between equal but non-convertible types *)

(** - This one maps elements of a subset to the same subset under a different name
 %\label{mapbetweenequalsubsets}% *)
Definition map_between_equal_subsets: (A:Setoid;X,Y:(part_set A))X='Y->X->Y.
Intros A X Y H x.
Inversion_clear x.
Apply (!Build_subtype A Y subtype_elt).
Simpl in H.
Red in H.
Generalize (H subtype_elt).
Intro H'.
Inversion_clear H'.
(Apply H0;Auto with algebra).
Defined.

Lemma subtype_elt_eats_map_between_equal_subsets :
  (A:Setoid;X,Y:(part_set A);H:X='Y;x:X)
    (subtype_elt (map_between_equal_subsets H x)) =' (subtype_elt x).
Intros.
Elim x.
Simpl.
Auto with algebra.
Qed.

Hints Resolve subtype_elt_eats_map_between_equal_subsets : algebra.

Lemma map_between_equal_subsets_inj : (A:Setoid;X,Y:(part_set A);H,H':X='Y;x,x':X)
  (map_between_equal_subsets H x) =' (map_between_equal_subsets H' x')
     -> x='x'.
Simpl.
Unfold subtype_image_equal;Simpl.
Intros.
Apply Trans with (subtype_elt (map_between_equal_subsets H x));Auto with algebra.
Apply Trans with (subtype_elt (map_between_equal_subsets H' x'));Auto with algebra.
Qed.

(** - This one turns $f:A\to X$ into $A\to Y$ whenever $X='Y$ *)

(** %\label{Maptoequalsubsets}% *)
Definition Map_to_equal_subsets : (A,B:Setoid;X,Y:(part_set A))
  X='Y -> (MAP B X)->(MAP B Y).
Intros.
Apply (Build_Map 3![b:B](map_between_equal_subsets H (X0 b))).
Red;Simpl;Red.
Intros.
Unfold map_between_equal_subsets.
Generalize (Map_compatible_prf X0 H0).
Case (X0 x);Case (X0 y).
Simpl.
Auto.
Defined.

Lemma subtype_elt_eats_Map_to_equal_subsets :
  (A,B:Setoid;X,Y:(part_set A);H:X='Y;b:B;M:(Map B X))
    (subtype_elt (Map_to_equal_subsets H M b)) =' (subtype_elt (M b)).
Intros.
Simpl.
Case (M b).
Simpl.
Auto with algebra.
Qed.

Hints Resolve subtype_elt_eats_Map_to_equal_subsets : algebra.

Lemma Map_embed_eats_Map_to_equal_subsets :
  (A,B:Setoid;X,Y:(part_set A);H:X='Y;M:(Map B X))
    (Map_embed (Map_to_equal_subsets H M)) =' (Map_embed M).
Intros.
Simpl.
Red.
Intros b.
Simpl.
Auto with algebra.
Qed.

Hints Resolve Map_embed_eats_Map_to_equal_subsets : algebra.

Lemma Map_to_equal_subsets_inj :
  (A,B:Setoid;X,Y:(part_set A);H,H':X='Y;f,g:(Map B X)) 
    (Map_to_equal_subsets H f) =' (Map_to_equal_subsets H' g)
       -> f='g in (MAP??).
Unfold Map_to_equal_subsets;Simpl;Unfold Map_eq;Simpl;Unfold subtype_image_equal;Simpl.
Intros.
Apply subtype_elt_comp.
Apply map_between_equal_subsets_inj with Y H H';Auto with algebra.
Simpl;Red;Simpl.
Auto.
Qed.

(** - if $\forall b\in B, f(b)\in W\subset A$ for $f:B\to A$ then $f$ can be seen as
 $f:B\to W$. This is done by cast_map_to_subset. *)

Local cast_to_subset_fun :(A,B:Setoid;v:(MAP B A);W:(part_set A))
  ((i:B)(in_part (v i) W))->(B-> W::Type).
Intros A B v.
Elim v.
Intros vseq vprf;Intros.
Generalize X;Clear X.
Simpl.
Exact [i:B](Build_subtype (H i)).
Defined.

Lemma cast_doesn't_change :
  (A,B:Setoid;v:(MAP B A);W:(part_set A);H:((i:B)(in_part (v i) W));i:B)
    (subtype_elt ((cast_to_subset_fun H) i)) =' (v i).
Intros A B v.
Elim v.
Simpl.
Auto with algebra.
Qed.

Hints Resolve cast_doesn't_change : algebra.

(** %\label{castmaptosubset}% *)
Definition cast_map_to_subset : (A,B:Setoid;v:(MAP B A);W:(part_set A))
  ((i:B)(in_part (v i) W))->(MAP B W).
Intros.
Cut (fun_compatible (cast_to_subset_fun H)).
Intro.
Exact (Build_Map H0).
Red.
Simpl.
Red.
Intros.
(Apply Trans with (v x);Auto with algebra).
(Apply Trans with (v y);Auto with algebra).
Defined.

Lemma cast_map_to_subset_doesn't_change :
  (A,B:Setoid;v:(MAP B A);W:(part_set A)) (H:(i:B)(in_part (v i) W))
    (i:B) (subtype_elt ((cast_map_to_subset H) i))='(v i).
Intros.
Simpl.
Auto with algebra.
Qed.

Hints Resolve cast_map_to_subset_doesn't_change : algebra.

Lemma Map_embed_cast_map_to_subset_inv :
  (A,B:Setoid;v:(MAP B A);W:(part_set A)) (H:(i:B)(in_part (v i) W))
    (Map_embed (cast_map_to_subset H))='v.
Intros.
Simpl.
Red.
Simpl.
Auto with algebra.
Qed.

Hints Resolve Map_embed_cast_map_to_subset_inv : algebra.

Lemma Map_embed_eats_cast_map_to_subset :
  (A,D:Setoid; B,C:(part_set A); v:(MAP D B); H:((i:D)(in_part ((Map_embed v) i) C)))
    (Map_embed (cast_map_to_subset H))='(Map_embed v).
Intros.
Auto with algebra.
Qed.

Hints Resolve Map_embed_eats_cast_map_to_subset : algebra.

Lemma seq_castable : (A,B:Setoid;v:(MAP B A);W:(part_set A))
  ((i:B)(in_part (v i) W)) -> (EXT w:(MAP B W)| (Map_embed w)='v).
Intros.
Exists (cast_map_to_subset H).
Auto with algebra.
Qed.

Hints Resolve seq_castable : algebra.

Lemma subset_seq_castable :
  (A,D:Setoid; B,C:(part_set A); v:(MAP D B); H:((i:D)(in_part ((Map_embed v) i) C)))
    (EXT w:(MAP D C) | (Map_embed w)='(Map_embed v)).
Intros.
Exists (cast_map_to_subset H).
Auto with algebra.
Qed.

Hints Resolve subset_seq_castable : algebra.

Lemma cast_seq_nice :
  (A,B:Setoid;v:(MAP B A);W:(part_set A);H:(i:B)(in_part (v i) W);P:(Predicate (MAP B A)))
    (Pred_fun P v)->(Pred_fun P (Map_embed (cast_map_to_subset H))).
NewDestruct P.
Intros.
Red in Pred_compatible_prf.
Simpl.
Simpl in H0.
(Apply Pred_compatible_prf with v;Auto with algebra).
Qed.

Hints Resolve cast_seq_nice : algebra.

Lemma cast_subset_seq_nice : (A,D:Setoid; B,C:(part_set A); v:(MAP D B); H:((i:D)(in_part ((Map_embed v) i) C));P:(Predicate (MAP D A)))
  (Pred_fun P (Map_embed v)) ->(Pred_fun P (Map_embed (cast_map_to_subset H))).
Intros.
Auto with algebra.
Qed.

Hints Resolve cast_subset_seq_nice : algebra.

Lemma cast_respects_predicates_per_elt : (A,D:Setoid; B,C:(part_set A); v:(MAP D B);P:(Predicate A); H:((i:D)(in_part ((Map_embed v) i) C))) 
  (i:D)(Pred_fun P ((Map_embed v) i))->(Pred_fun P ((Map_embed (cast_map_to_subset H)) i)).
Intros.
Generalize H0;Clear H0;Elim P.
Intros Pf pc H0.
Simpl.
Simpl in H0.
Auto.
Qed.

Lemma cast_respects_all_elt_predicates : (A,D:Setoid; B,C:(part_set A); v:(MAP D B);P:(Predicate A); H:((i:D)(in_part ((Map_embed v) i) C))) 
  ((i:D)(Pred_fun P ((Map_embed v) i)))->(j:D)(Pred_fun P ((Map_embed (cast_map_to_subset H)) j)).
Intros.
Generalize H0;Clear H0;Elim P.
Intros Pf pc H0.
Simpl.
Simpl in H0.
Auto.
Qed.

Hints Resolve cast_respects_predicates_per_elt cast_respects_all_elt_predicates : algebra.

(** - Similarly, if $B\subset C$ are subsets of $A$, then $f:D\to B$ is also $f:D\to C$. *)

Definition Map_include : (A,D:Setoid;B,C:(part_set A))
  (included B C)->(MAP D B)->(MAP D C).
Intros.
Apply (cast_map_to_subset 3!(Map_embed X)).
Red in H.
Intro.
(Apply H;Auto with algebra).
(Apply Map_embed_prop;Auto with algebra).
Defined.

Definition Map_include_map : (A,D:Setoid;B,C:(part_set A))
  (included B C)->(MAP (MAP D B) (MAP D C)).
Intros.
Simpl.
Apply Build_Map with (Map_include 2!D H).
Red.
Intuition.
Defined.