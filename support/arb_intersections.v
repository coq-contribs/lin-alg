(** %\subsection*{ support :  arb\_intersections.v }%*)
(** - This stuff could be put in the algebra contribution as well. We 
 define indexed intersections $\bigcap_{i\in I} X_i$ whenever all 
 $X_i\subset X$, and arbitrary intersections $\bigcap_{X\in P}X$ for
 $P\subset{\cal P}(A)$.
 - Suppose we have a collection of subsets $A_i$ of a setoid $A$, 
 indexed by some index set $I$. Then we may define the 
 intersection $\bigcap_{i\in I} A_i \subset A$ as 
 $\{a\in A | \forall i\in I.a\in A_i\}$ *)

Set Implicit Arguments.
Require Export Parts2.
Require Export Classical_Pred_Type.
Section MAIN.
Section indexed_int.

Variable A:Setoid.
Variable I:Setoid.
Variable f:(MAP I (part_set A)). (* Picks A_i for i\in I *)
 
(** - so, given an index set $I$ and an indexing function $f$ mapping 
 this set to the part_set (powerset) of X,  (ie. $f(i) = A_i\ (\in (part\_set A))$,) 
 then (indexed_intersection f) will be $\bigcap_{i\in I} A_i$. *)

Definition indexed_intersection: (part_set A).
Simpl.
Apply (Build_Predicate 2![a:A](i:I)(in_part a (f i))).
Red.
Intros.
Apply in_part_comp_l with x.
Apply H.
Assumption.
Defined.


(* Note that as we used "Variable"s, in this section we can write *)
(* "indexed_intersection" instead of (indexed_intersection f). *)
(* The following Lemma then states that \forall i \in I: intersection \subseteq A_i *)
Lemma indexed_intersection_included_in_subsets :
  (i:I) (included indexed_intersection (f i)).
Intro.
Red.
Intros.
Unfold indexed_intersection in H.
Simpl in H.
Apply H.
Qed.

(* if a \in indexed_intersection then a \in A_i (\forall i \in I) *)
Lemma in_indexed_intersection_then_in_subsets :
  (a:A)(in_part a indexed_intersection) -> (i:I)(in_part a (f i)).
Intros.
Unfold indexed_intersection in H.
Simpl in H.
Apply H.
Qed.


(* if a is an element of all A_i, then it is an element of the intersection *)
Lemma in_subsets_then_in_indexed_intersection :
  (a:A)((i:I)(in_part a (f i))) -> (in_part a indexed_intersection).
Intros.
Unfold indexed_intersection.
Simpl.
Assumption.
Qed.

(* contrarily, if for some i \in I a is not in A_i, then neither is it in *)
(* the indexed intersection *)
Lemma not_in_part_then_not_in_indexed_intersection :
  (a:A)(EXT i:I | ~(in_part a (f i))) -> ~(in_part a indexed_intersection).
Intros.
Inversion H.
Simpl.
Intro.
Apply H0.
Apply H1.
Qed.

Lemma not_in_indexed_intersection_then_not_in_part :
  (a:A) ~(in_part a indexed_intersection) -> (EXT i:I | ~(in_part a (f i))).
Intros.
Simpl in H.
Apply (not_all_ex_not I [i:I](in_part a (f i))).
Assumption.
Qed.

(* if one of the A_i is contained in some subset B, then so is the intersection *)
Lemma subset_included_then_indexed_intersection_included : 
  (B:(part_set A))(EXT i:I | (included (f i) B)) -> (included indexed_intersection B).
Intros.
Inversion H.
Unfold included.
Unfold included in H0.
Intros.
Apply H0.
Simpl in H1.
Apply H1.
Qed.

End indexed_int.

(* The following is 'predefined' as "image_map"; I prefer this name: *)
Local range [A,B:Setoid;f:(MAP A B)] := (image f (full A)).

Section Compatibility_of_indexed_intersections.
Variable A:Setoid.
Variable I:Setoid.

(** - If $(F_i)_i$ (indexed by $f$) and $(G_j)_j$ (indexed by $g$) denote the same set 
 of subsets of $A$, then the indexed intersections of the $F_i$ and $G_j$ are equal *)
Lemma indexed_intersection_comp : (f,g:(MAP I (part_set A)))
  (Equal f g) 
    -> (Equal (indexed_intersection f) (indexed_intersection g)).
Intros.
Simpl.
Unfold eq_part.
Intros.
Split.
Intro.
Simpl.
Simpl in H0.
Intro.
Apply in_part_comp_r with (f i);Auto.
Intro.
Simpl.
Simpl in H0.
Intro.
Apply in_part_comp_r with (g i);Auto.
Apply Sym.
Apply H.
Qed.

(** - in fact, even if only the images of the indexing functions are the same, so 
 is their intersection (ie. the index sets $I,J$ may not be equal, but (indexing the 
 subsets by $F$ and $G$) for all $F_i, i \in I$, there is some $G_j, j \in J$ equal 
 to it and vice versa) *)


Variable J:Setoid.
Lemma indexed_intersection_indep_of_indexing :
(f:(MAP I (part_set A))) (g:(MAP J (part_set A)))
  (Equal (range f) (range g)) ->
    (Equal (indexed_intersection f) (indexed_intersection g)).
Intros.
Simpl.
Unfold eq_part.
Intro a.
Split.
Simpl.
Intros H0 j.
Unfold image in H.
Simpl in H.
Unfold eq_part in H.
Simpl in H.
Generalize (H (g j)).
Intros (H1,H2).
Cut (EXT j':J |
            True
            /\((a0:A)
                ((in_part a0 (g j))->(in_part a0 (g j')))
                /\((in_part a0 (g j'))->(in_part a0 (g j))))).
Intro.
Generalize (H2 H3).
Intro.
Inversion_clear H4.
Inversion_clear H5.
Elim (H6 a).
Auto.
Exists j.
Intuition.
Simpl.
Intros H0 i.
Unfold image in H.
Simpl in H.
Unfold eq_part in H.
Simpl in H.
Generalize (H (f i)).
Intros (H1,H2).
Cut (EXT i':I |
            True
            /\((x0:A)
                ((in_part x0 (f i))->(in_part x0 (f i')))
                /\((in_part x0 (f i'))->(in_part x0 (f i))))).
Intro.
Generalize (H1 H3).
Intro.
Inversion_clear H4.
Inversion_clear H5.
Elim (H6 a).
Auto.
Exists i.
Intuition.
Qed.
End Compatibility_of_indexed_intersections.

(** - If $I=\emptyset$ then $\bigcap_{i\in I} X_i = A$ *)

Lemma empty_indexed_intersection_gives_full_set : 
  (A:Setoid;f:(MAP (empty A) (part_set A))) 
    (Equal (indexed_intersection f) (full A)).
Intros.
Unfold indexed_intersection;Simpl.
Red;Simpl;Simpl in f.
Intro a;Split.
Auto.
Intros _ i;Inversion_clear i.
Simpl in subtype_prf.
Contradiction.
Qed.



(** - Fully general intersections of (a set of) sets is introduced as follows: *)

Definition intersection : (A:Setoid)(part_set (part_set A))->(part_set A).
Intros A P.
Simpl.
Apply Build_Predicate with [a:A](p:(part_set A))(in_part p P)->(in_part a p).
Red;Simpl.
Intros.
Apply in_part_comp_l with x;Auto with algebra.
Defined.

Section intersection_v_indexed_intersection.

Lemma intersection_to_indexed_intersection : 
  (A,I:Setoid;f:(MAP I (part_set A)))
    (Equal (intersection (range f)) (indexed_intersection f)).
Intros.
Simpl.
Red.
Split;Simpl;Intros.
Generalize (H (f i)).
Intro p;Apply p.
Exists i;Split;Auto with algebra.
Red.
Split;Auto.
Inversion_clear H0.
Inversion_clear H1.
Apply in_part_comp_r with (f x0);Auto with algebra.
Qed.

End intersection_v_indexed_intersection.
End MAIN.