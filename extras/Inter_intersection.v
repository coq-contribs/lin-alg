(** %\subsection*{ extras :  Inter\_intersection.v }%*)
Set Implicit Arguments. 
Require Export arb_intersections.
Require Export conshdtl.
Require Export Inter.

(** - A nice lemma relating indexed intersections with binary ones.
   Remember that 'indexed_intersection' takes a map from some setoid I to
   the powerset of A, yielding the intersection of the range.
   As it happens, sequences can be such maps (with I=(fin n)).
   So suppose we have an n-length sequence of part_sets of A
   If n=0, its intersection is the full subset of A
   For n+1, take the binary intersection inter with the n-length intersection*)

Fixpoint repeated_inter [A:Setoid;n:nat] :(seq n (part_set A))->(part_set A) :=
<[n:nat](seq n (part_set A))->(part_set A)>
Cases n of O   => [v:(seq O ?)](full A)
      | (S n') => [v:(seq (S n') ?)](inter (head v) (repeated_inter (Seqtl v)))
    end.

Lemma indexed_intersection_as_repeated_inter : (n:nat;A:Setoid;f:(seq n (part_set A))) 
(indexed_intersection f) =' (repeated_inter f).
Intros.
NewInduction n.
Assert (Map (empty A) (part_set A)).
Assert (empty A)->(part_set A).
Intro x;NewDestruct x;Simpl in subtype_prf;Contradiction.
Apply Build_Map with X.
Red.
Intro x;NewDestruct x;Simpl in subtype_prf;Contradiction.
(Apply Trans with (indexed_intersection X);Auto with algebra).
Apply indexed_intersection_indep_of_indexing.
Simpl.
Red;Simpl.
Split;Intro H;Inversion_clear H.
NewDestruct x0.
Inversion_clear in_range_prf.
NewDestruct x0.
Simpl in subtype_prf.
Contradiction.
Simpl.
Apply empty_indexed_intersection_gives_full_set.
Split;Intros.
Split.
Unfold head;Auto.
Elim (IHn (Seqtl f)) with x.
Intros.
Apply H0.
Simpl in H;Simpl.
NewDestruct i;Auto.
Assert (in_part x (inter (head f) (repeated_inter (Seqtl f)))).
Auto.
Simpl.
Intros.
NewDestruct i.
NewDestruct index.
Elim H0;Intros H1 _.
Unfold head in H1.
(Apply in_part_comp_r with (f (Build_finiteT (lt_O_Sn n)));Auto with algebra).
(Apply in_part_comp_r with (Seqtl f (Build_finiteT (lt_S_n ?? in_range_prf)));Auto with algebra).
Elim H0;Intros _ H1.
Assert (in_part x (indexed_intersection (Seqtl f))).
Elim (IHn (Seqtl f)) with x.
Auto.
Simpl in H2;Simpl.
Generalize (H2 (Build_finiteT (lt_S_n??in_range_prf))).
Auto.
Qed.