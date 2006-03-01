(** %\subsection*{ extras :  Inter\_intersection.v }%*)
Set Implicit Arguments.
Unset Strict Implicit. 
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

Fixpoint repeated_inter (A : Setoid) (n : nat) {struct n} :
 seq n (part_set A) -> part_set A :=
  match n return (seq n (part_set A) -> part_set A) with
  | O => fun v : seq 0 _ => full A
  | S n' => fun v : seq (S n') _ => inter (head v) (repeated_inter (Seqtl v))
  end.

Lemma indexed_intersection_as_repeated_inter :
 forall (n : nat) (A : Setoid) (f : seq n (part_set A)),
 indexed_intersection f =' repeated_inter f in _.
intros.
induction n.
assert (Map (empty A) (part_set A)).
assert (empty A -> part_set A).
intro x; destruct x; simpl in subtype_prf; contradiction.
apply Build_Map with X.
red in |- *.
intro x; destruct x; simpl in subtype_prf; contradiction.
apply Trans with (indexed_intersection X); auto with algebra.
apply indexed_intersection_indep_of_indexing.
simpl in |- *.
red in |- *; simpl in |- *.
split; intro H; inversion_clear H.
destruct x0.
inversion_clear in_range_prf.
destruct x0.
simpl in subtype_prf.
contradiction.
simpl in |- *.
apply empty_indexed_intersection_gives_full_set.
split; intros.
split.
unfold head in |- *; auto.
elim (IHn (Seqtl f)) with x.
intros.
apply H0.
simpl in H; simpl in |- *.
destruct i; auto.
assert (in_part x (inter (head f) (repeated_inter (Seqtl f)))).
auto.
simpl in |- *.
intros.
destruct i.
destruct index as [| n0].
elim H0; intros H1 _.
unfold head in H1.
apply in_part_comp_r with (f (Build_finiteT (lt_O_Sn n))); auto with algebra.
apply in_part_comp_r with (Seqtl f (Build_finiteT (lt_S_n _ _ in_range_prf)));
 auto with algebra.
elim H0; intros _ H1.
assert (in_part x (indexed_intersection (Seqtl f))).
elim (IHn (Seqtl f)) with x.
auto.
simpl in H2; simpl in |- *.
generalize (H2 (Build_finiteT (lt_S_n _ _ in_range_prf))).
auto.
Qed.