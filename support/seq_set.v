(** %\subsection*{ support :  seq\_set.v }%*)
(** - From seqs we can make (sub)setoids containing exactly the listed elements:
 (seq_set v) = $\{a\in A | \exists i. a=v_i\}$.
 Note that v:(seq n A) doesn't give us an n-element set a priori since 
 v may contain duplicates. *)

Set Implicit Arguments.
Unset Strict Implicit.
Require Export finite.
Require Export Parts.

Section MAIN.

(** %\label{seqset}% *)
Definition seq_set : forall (A : Setoid) (n : Nat) (v : seq n A), part_set A.
intros.
simpl in |- *.
apply
 (Build_Predicate (Pred_fun:=fun a : A => exists i : fin n, a =' v i in _)).
red in |- *.
intros.
inversion H.
exists x0.
apply Trans with x; auto with algebra.
Defined.

Variable A : Setoid.
Variable n : Nat.

Lemma seq_set_comp :
 forall v v' : seq n A, v =' v' in _ -> seq_set v =' seq_set v' in _.
intros.
simpl in |- *.
red in |- *.
split.
simpl in |- *.
simpl in H.
red in H.
intro P; inversion_clear P.
exists x0.
apply Trans with (v x0); auto with algebra.
simpl in |- *.
simpl in H.
red in H.
intro P; inversion_clear P.
exists x0.
apply Trans with (v' x0); auto with algebra.
Qed.

End MAIN.
Hint Resolve seq_set_comp: algebra.