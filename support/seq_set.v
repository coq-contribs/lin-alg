(** %\subsection*{ support :  seq\_set.v }%*)
(** - From seqs we can make (sub)setoids containing exactly the listed elements:
 (seq_set v) = $\{a\in A | \exists i. a=v_i\}$.
 Note that v:(seq n A) doesn't give us an n-element set a priori since 
 v may contain duplicates. *)

Set Implicit Arguments.
Require Export finite.
Require Export Parts.

Section MAIN.

(** %\label{seqset}% *)
Definition seq_set : (A:Setoid;n:Nat;v:(seq n A)) (part_set A).
Intros.
Simpl.
Apply (Build_Predicate 2!([a:A](EXT i:(fin n) | a =' (v i)))).
Red.
Intros.
Inversion H.
Exists x0.
(Apply Trans with x;Auto with algebra).
Defined.

Variable A:Setoid.
Variable n:Nat.

Lemma seq_set_comp : (v,v':(seq n A)) v='v'->(seq_set v)='(seq_set v').
Intros.
Simpl.
Red.
Split.
Simpl.
Simpl in H.
Red in H.
Intro P;Inversion_clear P.
Exists x0.
(Apply Trans with (v x0);Auto with algebra).
Simpl.
Simpl in H.
Red in H.
Intro P;Inversion_clear P.
Exists x0.
(Apply Trans with (v' x0);Auto with algebra).
Qed.

End MAIN.
Hints Resolve seq_set_comp : algebra.
