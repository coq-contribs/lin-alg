(** %\subsection*{ support :  empty.v }%*)
Set Implicit Arguments.
Require Export seq_set.
(** - Lemmas on empty sets and sequences *)

(* The empty sequences: *)
(** %\label{emptyseq}% *)
Definition empty_seq : (A:Setoid)(seq O A).
Intro.
(Apply (Build_Map 3![i:(fin O)]Cases i of (Build_finiteT n Hn) => (False_rect A (lt_n_O n Hn)) end);Auto with algebra).
Red.
Intros.
(Apply False_ind;Auto with algebra).
Defined.

Lemma seq_O_is_empty : (A:Setoid;v:(seq O A)) v='(empty_seq A).
Intros.
Simpl.
Red.
Intros.
(Apply False_ind;Auto with algebra).
Qed.

Hints Resolve seq_O_is_empty : algebra.


Lemma seq_set_empty_seq_is_empty : (A:Setoid;v:(seq O A)) (seq_set v)='(empty A).
Intros.
(Apply Trans with (seq_set (empty_seq A));Auto with algebra).
Simpl.
Red.
Split.
Intro.
Simpl in H.
Inversion H;(Apply False_ind;Auto with algebra).
Intro.
Simpl in H.
Contradiction.
Qed.

Hints Resolve seq_set_empty_seq_is_empty : algebra.


(* The only sequence of empty-set-elements is the empty sequence *)
Lemma no_seq_n_empty : (n:Nat;A:Setoid;W:(part_set A)) W='(empty A)->(seq n W)->n='O.
Intros;Simpl in n;Simpl.
NewDestruct n.
Auto.
Intros.
Elim (X (Build_finiteT (lt_O_Sn n))).
Intros a Ha.
Simpl in H;Red in H;Simpl in H.
Elim (H a).
Intros.
Generalize (H0 Ha).
Intro.
Contradiction.
Qed.
