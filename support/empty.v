(** %\subsection*{ support :  empty.v }%*)
Set Implicit Arguments.
Unset Strict Implicit.
Require Export seq_set.
(** - Lemmas on empty sets and sequences *)

(* The empty sequences: *)
(** %\label{emptyseq}% *)
Definition empty_seq : forall A : Setoid, seq 0 A.
intro.
apply
 (Build_Map
    (Ap:=fun i : fin 0 =>
         match i with
         | Build_finiteT n Hn => False_rect A (lt_n_O n Hn)
         end)); auto with algebra.
red in |- *.
intros.
apply False_ind; auto with algebra.
Defined.

Lemma seq_O_is_empty :
 forall (A : Setoid) (v : seq 0 A), v =' empty_seq A in _.
intros.
simpl in |- *.
red in |- *.
intros.
apply False_ind; auto with algebra.
Qed.

Hint Resolve seq_O_is_empty: algebra.


Lemma seq_set_empty_seq_is_empty :
 forall (A : Setoid) (v : seq 0 A), seq_set v =' empty A in _.
intros.
apply Trans with (seq_set (empty_seq A)); auto with algebra.
simpl in |- *.
red in |- *.
split.
intro.
simpl in H.
inversion H; (apply False_ind; auto with algebra).
intro.
simpl in H.
contradiction.
Qed.

Hint Resolve seq_set_empty_seq_is_empty: algebra.


(* The only sequence of empty-set-elements is the empty sequence *)
Lemma no_seq_n_empty :
 forall (n : Nat) (A : Setoid) (W : part_set A),
 W =' empty A in _ -> seq n W -> n =' 0 in _.
intros; simpl in n; simpl in |- *.
destruct n.
auto.
intros.
elim (X (Build_finiteT (lt_O_Sn n))).
intros a Ha.
simpl in H; red in H; simpl in H.
elim (H a).
intros.
generalize (H0 Ha).
intro.
contradiction.
Qed.