(** %\subsection*{ support :  seq\_set\_seq.v }%*)
Set Implicit Arguments.
Unset Strict Implicit.
Require Export seq_set.

(** - Suppose we have a sequence $a=\langle a_0,...,a_{n-1}\rangle$ of elements of
 Setoid A. We can make a Setoid out of those: $\{a_0...a_{n-1}\}$, ie. (seq_set a) 
 Now the original sequence a "is" also a sequence of elements of this new Setoid 
 This "new" sequence (ie. the old one in a new guise) is (seq_set_seq a) *)

Let seq_set_fun :
  forall (A : Setoid) (n : Nat) (v : seq n A), fin n -> (seq_set v:Type).
intros.
apply (Build_subtype (P:=seq_set v:Predicate _) (subtype_elt:=v X)).
simpl in |- *.
exists X.
apply Refl.
Defined.

(** %\label{seqsetseq}% *)
Definition seq_set_seq :
  forall (A : Setoid) (n : Nat) (v : seq n A), seq n (seq_set v).
intros.
simpl in |- *.
apply (Build_Map (Ap:=seq_set_fun v)).
red in |- *.
intros.
simpl in |- *.
red in |- *.
simpl in |- *.
apply Ap_comp; auto with algebra.
Defined.