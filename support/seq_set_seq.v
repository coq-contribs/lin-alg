(** %\subsection*{ support :  seq\_set\_seq.v }%*)
Set Implicit Arguments.
Require Export seq_set.

(** - Suppose we have a sequence $a=\langle a_0,...,a_{n-1}\rangle$ of elements of
 Setoid A. We can make a Setoid out of those: $\{a_0...a_{n-1}\}$, ie. (seq_set a) 
 Now the original sequence a "is" also a sequence of elements of this new Setoid 
 This "new" sequence (ie. the old one in a new guise) is (seq_set_seq a) *)

Local seq_set_fun : (A:Setoid;n:Nat;v:(seq n A)) (fin n)-> ((seq_set v)::Type).
Intros.
Apply (!Build_subtype ? (seq_set v)::(Predicate ?) (v X)).
Simpl.
Exists X.
Apply Refl.
Defined.

(** %\label{seqsetseq}% *)
Definition seq_set_seq : (A:Setoid;n:Nat;v:(seq n A)) (seq n (seq_set v)).
Intros.
Simpl.
Apply (Build_Map 3!(seq_set_fun v)).
Red.
Intros.
Simpl.
Red.
Simpl.
(Apply Ap_comp;Auto with algebra).
Defined.
