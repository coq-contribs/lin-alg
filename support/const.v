(** %\subsection*{ support :  const.v }%*)
Set Implicit Arguments.
Require Export conshdtl.

Section MAIN.
Variable A:Setoid.

(** - Constant functions and their compatibility 
 %\label{constmap}% *)
Definition const_map : (X,Y:Setoid;y:Y)(MAP X Y).
Intros.
Apply (Build_Map 3![x:X]y).
Red.
Intros.
Apply Refl.
Defined.

Definition const_seq : (n:Nat;a:A)(seq n A).
Intros.
(Apply (const_map (fin n) a);Auto with algebra).
Defined.

Lemma seq_S_O_constseq : (v:(seq (S O) A)) v='(const_seq (S O) (head v)).
Simpl.
Red.
Intros.
Simpl.
Apply seq_S_O_contains_single_elt.
Qed.

Lemma Seqtl_const_seq : (n:Nat;a:A)(Seqtl (const_seq n a))=' (const_seq (pred n) a).
Intros.
Intro i.
Simpl.
NewInduction n.
Auto with algebra.
Case i.
Auto with algebra.
Qed.

Lemma cons_const_seq : (n:Nat;a,a',a'':A) 
  a='a' -> a'='a''
    -> a;;(const_seq n a')='(const_seq (S n) a'').
Intros.
Intro.
NewDestruct x.
NewDestruct index;Simpl;Auto with algebra.
Apply Trans with a';Auto with algebra.
Qed.

(** See random_facts.v for a concat version of this *)
End MAIN.