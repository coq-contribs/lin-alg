(** %\subsection*{ extras :  before\_after.v }%*)
Set Implicit Arguments.
Require Export omit_facts.

(** - Some stuff I thought would be useful some day but wasn't *)

Definition before [N,N':nat;i:(fin N);j:(fin N')] := (lt (index i) (index j)).
Definition after  [N,N':nat;i:(fin N);j:(fin N')] := (gt (index i) (index j)).

Definition notbefore [N,N':nat;i:(fin N);j:(fin N')] := (index i)=(index j) \/ (after i j).
Definition notafter [N,N':nat;i:(fin N);j:(fin N')] := (before i j)\/(index i)=(index j).

Lemma decide_fin : (N,N':nat;i:(fin N);i':(fin N')) (before i i') \/ (index i)=(index i') \/ (after i i').
Simpl.
Unfold before after.
Intros.
Case i;Case i'.
Simpl.
Intros x l x0 l0.
Clear l0 l i' i N N'.
Induction x;Induction x0;Unfold gt;Auto with arith.
Case Hrecx.
Auto with arith.
Intro.
Unfold gt;Case H.
Intro;Left.
Rewrite H0.
Auto.
Unfold gt.
Intro.
Right.
Case H0.
Auto.
Intros.
Cut (lt (S x) (S m))\/(S x)=(S m).
Intro.
Case H2.
Auto.
Auto.
Left.
Auto with arith.
Qed.

Lemma decide_before :(N,N':nat;i:(fin N);j:(fin N')) (before i j)\/(notbefore i j). 
Unfold notbefore.
Apply decide_fin.
Qed.

Lemma decide_after :(N,N':nat;i:(fin N);j:(fin N')) (after i j)\/(notafter i j).  
Unfold notafter.
Intros.
Case (decide_before i j).
Auto.
Unfold notbefore.
Tauto.
Qed.

Lemma seq_properties_split_before_eq_after : (A:Setoid;n:nat;v:(seq n A);i:(fin n);P:(Predicate A))
((j:(fin n))(before j i)->(Pred_fun P (v j))) -> (Pred_fun P (v i)) -> ((j:(fin n))(after j i)->(Pred_fun P (v j))) -> (j:(fin n))(Pred_fun P (v j)).
Intros.
Case (decide_fin j i);Auto.
Intro.
Case H2;Auto.
Generalize H0.
Elim P.
Simpl.
Unfold pred_compatible.
Intros.
(Apply Pred_compatible_prf with (v i);Auto with algebra).
Qed.


Lemma predicate_split_seq_before_notbefore : (A:Setoid;n:nat;v:(seq n A);i:(fin n);P:(Predicate A))
((j:(fin n))(before j i)->(Pred_fun P (v j))) -> ((j:(fin n))(notbefore j i)->(Pred_fun P (v j))) -> (j:(fin n))(Pred_fun P (v j)).
Intros.
Case (decide_before j i);Auto.
Qed.

Lemma predicate_split_seq_after_notafter : (A:Setoid;n:nat;v:(seq n A);i:(fin n);P:(Predicate A))
((j:(fin n))(after j i)->(Pred_fun P (v j))) -> ((j:(fin n))(notafter j i)->(Pred_fun P (v j))) -> (j:(fin n))(Pred_fun P (v j)).
Intros.
Case (decide_after j i);Auto.
Qed.

Lemma seq_properties_split_before_notbefore : (A:Setoid;n:nat;v:(seq n A);i:(fin n);P:A->Prop)
((j:(fin n))(before j i)->(P (v j))) -> ((j:(fin n))(notbefore j i)->(P (v j))) -> (j:(fin n))(P (v j)).
Intros.
Case (decide_before j i);Auto.
Qed.

Lemma seq_properties_split_after_notafter : (A:Setoid;n:nat;v:(seq n A);i:(fin n);P:A->Prop)
((j:(fin n))(after j i)->(P (v j))) -> ((j:(fin n))(notafter j i)->(P (v j))) -> (j:(fin n))(P (v j)).
Intros.
Case (decide_after j i);Auto.
Qed.


Definition next : (n:nat)(fin n)->(fin (S n)) := [n:nat;i:(fin n)]Cases i of 
 (Build_finiteT ni Hi)=>(Build_finiteT (lt_n_S??Hi)) end.
Definition prev : (n:nat)(i:(fin (S n)))~i='(Build_finiteT (lt_O_Sn n))->(fin n).
Intros n i;Case i.
Intro x;Case x.
Simpl.
Intros.
Absurd O=O;Auto.
Intros.
Exact (Build_finiteT (lt_S_n??in_range_prf)).
Defined.