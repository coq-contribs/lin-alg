(** %\subsection*{ extras :  Equality\_structures.v }%*)
Set Implicit Arguments.
Require Export seq_equality_facts.

(** - This is a rather experimental file.
 - Remember how we defined not only a setoid of sequences (seq n A) 
 for each n:nat and A:Setoid, but also a new equality predicate seq_equal 
 spanning all sequences over A. Perhaps we can generalize this idea: 
 in a setoid, the equality comes with the definition of the setoid, which 
 is in a sense "prior" to the equality; we have no equality unless we 
 have a setoid. Here I try to reverse things by defining a predicate 
 spanning many setoids that has some nice properties, such as being 
 refl, symm, and trans, and nicely restricts to, and extends the setoid 
 equalities just like seq_equal *)

Section defs.
Variable A:Setoid.
Variable I:A->Setoid.
Definition StrEqType := (a,b:A)(I a)->(I b)->Prop.
Record EqStructure : Type :=
{ StrEq       :> (a,b:A)(I a)->(I b)->Prop
; StrEqRefl   :  (a:A;x:(I a))(StrEq ?? x x)
; StrEqSym    :  (a,b:A;x:(I a);y:(I b))(StrEq ?? x y)->(StrEq ?? y x)
; StrEqTrans  :  (a,b,c:A;x:(I a);y:(I b);z:(I c))(StrEq ?? x y)->(StrEq ?? y z)->(StrEq ?? x z)
; StrEqRestr  :  (a:A;x,y:(I a))(StrEq ?? x y)->x='y in (I a)
; StrEqExtend :  (a:A;x,y:(I a))x='y in (I a)->(StrEq ?? x y)
; StrEqIndex  :  (a,b:A;x:(I a);y:(I b))(StrEq ?? x y)->a='b in A}.
End defs.

Definition seq_eq_str [A:Setoid] : (EqStructure [n:Nat](seq n A)).
Intro.
(Apply (Build_EqStructure 2![n:Nat](seq n A) 3![n,m:Nat;v:(seq n A);w:(seq m A)](seq_equal v w));Auto with algebra).
Intros.
(Apply seq_equal_trans with w:=y;Auto with algebra).
2:Intros.
2:Simpl.
2:(Apply seq_equal_length_equal with v:=x w:=y;Auto with algebra).
Simpl.
Intros;Red in H;Red;Simpl in H;Simpl.
Intros.
Elim (le_or_lt a i).
Right.
Auto.
Left.
Exists H0;Exists H0.
Auto.
Defined.


Definition fin_eq_str : (EqStructure [n:Nat](fin n)).
(Apply (Build_EqStructure 2![n:Nat](fin n) 3![n,m;i:(fin n);j:(fin m)](n==m/\(index i)=(index j)));Auto with algebra).
Intros.
Intuition.
Intuition.
Transitivity b;Auto.
Transitivity (index y);Auto.
Intros.
Simpl.
Inversion_clear H.
Auto.
Intros.
Simpl.
Inversion_clear H.
Rewrite H0.
Auto.
Defined.

Definition fin_eq := (StrEq fin_eq_str).

Lemma test1 : (n:nat;i:(fin n))(fin_eq i i).
Intros.
Red.
Simpl.
Split;Auto.
Qed.

Definition seq_eq := [A:Setoid](StrEq (seq_eq_str A)).

Lemma test2 : (A:Setoid;n,m:nat;v:(seq n A);w:(seq m A))(seq_eq v w)->(seq_eq w v).
Intros.
Red.
Simpl.
Red in H;Simpl in H.
Auto with algebra.
Qed.

(** - Somthing I'd like to do is somehow enable EqStructures to span setoids indexed
 by more than one setoid; something like [MatEqStr : (EqStructure [n,m:Nat](matrix F n m))]
 instead of (modulo correction of notation) [MatEqStr : (EqStructure
 [nm:(cartesian_prod Nat Nat)](matrix F (pi1 nm) (pi2 nm)))] *)