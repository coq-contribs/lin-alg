(** %\subsection*{ support :  distinct.v }%*)
(** - "Distinct" is a fairly basic notion saying that all elements of a sequence
 are distinct (i.e. we have an injection $\{0...n-1\}\to A$) *)
Set Implicit Arguments.
Require Export finite.
Require Export Parts.

(** %\label{distinct}% *)
Definition distinct [A:Setoid; n:Nat; v:(seq n A)] := (i,j:(fin n)) ~i='j->~(v i)='(v j).

Lemma distinct_comp : (A:Setoid;n:Nat;v,v':(seq n A)) (distinct v)->v='v'->(distinct v').
Unfold distinct.
Intros.
Simpl in H0;Red in H0.
Red in H;Red;Intro.
Apply H with i j;Auto with algebra.
(Apply Trans with (v' i);Auto with algebra).
(Apply Trans with (v' j);Auto with algebra).
Qed.

Hints Resolve distinct_comp : algebra.

Definition distinct_pred [A:Setoid;n:Nat] : (Predicate (seq n A)). 
Intros.
(Apply (Build_Predicate 2!(!distinct A n));Auto with algebra).
Red.
Intros.
(Apply distinct_comp with x;Auto with algebra).
Defined.

