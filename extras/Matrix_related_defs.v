(** %\subsection*{ extras :  Matrix\_related\_defs.v }%*)
Set Implicit Arguments.
Unset Strict Implicit.
Require Export Matrices.
Require Export sums.

Section defs.
Variable F : field.
Variable n : Nat.
Variable M : matrix F n n.

Definition the_diagonal : seq n F.
apply (Build_Map (Ap:=fun i : fin n => M i i)).
red in |- *.
intros.
destruct M.
simpl in |- *.
apply Ap2_comp_proof; auto with algebra.
Defined.

Definition trace := sum the_diagonal.
End defs.