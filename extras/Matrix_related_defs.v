(** %\subsection*{ extras :  Matrix\_related\_defs.v }%*)
Set Implicit Arguments.
Require Export Matrices.
Require Export sums.

Section defs.
Variable F:field.
Variable n:Nat.
Variable M:(matrix F n n).

Definition the_diagonal : (seq n F).
Apply (Build_Map 3![i:(fin n)](M i i)).
Red.
Intros.
NewDestruct M.
Simpl.
(Apply Ap2_comp_proof;Auto with algebra).
Defined.

Definition trace := (sum the_diagonal).
End defs.