(** %\subsection*{ examples :  Matrices.v }%*)
(** - Some preliminary notions about matrices *)
Set Implicit Arguments.
Require Export Map2.
Require Export vecspace_Fn.

Definition Matrix_general_type := [A:Setoid;n,m:Nat](MAP2 (fin n) (fin m) A).

Definition matrix:= [F:field](Matrix_general_type F).

Section add.
Local matrix_addition_fun [F:field;m,n:Nat;M,N:(matrix F m n)]:(matrix F m n).
Intros.
Apply (Build_Map2 4![i,j](M i j)+'(N i j)).
Red.
Intros.
(Apply SGROUP_comp;Auto with algebra).
(Apply (Ap2_comp_proof M);Auto with algebra).
(Apply (Ap2_comp_proof N);Auto with algebra).
Defined.

Definition matrix_addition [F:field;m,n:Nat] :
  (MAP2 (matrix F m n) (matrix F m n) (matrix F m n)).
Intros.
Apply (Build_Map2 4!(!matrix_addition_fun F m n)).
Red.
Simpl;Intros.
(Apply SGROUP_comp;Auto with algebra).
Defined.
End add.

Section mult.
Definition matrix_scmult_fun [F:field;m,n:Nat;c:F;M:(matrix F m n)]:(matrix F m n).
Intros.
Apply (Build_Map2 4![i,j](c rX (M i j))).
Red.
Intros.
(Apply RING_comp;Auto with algebra).
(Apply (Ap2_comp_proof M);Auto with algebra).
Defined.

Definition matrix_scmult [F:field;m,n:Nat]: (MAP2 F  (matrix F m n) (matrix F m n)).
Intros.
Apply (Build_Map2 4!(!matrix_scmult_fun F m n)).
Red.
Simpl;Intros.
(Apply RING_comp;Auto with algebra).
Defined.
End mult.

Section transpose.
Definition transpose : (F:field;m,n:Nat) (matrix F m n)->(matrix F n m).
Intros.
Red.
Red.
Red in X;Red in X.
NewDestruct X.
(Apply (Build_Map2 4![i,j](Ap2 j i));Auto with algebra).
Red in Ap2_comp_proof;Red.
Intros.
Auto with algebra.
Defined.

Definition transpose_map : (F:field;m,n:Nat)(MAP (matrix F m n) (matrix F n m)).
Intros.
Apply (Build_Map 3!(!transpose F m n)).
Red.
Unfold transpose.
Intros;NewDestruct x;NewDestruct y.
Simpl.
Auto with algebra.
Defined.

Lemma transpose_defprop : (F:field;m,n:Nat;M:(matrix F m n);i:(fin n);j:(fin m))
(transpose M i j)='(M j i).
Intros.
Unfold transpose;NewDestruct M;Simpl.
Apply Refl.
Qed.
End transpose.
Hints Resolve transpose_defprop : algebra.

Definition zero_matrix : (F:field;n,m:Nat)(matrix F n m).
Intros.
Apply (Build_Map2 4![i:(fin n);j:(fin m)](zero F)).
Red.
Auto with algebra.
Defined.

Definition is_square := [F:field;n,m:Nat;M:(matrix F n m)]n='m.

Definition is_diagonal := [F:field;n:Nat;M:(matrix F n n)](i,j:(fin n))
  (~(index i)=(index j)) -> (M i j) ='(zero F).

Definition identity_matrix : (F:field;n:Nat)(matrix F n n).
Intros.
Apply (Build_Map2 4![i,j:(fin n)](Kronecker one (zero F) (index i) (index j))).
Red.
Unfold Kronecker.
Intros;NewDestruct x;NewDestruct x';NewDestruct y;NewDestruct y'.
Simpl.
Simpl in H H0.
Rewrite H.
Rewrite H0.
Auto with algebra.
Defined.

Lemma id_is_square : (F:field;n:Nat)(is_square (identity_matrix F n)).
Red.
Simpl.
Auto.
Qed.

Definition row : (F:field;m,n:Nat)(matrix F m n)->(fin m)->(Fn F n)
 := [F,n,m,M,i](Ap2_Map M i).

Definition col : (F:field;m,n:Nat)(matrix F m n)->(fin n)->(Fn F m)
 := [F,n,m,M,j](Ap2_Map' M j).

Lemma row_transpose_col : (F:field;m,n:Nat;M:(matrix F m n);i:(fin m))
  (row M i)='(col (transpose M) i).
Intros;Simpl.
Red;Simpl.
Intros;(Apply Sym;Auto with algebra).
Qed.

Lemma row_comp : (F:field;m,n:Nat;M,M':(matrix F m n);i,i':(fin m))
  M='M' -> i='i' -> (row M i)='(row M' i').
Intros.
Simpl.
Red;Simpl.
Intros.
NewDestruct M;NewDestruct M';Simpl.
Simpl in H.
(Apply Trans with (Ap2 i' x);Auto with algebra).
Qed.

Lemma col_comp : (F:field;m,n:Nat;M,M':(matrix F m n);i,i':(fin n))
  M='M' -> i='i' -> (col M i)='(col M' i').
Intros.
Simpl.
Red;Simpl.
Intros.
NewDestruct M;NewDestruct M';Simpl.
Simpl in H.
(Apply Trans with (Ap2 x i');Auto with algebra).
Qed.

Hints Resolve row_comp col_comp:algebra.