(** %\subsection*{ examples :  Matrix\_multiplication.v }%*)
Set Implicit Arguments.
Require Export vecspace_Mmn.
Require Export pointwise.
Require Export sums.

(** - Remember that (Fn F n) is the vectorspace $F^n$, based on the setoid (seq n F),
 and (Mmn F m n) is the vectorspace $M_{mn}$ of $m\times n$-matrices over $F$; based 
 on the setoid (matrix F m n) *)

Section matrix_x_vector.
Definition mat_vec_mult_fun : (F:field;m,n:Nat) (Mmn F m n)->(Fn F n)->(Fn F m).
Intros.
Simpl in X X0.
Simpl.
Apply (Build_Map 3![i:(fin m)](sum (pointwise (uncurry (RING_comp 1!F)) (Ap2_Map X i) X0))).
Red;Simpl.
Intros.
(Apply sum_comp;Auto with algebra);(Apply toMap;Apply pointwise_comp;Auto with algebra).
Simpl.
Red;Simpl.
Intro;NewDestruct X;Simpl;Auto with algebra.
Defined.

Definition matXvec : (F:field;m,n:Nat)(Map2 (Mmn F m n) (Fn F n) (Fn F m)).
Intros;Apply (Build_Map2 4!(!mat_vec_mult_fun F m n)).
Red;Simpl;Red;Simpl.
Intros.
(Apply sum_comp;Auto with algebra);(Apply toMap;Apply pointwise_comp;Auto with algebra).
Simpl.
Red;Simpl.
Intro;(Apply H;Auto with algebra).
Defined.
End matrix_x_vector.

Section matrix_x_matrix.
Definition mat_mat_mult_fun : (F:field;m,n,p:Nat)
  (Mmn F m n)->(Mmn F n p)->(Mmn F m p).
Intros F m n p M N.
Apply (Build_Map2 4![i,j](sum (pointwise (uncurry (RING_comp 1!F)) (row M i) (col N j)))).
Red;Simpl.
Intros.
(Apply sum_comp;Auto with algebra).
(Apply toMap;Apply pointwise_comp;Auto with algebra).
Change (row M x) =' (row M x').
(Apply row_comp;Auto with algebra).
Change (col N y) =' (col N y').
(Apply col_comp;Auto with algebra).
Defined.

Definition matXmat : (F:field;m,n,p:Nat)(Map2 (Mmn F m n) (Mmn F n p) (Mmn F m p)).
Intros;Apply (Build_Map2 4!(!mat_mat_mult_fun F m n p)).
Red;Simpl.
Intros.
(Apply sum_comp;Auto with algebra);(Apply toMap;Apply pointwise_comp;Auto with algebra).
Change (row x i) =' (row x' i').
(Apply row_comp;Auto with algebra).
Change (col y j) =' (col y' j').
(Apply col_comp;Auto with algebra).
Defined.
End matrix_x_matrix.

Section facts.
Variable F:field.
Variable n,m,p:Nat.
Variable M:(Mmn F m n).
Variable N:(Mmn F n p).
Lemma matXmat_col : (i:(fin p))
  (col (matXmat ???? M N) i)='(matXvec ??? M (col N i)).
Intros.
Unfold col matXmat matXvec.
Simpl.
Red;Simpl.
Intros.
(Apply sum_comp;Auto with algebra).
Qed.
End facts.

Section morefacts.
Require Export Cfield_facts.
Variable F:cfield.
Variable n,m,p:Nat.
Variable M:(Mmn F m n).
Variable N:(Mmn F n p).
Lemma matXmat_row : (i:(fin m))
  (row (matXmat ???? M N) i)='(matXvec ??? (transpose N) (row M i)).
Intros.
Unfold transpose row matXmat matXvec.
Simpl.
NewDestruct N.
Red;Simpl.
Unfold row col.
Intros.
(Apply sum_comp;Auto with algebra).
Simpl.
Red;Simpl.
Auto with algebra.
Qed.
End morefacts.
(* Note that one needs the fact that F is a *commutative* field *)