(** %\subsection*{ examples :  up\_lo\_triang\_mat.v }%*)
Set Implicit Arguments.
Require Export vecspace_Mmn.
Require Export subspaces.
 
(** - Upper, lower and diagonal matrices. Note that whereas the triangular matrices may
 be generally $m\times n$, diagonal matrices must be $n\times n$. *)

Definition is_up_triang := [F:field;m,n:Nat;M:(matrix F m n)]
  (i:(fin m);j:(fin n))(lt (index j) (index i))->(M i j)='(zero F).

Definition is_lo_triang := [F:field;m,n:Nat;M:(matrix F m n)]
  (i:(fin m);j:(fin n))(lt (index i) (index j))->(M i j)='(zero F).

Definition is_upper_triangular_pred : (F:field;m,n:Nat)(Predicate (Mmn F m n)).
Intros.
Apply (Build_Predicate 2!(!is_up_triang F m n)).
Red;Simpl;Red.
Intros.
Red in H.
(Apply Trans with (x i j);Auto with algebra).
Defined.

Definition is_lower_triangular_pred : (F:field;m,n:Nat)(Predicate (Mmn F m n)).
Intros.
Apply (Build_Predicate 2!(!is_lo_triang F m n)).
Red;Simpl;Red.
Intros.
Red in H.
(Apply Trans with (x i j);Auto with algebra).
Defined.

Definition is_diagonal_pred : (F:field;n:Nat)(Predicate (Mmn F n n)).
Intros.
Apply (Build_Predicate 2!(!is_diagonal F n)).
Red;Simpl;Red.
Intros.
Red in H.
(Apply Trans with (x i j);Auto with algebra).
Defined.

Section trivial_lemmas.
Lemma id_is_diagonal : (F:field;n:Nat)(is_diagonal (identity_matrix F n)).
Simpl.
Red.
Simpl.
Intros;NewDestruct i;NewDestruct j.
Simpl;Simpl in H.
(Apply Kronecker_case_unequal;Auto with algebra).
Qed.

Lemma is_upper_and_lower_then_diagonal : (F:field;n:Nat;M:(matrix F n n))
  (is_up_triang M) -> (is_lo_triang M) -> (is_diagonal M).
Intros;Red in H H0.
Red.
Intros.
Case (nat_total_order ?? H1);Intro;Auto with algebra.
Qed.
End trivial_lemmas.

Lemma up_triang_subspace : (F:field;m,n:Nat)
  (is_subspace (is_upper_triangular_pred F m n)).
Intros.
Red.
Split;Try Split.
Simpl.
Red.
Intros;Simpl.
Auto with algebra.
Intros.
Red in H0 H.
Simpl;Red.
Intros.
(Apply Trans with (x i j)+'(y i j);Auto with algebra).
(Apply Trans with (zero F)+'(zero F);Auto with algebra).
Intros;Simpl in H;Red in H;Simpl;Red.
Intros;(Apply Trans with (c rX (zero F));Auto with algebra).
Simpl.
(Apply RING_comp;Auto with algebra).
Qed.

Lemma lo_triang_subspace : (F:field;m,n:Nat)
  (is_subspace (is_lower_triangular_pred F m n)).
Intros.
Red.
Split;Try Split.
Simpl.
Red.
Intros;Simpl.
Auto with algebra.
Intros.
Red in H0 H.
Simpl;Red.
Intros.
(Apply Trans with (x i j)+'(y i j);Auto with algebra).
(Apply Trans with (zero F)+'(zero F);Auto with algebra).
Intros;Simpl in H;Red in H;Simpl;Red.
Intros;(Apply Trans with (c rX (zero F));Auto with algebra).
Simpl.
(Apply RING_comp;Auto with algebra).
Qed.

Lemma is_diagonal_subspace : (F:field;n:Nat)
  (is_subspace (is_diagonal_pred F n)).
Intros.
Red.
Split;Try Split.
Simpl.
Red.
Intros;Simpl.
Auto with algebra.
Intros.
Red in H0 H.
Simpl;Red.
Intros.
(Apply Trans with (x i j)+'(y i j);Auto with algebra).
(Apply Trans with (zero F)+'(zero F);Auto with algebra).
Intros;Simpl in H;Red in H;Simpl;Red.
Intros;(Apply Trans with (c rX (zero F));Auto with algebra).
Simpl.
(Apply RING_comp;Auto with algebra).
Qed.
