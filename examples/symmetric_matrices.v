(** %\subsection*{ examples :  symmetric\_matrices.v }%*)
Set Implicit Arguments.
Require Export vecspace_Mmn.
Require Export subspaces.

(** - Two equivalent definitions of being a symmetric matrix. Note that we require
 the matrix to be square a priori, i.e., this is defined not for arbitrary
 $m\times n$-matrices but only for $n\times n$ ones. Symmetric matrices are a subspace. *)

Section defs.
Definition is_symmetric := [F:field;n:Nat;M:(matrix F n n)](i,j:(fin n))(M i j)='(M j i).
Definition is_symmetric' := [F:field;n:Nat;M:(matrix F n n)]M='(transpose M).

Definition is_symmetric_pred : (F:field;n:Nat)(Predicate (Mmn F n n)).
Intros;Apply (Build_Predicate 2!(!is_symmetric F n)).
Red;Simpl;Red.
Intros;Red in H.
(Apply Trans with (x i j);Auto with algebra).
(Apply Trans with (x j i);Auto with algebra).
(Apply Sym;Auto with algebra).
Defined.

Definition is_symmetric'_pred : (F:field;n:Nat)(Predicate (Mmn F n n)).
Intros;Apply (Build_Predicate 2!(!is_symmetric' F n)).
Red;Simpl;Red.
Intros;Red in H.
NewDestruct x;NewDestruct y.
Simpl;Simpl in H H0.
Intros.
(Apply Trans with (Ap2 a b);Auto with algebra).
(Apply Trans with (Ap2 b a);Auto with algebra).
(Apply Trans with (Ap0 b a);Auto with algebra).
(Apply Sym;Auto with algebra).
Defined.

(** - Remember that (part_set X) really has (Predicate X)'s as members *)

Lemma symm_defs_eqv : (F:field;n:Nat)
  (is_symmetric_pred F n)='(is_symmetric'_pred F n) in (part_set (Mmn F n n)).
Intros.
Simpl.
Red.
Split;Simpl;Intro;Red in H;Red.
Unfold transpose;NewDestruct x;Simpl.
Simpl in H;Intros;(Apply Trans with (Ap2 b a);Auto with algebra).
Unfold transpose in H;NewDestruct x;Simpl.
Simpl in H;Intros.
Auto with algebra.
Qed.
End defs.

Lemma symm_matr_subspace : (n:Nat;F:field)(is_subspace (!is_symmetric_pred F n)).
Red;Intros.
Split;Try Split; Simpl.
Red.
Simpl.
Auto with algebra.
Intros.
Red in H0 H.
NewDestruct x;NewDestruct y.
Simpl in H0 H.
Red;Simpl.
Intros.
(Apply SGROUP_comp;Auto with algebra).
Intros;NewDestruct x;Red in H;Red;Simpl in H;Simpl.
Intros.
(Apply RING_comp;Auto with algebra).
Qed.

(** - the subspace itself: *)

Definition symm_subspace := [n,F](alt_Build_subspace (symm_matr_subspace n F)).