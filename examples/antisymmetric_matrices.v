(** %\subsection*{ examples :  antisymmetric\_matrices.v }%*)
Set Implicit Arguments.
Require Export vecspace_Mmn.
Require Export subspaces.

Definition is_antisymmetric := [F:field;n:Nat;M:(Mmn F n n)]
  (i,j:(fin n))(M i j)='(min (M j i)).

Definition is_antisymmetric_pred : (F:field;n:Nat)(Predicate (Mmn F n n)).
Intros;Apply (Build_Predicate 2!(!is_antisymmetric F n)).
Red;Simpl.
Intros.
Red;Red in H.
Intros.
(Apply Trans with (x i j);Auto with algebra).
(Apply Trans with (min (x j i));Auto with algebra).
(Apply GROUP_comp;Auto with algebra).
(Apply Sym;Auto with algebra).
Defined.

Lemma antisymm_matr_subspace : (n:Nat;F:field)
  (is_subspace (!is_antisymmetric_pred F n)).
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
(Apply Trans with (min (Ap2 j i))+' (min (Ap0 j i));Auto with algebra).
(Apply Trans with (min (Ap0 j i))+' (min (Ap2 j i));Auto with algebra).
Intros;NewDestruct x;Red in H;Red;Simpl in H;Simpl.
Intros.
(Apply Trans with c rX (min (Ap2 j i));Auto with algebra).
Qed.

Definition antisym_subspace := 
  [n,F](alt_Build_subspace (antisymm_matr_subspace n F)).