(** %\subsection*{ examples :  symmetric\_matrices.v }%*)
Set Implicit Arguments.
Unset Strict Implicit.
Require Export vecspace_Mmn.
Require Export subspaces.

(** - Two equivalent definitions of being a symmetric matrix. Note that we require
 the matrix to be square a priori, i.e., this is defined not for arbitrary
 $m\times n$-matrices but only for $n\times n$ ones. Symmetric matrices are a subspace. *)

Section defs.
Definition is_symmetric (F : field) (n : Nat) (M : matrix F n n) :=
  forall i j : fin n, M i j =' M j i in _.
Definition is_symmetric' (F : field) (n : Nat) (M : matrix F n n) :=
  M =' transpose M in _.

Definition is_symmetric_pred :
  forall (F : field) (n : Nat), Predicate (Mmn F n n).
intros; apply (Build_Predicate (Pred_fun:=is_symmetric (F:=F) (n:=n))).
red in |- *; simpl in |- *; red in |- *.
intros; red in H.
apply Trans with (x i j); auto with algebra.
apply Trans with (x j i); auto with algebra.
apply Sym; auto with algebra.
Defined.

Definition is_symmetric'_pred :
  forall (F : field) (n : Nat), Predicate (Mmn F n n).
intros; apply (Build_Predicate (Pred_fun:=is_symmetric' (F:=F) (n:=n))).
red in |- *; simpl in |- *; red in |- *.
intros; red in H.
destruct x; destruct y.
simpl in |- *; simpl in H, H0.
intros.
apply Trans with (Ap2 a b); auto with algebra.
apply Trans with (Ap2 b a); auto with algebra.
apply Trans with (Ap0 b a); auto with algebra.
apply Sym; auto with algebra.
Defined.

(** - Remember that (part_set X) really has (Predicate X)'s as members *)

Lemma symm_defs_eqv :
 forall (F : field) (n : Nat),
 is_symmetric_pred F n =' is_symmetric'_pred F n in part_set (Mmn F n n).
intros.
simpl in |- *.
red in |- *.
split; simpl in |- *; intro; red in H; red in |- *.
unfold transpose in |- *; destruct x; simpl in |- *.
simpl in H; intros; (apply Trans with (Ap2 b a); auto with algebra).
unfold transpose in H; destruct x; simpl in |- *.
simpl in H; intros.
auto with algebra.
Qed.
End defs.

Lemma symm_matr_subspace :
 forall (n : Nat) (F : field), is_subspace (is_symmetric_pred F n).
red in |- *; intros.
split; try split; simpl in |- *.
red in |- *.
simpl in |- *.
auto with algebra.
intros.
red in H0, H.
destruct x; destruct y.
simpl in H0, H.
red in |- *; simpl in |- *.
intros.
apply SGROUP_comp; auto with algebra.
intros; destruct x; red in H; red in |- *; simpl in H; simpl in |- *.
intros.
apply RING_comp; auto with algebra.
Qed.

(** - the subspace itself: *)

Definition symm_subspace n F := alt_Build_subspace (symm_matr_subspace n F).