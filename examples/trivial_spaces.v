(** %\subsection*{ examples :  trivial\_spaces.v }%*)
Set Implicit Arguments.
Require Export bases_finite_dim.
Require Export Singleton.
Require Export alt_build_vecsp.
(** - Here we will make the trivial vectorspace as an example of vectorspaces. Notice
 this differs from the trivial subspace defined in subspaces.v *)

(** -  The underlying set contains only the zero vector; we can take an arbitrary set
 and an arbitrary element on which we build the trivial vectorspace containing only 
 that element as the zero vector *)

Section MAIN.
Variable A:Setoid.
Variable a:A.

Local T:=(single a).

Definition Tplus : (Map2 T T T).
Apply Build_Map2 with [t,t':(single a)](Build_subtype ((Refl a)::(Pred_fun (single a) a))).
Red.
Intros.
Auto with algebra.
Defined.

Definition Tzero : T := (Build_subtype ((Refl a)::(Pred_fun (single a) a))).

Definition Tminus : (Map T T).
Apply Build_Map with [t:T]t.
Red.
Auto.
Defined.

Variable F:field.

Definition Tmult : (Map2 F T T).
Apply Build_Map2 with [f:F;t:T]t.
Red.
Auto.
Defined.

Definition trivvecsp : (vectorspace F).
Apply alt_Build_vectorspace with T Tplus Tmult Tzero Tminus;Red;Auto with algebra.
Simpl.
Red.
Intro;NewDestruct x.
Simpl in subtype_prf.
Simpl.
Auto with algebra.
Simpl.
Red.
Simpl.
Intros;NewDestruct x;Simpl in subtype_prf;Simpl;Auto with algebra.
Defined.
End MAIN.

Section basis.
Variable F:field.
Require Export bases.
Variable A:Setoid.
Variable a:A.
Definition triv_basis : (basis (trivvecsp a F)).
Apply Build_basis with (empty (trivvecsp a F)).
Red.
Split.
Red.
Simpl.
Red.
Simpl.
Split;Auto;Intros _.
Red.
Exists O.
Exists (empty_seq F).
Exists (empty_seq (empty (single a))).
Simpl.
NewDestruct x.
Red.
Simpl.
Simpl in subtype_prf.
Auto.
Apply empty_lin_indep.
Defined.

(* More generally: *)
Definition trivial_basis : (V:(vectorspace F))
  (full V)='(single (zero V)) -> (basis V).
Intros.
Apply Build_basis with (empty V).
Red.
Split.
2:Apply empty_lin_indep.
Red.
Apply Trans with (single (zero V));Auto with algebra.
Simpl.
Red.
Simpl.
Split;Intros.
Red in H0.
Inversion_clear H0.
Inversion_clear H1.
Inversion_clear H0.
Assert x0='O.
Generalize no_seq_n_empty;Intro p.
Apply (p ? V (empty V) (Refl (empty V)) x2).
Simpl in H0.
Move H0 after x1.
Generalize Dependent x0.
Intros x0 H0.
Rewrite H0.
Clear H0 x0.
Simpl.
Auto.

Apply is_lin_comb_comp with (zero V) (empty V);Auto with algebra.
Red.
Exists O.
Simpl.
Exists (empty_seq F).
Exists (empty_seq (empty V)).
Auto with algebra.
Defined.


Lemma trivial_then_has_dim_zero : (V:(vectorspace F)) (full V)='(single (zero V)) -> (has_dim O V).
Intros.
Red.
Exists (trivial_basis H).
Simpl.
Apply empty_then_has_zero_elements;Auto with algebra.
Qed.

Lemma trivvecsp_has_dim_zero : (has_dim O (trivvecsp a F)).
Red.
Exists triv_basis.
Apply has_n_elements_comp with O (empty (trivvecsp a F));Auto with algebra.
Qed.
End basis.