(** %\subsection*{ examples :  vecspace\_Fn.v }%*)
(** - In this file I define the vectorspaces $F^n$ (for arbitrary fields $F$); 
 this is done without using the 'tool' alt_build_vecspace, just to 
 show the tediousness of having to build all successive structures from the
 algebraic hierarchy by hand *)
Section Fn_vectors.

Set Implicit Arguments.
Require Export vecspaces_verybasic.
Require Export finite.

(**************************************)
(* In the beginning there was the set *)
(**************************************)

Definition Fn_set [F:Setoid;n:Nat] :SET := (seq n F).

(******************************************)
(* And Coq said, "let there be an sgroup" *)
(******************************************)

Local Fn_plus_fun : (F:sgroup;n:Nat)(Fn_set F n)->(Fn_set F n)->(Fn_set F n).
Intros F n x y.
Simpl.
Apply (Build_Map 3!([i:(fin n)](x i)+'(y i))).
Red.
Elim x.
Elim y.
Intros.
Red in Map_compatible_prf.
Red in Map_compatible_prf0.
(Apply SGROUP_comp;Auto with algebra).
Defined.

Definition Fn_plus : (F:sgroup;n:Nat)(law_of_composition (Fn_set F n)).
Intros F n.
Apply (uncurry 4!(!Fn_plus_fun F n)).
Red.
Simpl.
Intros.
Red.
Intro i.
Simpl.
(Apply SGROUP_comp;Auto with algebra).
Defined.

Lemma Fn_plus_associative : (F:sgroup;n:Nat)(associative (Fn_plus F n)).
Red.
Intros.
Simpl.
Red.
Intro i.
Simpl.
Apply SGROUP_assoc.
Qed.

Definition Fn_sgroup [F:sgroup;n:Nat] : SGROUP
  := (Build_sgroup (Build_sgroup_on (!Fn_plus_associative F n))).

(*****************************************************)
(* And there was an sgroup, and Abel saw it was good *)
(*****************************************************)

Lemma Fn_plus_commutative : (F:abelian_sgroup;n:Nat)(commutative (Fn_plus F n)).
Red.
Intros.
Simpl.
Red.
Intro i.
Simpl.
Auto with algebra.
Qed.

Definition Fn_absgp [F:abelian_sgroup;n:Nat]: ABELIAN_SGROUP := (Build_abelian_sgroup (Build_abelian_sgroup_on 1!(Fn_sgroup F n) (!Fn_plus_commutative F n))).

(******************************************************)
(* It is a monoid, Jim, but... exactly as we know it. *)
(******************************************************)

Definition Fn_zero : (F:monoid;n:Nat) (Fn_sgroup F n).
Intros F n.
Apply (Build_Map 3![i:(fin n)](zero F)).
Red.
Intros.
Apply Refl.
Defined.

Lemma Fn_zero_is_r_unit : (F:monoid;n:Nat)
  (unit_r (sgroup_law_map (Fn_sgroup F n)) (Fn_zero F n)).
Intros F n.
Red.
Intro.
Simpl.
Red.
Intro i.
Simpl.
Apply MONOID_unit_r.
Qed.

Lemma Fn_zero_is_l_unit :  (F:monoid;n:Nat)
  (unit_l (sgroup_law_map (Fn_sgroup F n)) (Fn_zero F n)).
Intros F n.
Red.
Intro.
Simpl.
Red.
Intro i.
Simpl.
Apply MONOID_unit_l.
Qed.

Definition Fn_monoid [F:monoid;n:Nat]: MONOID := (Build_monoid (!Build_monoid_on (Fn_sgroup F n) (Fn_zero F n) (!Fn_zero_is_r_unit F n) (!Fn_zero_is_l_unit F n))).

(*********************************)
(* And Abel saw that it was good *)
(*********************************)

Lemma Fn_monoid_is_abelian : (F:abelian_monoid;n:Nat)
  (abelian_monoid_on (Fn_monoid F n)).
Intros F n.
Apply Build_abelian_monoid_on.
Apply Build_abelian_sgroup_on.
Exact (!Fn_plus_commutative F n).
Qed.

Definition Fn_abmon [F:abelian_monoid;n:Nat]: ABELIAN_MONOID := 
  (Build_abelian_monoid (Fn_monoid_is_abelian F n)).

(***********************************)
(* What's in a name? That which we *)
(* call a group by any other word  *)
(* would smell as sweet.           *)
(***********************************)


Local Fn_inv_fun : (F:group;n:Nat)(Fn_monoid F n) -> (Fn_monoid F n).
Simpl.
Intros F n v.
Apply (Build_Map 3!([i:(fin n)](group_inverse F (v i)))).
Red.
Intros i i' H.
(Apply GROUP_comp;Auto with algebra).
Defined.

Definition Fn_inv : (F:group;n:Nat) (Map (Fn_monoid F n) (Fn_monoid F n)).
Intros F n.
Apply (Build_Map 3!(!Fn_inv_fun F n)).
Red.
Intros.
Simpl.
Red.
Intro i.
Simpl in H.
Red in H.
Simpl.
(Apply GROUP_comp;Auto with algebra).
Defined.

Lemma Fn_inv_is_r_inverse: (F:group;n:Nat)
  (inverse_r (Fn_plus F n) (Fn_zero F n) (Fn_inv F n)).
Intros F n.
Red.
Intro.
Simpl.
Red.
Intro i.
Simpl.
Auto with algebra.
Qed.

Lemma Fn_inv_is_l_inverse: (F:group;n:Nat)
  (inverse_l (Fn_plus F n) (Fn_zero F n) (Fn_inv F n)).
Intros F n.
Red.
Intro.
Simpl.
Red.
Intro i.
Simpl.
Auto with algebra.
Qed.

Definition Fn_group [F:group;n:Nat] : GROUP := (Build_group (Build_group_on 2!(Fn_inv F n) (!Fn_inv_is_r_inverse F n) (!Fn_inv_is_l_inverse F n))).

(****************************)
(* Once more, Abel spoke... *)
(****************************)

Lemma Fn_group_is_abelian : (F:abelian_group;n:Nat) (abelian_group_on (Fn_group F n)).
Intros.
Apply Build_abelian_group_on.
Apply Build_abelian_monoid_on.
Apply Build_abelian_sgroup_on.
Exact (!Fn_plus_commutative F n).
Qed.

Definition Fn_abgp [F:abelian_group;n:Nat] :ABELIAN_GROUP
  := (Build_abelian_group (Fn_group_is_abelian F n)).

(*******************************)
(* Alle modulen werden brueder *)
(*******************************)

Definition Fn_scmult_fun : (F:ring;n:Nat) F->(Fn_set F n)->(Fn_set F n).
Simpl.
Intros F n c v.
Apply (Build_Map 3!([i:(fin n)]c rX (v i))).
Red.
Auto with algebra.
Defined.

Lemma Fn_scmult_fun_comp : (F:ring;n:Nat)(c,c':F;v,v':(Fn_set F n))
  c='c' -> v='v' -> (Fn_scmult_fun c v)='(Fn_scmult_fun c' v').
Simpl.
Intros.
Red.
Intro i.
Simpl.
(Apply RING_comp;Auto with algebra).
Qed.

(********************************)
(* But that takes quite a while *)
(********************************)

Section necessary_module_stuff.

Local Fn_scmult_fun_map : (F:ring;n:Nat)F->(MAP (Fn_set F n) (Fn_set F n)).
Intros F n c.
Apply (Build_Map 3!([v:(Fn_set F n)](Fn_scmult_fun c v))).
Red.
Intros v v' H.
(Apply Fn_scmult_fun_comp;Auto with algebra).
Defined.

Local Fn_scmult_F_to_EndoSet : (F:ring;n:Nat)
  (Map (Build_monoid (ring_monoid F)) (Endo_SET (Fn_set F n))).
Intros F n.
Simpl.
Apply (Build_Map 3!([c:F](!Fn_scmult_fun_map F n c))).
Red.
Intros c c' H.
Simpl.
Red.
Intro v.
Generalize (!Fn_scmult_fun_comp F n c c' v v H).
Simpl.
Generalize (Refl v).
Auto.
Defined.

Local Fn_scmult_sgroup_hom : (F:ring;n:Nat)
  (sgroup_hom (Build_monoid (ring_monoid F)) (Endo_SET (Fn_set F n))).
Intros F n.
Apply (Build_sgroup_hom 3!(!Fn_scmult_F_to_EndoSet F n)).
Red.
Simpl.
Red.
Intros c c' v.
Simpl.
Red.
Intro i.
Simpl.
(Apply Trans with (ring_mult (ring_mult c c') (Ap v i));Auto with algebra).
Defined.

Local Fn_scmult_monoid_hom : (F:ring;n:Nat)
  (monoid_hom (Build_monoid (ring_monoid F)) (Endo_SET (Fn_set F n))).
Intros.
Apply (Build_monoid_hom 3!(!Fn_scmult_sgroup_hom F n)).
Red.
Simpl.
Red.
Intro v.
Simpl.
Red.
Intro i.
Simpl.
(Apply Trans with one rX (v i);Auto with algebra).
Defined.

Definition Fn_scmult : (F:ring;n:Nat)
  (operation (Build_monoid (ring_monoid F)) (Fn_abgp F n)).
Intros.
Simpl.
Exact (Fn_scmult_monoid_hom F n).
Defined.

End necessary_module_stuff.

Lemma Fn_scmult_l_lin : (F:ring;n:Nat)(op_lin_left (Fn_scmult F n)).
Red.
Intros F n c c' v.
Simpl.
Red.
Intro i.
Simpl.
Apply RING_dist_r.
Qed.

Lemma Fn_scmult_r_lin : (F:ring;n:Nat)(op_lin_right (Fn_scmult F n)).
Intros F n.
Red.
Intros c c' v.
Simpl.
Red.
Intro i.
Simpl.
Apply RING_dist_l.
Qed.

Definition Fn_mod [F:ring;n:Nat]: (MODULE F)
   := (Build_module (Build_module_on (!Fn_scmult_l_lin F n) (!Fn_scmult_r_lin F n))).

Definition Fn [F:field;n:Nat] : (VECSP F)
  := ((Fn_mod F n)::(vectorspace F)).

End Fn_vectors.


(** - Defining the standard basis vectors needs a generalised Kronecker since
 0 and 1 from [nat] cannot be used in $F$ *)
Section Basis_vectors.

Fixpoint Kronecker [A:Setoid;t,f:A;n,m:Nat]:A :=
Cases n m of 
  O O => t 
| (S n') O => f 
| O (S m') => f 
| (S n') (S m') => (Kronecker t f n' m') 
end.

Lemma Kronecker_case_equal : (A:Setoid;t,f:A;n,m:Nat)n='m->(Kronecker t f n m)='t.
NewInduction n;NewInduction m;Auto with algebra;Intros.
Inversion_clear H.
Inversion_clear H.
Simpl.
(Apply IHn;Auto with algebra).
Simpl;Simpl in H;Auto with arith.
Qed.

Lemma Kronecker_case_unequal : (A:Setoid;t,f:A;n,m:Nat)~n='m->(Kronecker t f n m)='f.
Intros until n.
NewInduction n.
NewInduction m;Auto with algebra.
Intros;Absurd O=O;Auto.
Intros.
NewInduction m;Auto with algebra.
Simpl.
(Apply IHn;Auto with algebra).
Intro p;Red in H;Apply H;Simpl in p;Simpl;Auto with arith.
Qed.

Definition Basisvec_Fn : (F:field;n,i:Nat;H:(lt i n))((Fn F n)::Type).
Intros.
Simpl.
Apply (Build_Map 3!([j:(fin n)]Cases j of (Build_finiteT j' _) => (Kronecker one (zero F) i j') end)).
Red.
Intros x y.
Elim x.
Elim y.
Simpl.
Intros.
Rewrite H0.
Apply Refl.
Defined.
End Basis_vectors.