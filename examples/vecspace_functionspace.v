(** %\subsection*{ examples :  vecspace\_functionspace.v }%*)
(** - Another vectorspace, defined old-fashionedly. Fortunately, given vecspace_Fn, 
 this file is hardly more than cut-n-paste *)
Set Implicit Arguments.
Require Export vecspaces_verybasic.
Require Export Map2.

Section Function_spaces.

Definition func_set := [A,B:Setoid](MAP A B).

Local func_plus_fun : (A:Setoid; B:sgroup)
 (func_set A B)->(func_set A B)->(func_set A B).
Intros A B f g.
Simpl.
Simpl in f.
Simpl in g.
Apply (!Build_Map A B [a:A]((Ap f a)+'(Ap g a))).
Red.
Intros a a' Ha.
(Apply SGROUP_comp;Auto with algebra).
Defined.

Definition func_plus : (A:Setoid; B:sgroup)
  (law_of_composition (func_set A B)).
Intros.
Simpl.
Apply Map2_Mapcart.
Apply (Build_Map2 4!(!func_plus_fun A B)).
Red.
Intros f f' g g' Hf Hg.
Unfold func_plus_fun.
Simpl.
Red.
Intro a.
Simpl.
(Apply SGROUP_comp;Auto with algebra).
Defined.

Lemma func_plus_associative : (A:Setoid;B:sgroup)
  (associative (!func_plus A B)).
Intros.
Red.
Intros f g h.
Unfold func_plus.
Simpl.
Red.
Intro a.
Unfold func_plus_fun.
Simpl.
Apply SGROUP_assoc.
Qed.

Definition func_sgroup [A:Setoid;B:sgroup] : SGROUP
  := (Build_sgroup (Build_sgroup_on (!func_plus_associative A B))).

Lemma func_plus_commutative : (A:Setoid;B:abelian_sgroup)
  (commutative (func_plus A B)).
Intros.
Red.
Intros f f'.
Unfold func_plus.
Simpl.
Red.
Intro a.
Unfold func_plus_fun.
Simpl.
Apply ABELIAN_SGROUP_com.
Qed.

Definition func_absgp [A:Setoid;B:abelian_sgroup] : ABELIAN_SGROUP := (Build_abelian_sgroup (!Build_abelian_sgroup_on (func_sgroup A B) (!func_plus_commutative A B))).

Definition func_zerofun : (A:Setoid;B:monoid)(func_set A B).
Intros.
Apply (Build_Map 3!([a:A](zero B))).
Red.
Intros.
Apply Refl.
Defined.

Lemma func_zerofun_is_r_unit : (A:Setoid;B:monoid)
  (unit_r (sgroup_law_map (func_sgroup A B)) (func_zerofun A B)).
Intros A B.
Red.
Intro.
Simpl.
Red.
Intro i.
Simpl.
Apply MONOID_unit_r.
Qed.

Lemma func_zerofun_is_l_unit : (A:Setoid;B:monoid)
  (unit_l (sgroup_law_map (func_sgroup A B)) (func_zerofun A B)).
Intros A B.
Red.
Intro.
Simpl.
Red.
Intro i.
Simpl.
Apply MONOID_unit_l.
Qed.

Definition func_monoid [A:Setoid;B:monoid] : MONOID := (Build_monoid (!Build_monoid_on (func_sgroup A B) (!func_zerofun A B) (!func_zerofun_is_r_unit A B) (!func_zerofun_is_l_unit A B))).

Lemma func_monoid_is_abelian : (A:Setoid;B:abelian_monoid)
  (abelian_monoid_on (func_monoid A B)).
Intros.
Apply Build_abelian_monoid_on.
Apply Build_abelian_sgroup_on.
Exact (!func_plus_commutative A B).
Qed.

Definition func_abmon [A:Setoid;B:abelian_monoid]: ABELIAN_MONOID
  := (Build_abelian_monoid (func_monoid_is_abelian A B)).

Local func_inv_fun : (A:Setoid;B:group)(func_monoid A B) -> (func_monoid A B).
Intros A B.
Simpl.
Intro v.
Apply (Build_Map 3!([i:A](min (v i)))).
Red.
Intros i i' H.
(Apply GROUP_comp;Auto with algebra).
Defined.

Definition func_inv : (A:Setoid;B:group)(Map (func_monoid A B) (func_monoid A B)).
Intros.
Apply (Build_Map 3!(!func_inv_fun A B)).
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

Lemma func_inv_is_r_inverse: (A:Setoid;B:group)
  (inverse_r (func_plus A B) (func_zerofun A B) (func_inv A B)).
Intros.
Red.
Intro.
Simpl.
Red.
Intro i.
Simpl.
Auto with algebra.
Qed.

Lemma func_inv_is_l_inverse: (A:Setoid;B:group)
  (inverse_l (func_plus A B) (func_zerofun A B) (func_inv A B)).
Intros.
Red.
Intro.
Simpl.
Red.
Intro i.
Simpl.
Auto with algebra.
Qed.

Definition func_group [A:Setoid;B:group]: GROUP := (Build_group (Build_group_on 2!(func_inv A B) (!func_inv_is_r_inverse A B) (!func_inv_is_l_inverse A B))).

Lemma func_group_is_abelian : (A:Setoid;B:abelian_group)
  (abelian_group_on (func_group A B)).
Intros.
Apply Build_abelian_group_on.
Apply Build_abelian_monoid_on.
Apply Build_abelian_sgroup_on.
Exact (!func_plus_commutative A B).
Qed.

Definition func_abgp[A:Setoid;B:abelian_group]:ABELIAN_GROUP
  := (Build_abelian_group (func_group_is_abelian A B)).

Definition func_scmult_fun : (A:Setoid;B:ring)B->(func_set A B)->(func_set A B).
Simpl.
Intros A B c v.
Apply (Build_Map 3!([i:A]c rX (v i))).
Red.
Auto with algebra.
Defined.

Lemma func_scmult_fun_comp : (A:Setoid;B:ring)(c,c':B;v,v':(func_set A B))
  c='c' -> v='v' -> (func_scmult_fun c v)='(func_scmult_fun c' v').
Intros A B.
Simpl.
Intros.
Red.
Intro i.
Simpl.
(Apply RING_comp;Auto with algebra).
Qed.

Section necessary_module_stuff.

Local func_scmult_fun_map : (A:Setoid;B:ring)
  B->(MAP (func_set A B) (func_set A B)).
Intros A B c.
Apply (Build_Map 3!([v:(func_set A B)](func_scmult_fun c v))).
Red.
Intros v v' H.
(Apply func_scmult_fun_comp;Auto with algebra).
Defined.

Local func_scmult_F_to_EndoSet : (A:Setoid;B:ring)
  (Map (Build_monoid (ring_monoid B)) (Endo_SET (func_set A B))).
Intros A B.
Simpl.
Apply (Build_Map 3!([c:B](func_scmult_fun_map A 2!B c))).
Red.
Intros c c' H.
Simpl.
Red.
Intro v.
Generalize (!func_scmult_fun_comp A B c c' v v H).
Simpl.
Generalize (Refl v).
Intros.
Simpl in H0.
(Apply H1;Auto with algebra).
Defined.

Local func_scmult_sgroup_hom : (A:Setoid;B:ring)
  (sgroup_hom (Build_monoid (ring_monoid B)) (Endo_SET (func_set A B))).
Intros.
Apply (Build_sgroup_hom 3!(func_scmult_F_to_EndoSet A B)).
Red.
Simpl.
Red.
Intros c c' v.
Simpl.
Red.
Intro i.
Simpl.
(Apply Trans with (c rX c') rX (v i);Auto with algebra).
Defined.

Local func_scmult_monoid_hom : (A:Setoid;B:ring)
  (monoid_hom (Build_monoid (ring_monoid B)) (Endo_SET (func_set A B))).
Intros A B.
Apply (Build_monoid_hom 3!(func_scmult_sgroup_hom A B)).
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

Definition func_scmult : (A:Setoid;B:ring)
  (operation (Build_monoid (ring_monoid B)) (func_group A B)).
Simpl.
Intros.
Exact (func_scmult_monoid_hom A B).
Defined.

End necessary_module_stuff.

Lemma func_scmult_l_lin : (A:Setoid;B:ring)
  (op_lin_left 2!(func_abgp A B) (func_scmult A B)).
Red.
Intros c c' v.
Simpl.
Red.
Intro i.
Simpl.
Intros.
Apply RING_dist_r.
Qed.

Lemma func_scmult_r_lin : (A:Setoid;B:ring)
  (op_lin_right 2!(func_abgp A B) (func_scmult A B)).
Intros A B.
Red.
Intros c c' v.
Simpl.
Red.
Intro i.
Simpl.
Apply RING_dist_l.
Qed.

Definition func_mod : (A:Setoid;B:ring)(MODULE B) := [A:Setoid;B:ring](Build_module (Build_module_on (!func_scmult_l_lin A B) (!func_scmult_r_lin A B))).

Definition func : (A:Setoid;B:field)(VECSP B)
  := [A:Setoid;B:field]((func_mod A B)::(vectorspace B)).

End Function_spaces.
