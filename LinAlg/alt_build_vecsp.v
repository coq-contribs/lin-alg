(** * alt_build_vecsp.v *)
Set Implicit Arguments.
Require Export vecspaces_verybasic.
Require Export Map2.


(** - It is very tedious to build up a vectorspace from scratch every time:
 One must build a setoid, then a semigroup, an abelian semigroup, a monoid,
 etc. etc. - hence this file: it provides a uniform way of building a
 vectorspace is one has proved the eight vectorspace axioms. *)

Section MAIN.
Variable V: Setoid.
Variable F: field.
Variable add: (Map2 V V V).
Variable mlt: (Map2 F V V).
Variable zer: V.
Variable mns: (Map V V).
Definition VS1:= (x,y:V)(add x y)='(add y x).
Definition VS2:= (x,y,z:V)(add (add x y) z)='(add x (add y z)).
Definition VS3:= (x:V) (add x zer)='x.
Definition VS4:= (x:V) (add x (mns x))='zer.
Definition VS5:= (x:V)(mlt one x)='x.
Definition VS6:= (a,b:F;x:V)(mlt (a rX b) x)='(mlt a (mlt b x)).
Definition VS7:= (a:F;x,y:V)(mlt a (add x y))='(add (mlt a x) (mlt a y)).
Definition VS8:= (a,b:F;x:V)(mlt (a+'b) x)='(add (mlt a x) (mlt b x)).

Local Vsg_on:VS2->(sgroup_on V).
Intro VS2p.
Apply (Build_sgroup_on 2!(Map2_Mapcart add)).
Red.
Intros.
Simpl.
Auto with algebra.
Defined.

Local Vsg:VS2->sgroup.
Intro VS2p.
Apply (Build_sgroup (Vsg_on VS2p)).
Defined.

Local Vmon_on:VS1->(VS2p:VS2)VS3->(monoid_on (Vsg VS2p)).
Intros VS1p VS2p VS3p.
Apply (Build_monoid_on 2!(zer::(Vsg VS2p))).
Red;Simpl.
Auto.
Red;Simpl;Intro.
(Apply Trans with (add x zer::(Vsg VS2p));Auto with algebra).
Defined.

Local Vmon:VS1->VS2->VS3->monoid.
Intros VS1p VS2p VS3p.
Apply (Build_monoid (Vmon_on  VS1p VS2p VS3p)).
Defined.

Local Vgp_on:(VS1p:VS1;VS2p:VS2;VS3p:VS3) VS4->(group_on (Vmon VS1p VS2p VS3p)).
Intros.
LetTac VMON := (Vmon VS1p VS2p VS3p).
Apply (Build_group_on 2!(mns::(Map VMON VMON))).
Red;Simpl.
Auto with algebra.
Red;Simpl.
Intro.
(Apply Trans with (add x (mns x));Auto with algebra).
Defined.

Local Vgp:VS1->VS2->VS3->VS4->group.
Intros VS1p VS2p VS3p VS4p.
Apply (Build_group (Vgp_on VS1p VS2p VS3p VS4p)).
Defined.

Local Vabgp_on:(VS1p:VS1;VS2p:VS2;VS3p:VS3;VS4p:VS4) (abelian_group_on (Vgp VS1p VS2p VS3p VS4p)).
Intros.
Apply Build_abelian_group_on.
Apply Build_abelian_monoid_on.
Apply Build_abelian_sgroup_on.
Red;Simpl.
Auto.
Defined.

Local Vabgp:VS1->VS2->VS3->VS4->abelian_group.
Intros VS1p VS2p VS3p VS4p.
Apply (Build_abelian_group (Vabgp_on VS1p VS2p VS3p VS4p)).
Defined.

Local F_act_map:(VS1p:VS1;VS2p:VS2;VS3p:VS3;VS4p:VS4)(Map (Build_monoid (ring_monoid F)) (Endo_SET (Vabgp VS1p VS2p VS3p VS4p))).
Intros VS1p VS2p VS3p VS4p.
Simpl.
Apply (Build_Map 3!([c:F](Ap2_Map mlt c))).
Red.
Intros;NewDestruct mlt;Simpl.
Red;Simpl.
Intro;Auto with algebra.
Defined.

Local F_sgp_hom:(VS1p:VS1;VS2p:VS2;VS3p:VS3;VS4p:VS4)VS6->(sgroup_hom (Build_monoid (ring_monoid F)) (Endo_SET (Vabgp VS1p VS2p VS3p VS4p))).
Intros VS1p VS2p VS3p VS4p VS6p.
Apply (Build_sgroup_hom 3!(F_act_map  VS1p VS2p VS3p VS4p)).
Red.
Intros;Simpl.
Red;Simpl.
Intro.
(Apply Trans with (mlt (x rX y) x0);Auto with algebra).
Defined.

Local F_op : (VS1p:VS1;VS2p:VS2;VS3p:VS3;VS4p:VS4)VS5->VS6->(operation (Build_monoid (ring_monoid F)) (Vabgp VS1p VS2p VS3p VS4p)).
Intros VS1p VS2p VS3p VS4p VS5p VS6p.
Apply (Build_monoid_hom 3!(F_sgp_hom VS1p VS2p VS3p VS4p VS6p)).
Red.
Simpl.
Red.
Intro;Simpl.
(Apply Trans with (mlt one x);Auto with algebra).
Defined.

Local Vmod_on:(VS1p:VS1;VS2p:VS2;VS3p:VS3;VS4p:VS4)VS5->VS6->VS7->VS8->(module_on F (Vabgp VS1p VS2p VS3p VS4p)).
Intros VS1p VS2p VS3p VS4p VS5p VS6p VS7p VS8p.
Apply (Build_module_on 3!(F_op  VS1p VS2p VS3p VS4p VS5p VS6p)).
Red;Simpl.
Auto with algebra.
Red.
Intros.
Simpl.
Red in VS7p.
(Apply Trans with (mlt a (add x y));Auto with algebra).
(Apply Trans with (add (mlt a x) (mlt a y));Auto with algebra).
Defined.

Definition alt_Build_vectorspace : VS1->VS2->VS3->VS4->VS5->VS6->VS7->VS8->(vectorspace F).
Intros VS1p VS2p VS3p VS4p VS5p VS6p VS7p VS8p.
Red.
Simpl.
Apply (Build_module (Vmod_on VS1p VS2p VS3p VS4p VS5p VS6p VS7p VS8p)).
Defined.

Definition vectorspace_construction : VS1->VS2->VS3->VS4->VS5->VS6->VS7->VS8->(sigT (vectorspace F) [VV:(vectorspace F)](Carrier VV)==V).
Intros.
Exists (alt_Build_vectorspace H H0 H1 H2 H3 H4 H5 H6).
Simpl.
Auto.
Defined.
End MAIN.
