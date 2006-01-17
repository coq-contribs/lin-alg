(** %\subsection*{ extras :  ring\_module.v }%*)
(** - How to build a module from a ring...*)
(* Later I found out that this is also done in Ideals.v from the *)
(* Algebra contribution... nonetheless, for your viewing pleasure: *)
Set Implicit Arguments.
Unset Strict Implicit.
Require Export Ring_facts.
Require Export equal_syntax.
Require Export more_syntax.
Require Export Endo_set.
Section ring_module.
Variable R : ring.




Let mult_map : forall r : R, MAP (ring_group R) (ring_group R).
intro.
simpl in |- *.
apply (Build_Map (Ap:=fun a : R => r rX a)).
red in |- *.
intros.
apply RING_comp; auto with algebra.
Defined.

Let ring_module_sgp_map :
  Map (Build_monoid (ring_monoid R)) (Endo_SET (ring_group R)).
simpl in |- *.
apply (Build_Map (Ap:=fun r : R => mult_map r)).
red in |- *.
intros.
simpl in |- *.
red in |- *.
intro z.
simpl in |- *.
apply RING_comp; auto with algebra.
Defined.

Let ring_module_sgp_hom :
  sgroup_hom (Build_monoid (ring_monoid R)) (Endo_SET (ring_group R)).
simpl in |- *.
apply (Build_sgroup_hom (sgroup_map:=ring_module_sgp_map)).
red in |- *.
intros.
simpl in |- *.
red in |- *.
intro r.
simpl in |- *.
unfold ring_mult in |- *.
change (x +' y +' r =' x +' (y +' r) in Build_sgroup (ring_mult_sgroup R))
 in |- *.
apply SGROUP_assoc.
Defined.
(* Something fishy-looking was going on due to syntax: *)
(* since we're working in an environment where the monoid-operation is *)
(* multiplication instead of addition, things look weird and garbled *)

Let ring_module_op : operation (Build_monoid (ring_monoid R)) (ring_group R).
simpl in |- *.
apply (Build_monoid_hom (monoid_sgroup_hom:=ring_module_sgp_hom)).
simpl in |- *.
red in |- *.
simpl in |- *.
red in |- *.
intro.
unfold mult_map in |- *.
simpl in |- *.
change (one rX x =' x in _) in |- *.
apply RING_unit_l.
Defined.
(* again. the zero of the ring-monoid is actually 1 *)

Definition Ring_module : module R.
apply (Build_module (R:=R) (module_carrier:=ring_group R)).
apply (Build_module_on (module_op:=ring_module_op)).
red in |- *.
intros.
simpl in |- *.
apply RING_dist_r.
red in |- *.
intros.
simpl in |- *.
apply RING_dist_l.
Defined.

End ring_module.