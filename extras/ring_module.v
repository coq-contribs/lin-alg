(** %\subsection*{ extras :  ring\_module.v }%*)
(** - How to build a module from a ring...*)
(* Later I found out that this is also done in Ideals.v from the *)
(* Algebra contribution... nonetheless, for your viewing pleasure: *)
Set Implicit Arguments.
Require Export Ring_facts.
Require Export equal_syntax.
Require Export more_syntax.
Require Export Endo_set.
Section ring_module.
Variable R:ring.




Local mult_map : (r:R)(MAP (ring_group R) (ring_group R)).
Intro.
Simpl.
Apply (Build_Map 3!([a:R](ring_mult r a))).
Red.
Intros.
(Apply RING_comp;Auto with algebra).
Defined.

Local ring_module_sgp_map : (Map (Build_monoid (ring_monoid R)) (Endo_SET(ring_group R))).
Simpl.
Apply (Build_Map 3![r:R](mult_map r)).
Red.
Intros.
Simpl.
Red.
Intro z.
Simpl.
(Apply RING_comp;Auto with algebra).
Defined.

Local ring_module_sgp_hom : (sgroup_hom (Build_monoid (ring_monoid R)) (Endo_SET(ring_group R))).
Simpl.
Apply (Build_sgroup_hom 3!ring_module_sgp_map).
Red.
Intros.
Simpl.
Red.
Intro r.
Simpl.
Unfold ring_mult.
Change  (x+'y)+'r =' x+'(y+'r) in (Build_sgroup (ring_mult_sgroup (R))).
Apply SGROUP_assoc.
Defined.
(* Something fishy-looking was going on due to syntax: *)
(* since we're working in an environment where the monoid-operation is *)
(* multiplication instead of addition, things look weird and garbled *)

Local ring_module_op : (operation (Build_monoid (ring_monoid R)) (ring_group R)).
Simpl.
Apply (Build_monoid_hom 3!ring_module_sgp_hom).
Simpl.
Red.
Simpl.
Red.
Intro.
Unfold mult_map.
Simpl.
Change ((one rX x) =' x).
Apply RING_unit_l.
Defined.
(* again. the zero of the ring-monoid is actually 1 *)

Definition Ring_module : (module R).
Apply (!Build_module R (ring_group R)).
Apply (Build_module_on 3!ring_module_op).
Red.
Intros.
Simpl.
Apply RING_dist_r.
Red.
Intros.
Simpl.
Apply RING_dist_l.
Defined.

End ring_module.
