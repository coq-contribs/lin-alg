(** %\subsection*{ support :  Map2.v }%*)
(** This file introduces [Map2] which is to [A->B->C] like [Map] is to [A->B]
 Similarly a setoid [MAP2] is introduced and we have tools for (un)currying 
 and using / filling in arguments. This is not linear algebra-specific and 
 could all have been done inside the  algebra contribution; it just facilitates
 using fuctions of two arguments *)

Set Implicit Arguments.
Require Export equal_syntax.
Require Export Cartesian.

(* We have setoid-compatible functions called "Map" *)

(* These are 1-ary functions; more general n-ary functions are defined by *)
(* (un)currying, (repeatedly) using (cart A B), the cartesian product *)
(* setoid construction. Still, it's nicer to have a more direct way of *)
(* dealing with 2-ary functions because these occur relatively often. *)

(* I call these "Map2" - and here I provide also tools to jump between *)
(* the two representations. *)

(** %\label{Map2}% *)
Record Map2 [A,B,C:Setoid] : Type :=
 {Ap2 :> A->B->C ;
  Ap2_comp_proof : (fun2_compatible Ap2)}.


Definition Map2_Mapcart : (A,B,C:Setoid)(Map2 A B C)->(Map (cart A B) C).
Intros.
Apply (Build_Map 3!([ab:(cart A B)](X (proj1 ab) (proj2 ab)))).
Red.
Intros.
Elim X.
Intros.
Red in Ap2_comp_proof0.
Simpl.
(Apply Ap2_comp_proof0;Auto with algebra).
Defined.

Definition Mapcart_Map2 : (A,B,C:Setoid)(Map (cart A B) C)->(Map2 A B C).
Intros.
Apply (Build_Map2 4!([a:A;b:B](X (couple a b)))).
Red.
Intros.
(Apply Ap_comp;Auto with algebra).
Defined.


(* The setoid of 2-ary functions *)
Definition MAP2 [A,B,C:Setoid] : Setoid.
Intros.
Apply (Build_Setoid 2![f,g:(Map2 A B C)](a,a':A;b,b':B)a='a'->b='b'->(f a b)='(g a' b')).
Split;Try Split;Red;Unfold app_rel.
Intros;NewDestruct x.
Simpl.
(Apply Ap2_comp_proof0;Auto with algebra).
Intros.
(Apply Trans with (y a b);Auto with algebra).
Intros.
(Apply Sym;Auto with algebra).
Defined.


(* Tools for filling in first and second arguments. *)
Definition Map2_ap_Map : (A,B,C:Setoid)(Map2 A B C)->A->(MAP B C).
Intros.
Apply (Build_Map 3!(X X0)).
NewDestruct X;Red;Simpl.
Intros.
(Apply Ap2_comp_proof0;Auto with algebra).
Defined.

Definition Ap2_Map : (A,B,C:Setoid)(Map2 A B C)->(Map A (MAP B C)).
Intros.
Apply (Build_Map 3![a](Map2_ap_Map X a)).
Red.
Intros;Simpl.
Red;Simpl.
Intros;NewDestruct X.
Simpl.
(Apply Ap2_comp_proof0;Auto with algebra).
Defined.

Definition Map2_ap'_Map : (A,B,C:Setoid)(Map2 A B C)->B->(MAP A C).
Intros.
Apply (Build_Map 3![a](X a X0)).
NewDestruct X;Red;Simpl.
Intros.
(Apply Ap2_comp_proof0;Auto with algebra).
Defined.

Definition Ap2_Map' : (A,B,C:Setoid)(Map2 A B C)->(Map B (MAP A C)).
Intros.
Apply (Build_Map 3![b](Map2_ap'_Map X b)).
Red.
Intros;Simpl.
Red;Simpl.
Intros;NewDestruct X.
Simpl.
(Apply Ap2_comp_proof0;Auto with algebra).
Defined.