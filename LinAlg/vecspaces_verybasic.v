(** * vecspaces_verybasic.v *)
Section MAIN.
Set Implicit Arguments.
Require Export Field_facts.
Require Export equal_syntax.
Require Export more_syntax.
Require Export Module_facts.

(** - The definition of a vectorspace, and some very easy lemma's.
 This file is basically the book's Section 1.2 *)

Section vecfielddef.

(** %\tocdef{vectorspace}% *)
Definition vectorspace [F:field] : Type := (MODULE F).
Definition VECSP [F:field] : category 
  := (full_subcat [V:(vectorspace F)](V::(MODULE F))).

End vecfielddef.


Section jargon.
Variable F:field.
Variable V:(vectorspace F).
Definition carrier := module_carrier.
Definition scalar_mult : F->V->V 
  := [a:F;x:V] a mX x.
(** - Since scalar_mult is exactly the same as module_mult, ie mX, we will continue 
 to use that notation instead *)
Definition scalar_mult_comp : (x, x' : F) (y, y' : (carrier V))
  x =' x' -> y =' y' -> x mX y =' x' mX y'
  := (MODULE_comp 1!F 2!V).
Definition one_acts_as_unit : (x : (carrier V))  one mX x =' x
  := (MODULE_unit_l 1!F 2!V).
Definition quasi_associativity: (a, b : F) (x : (carrier V)) 
  (a rX b) mX x =' a mX (b mX x)
  := (MODULE_assoc 1!F 2!V).
Definition distributivity: (a : F) (x, y : (carrier V))  
  a mX (x +' y) =' (a mX x) +' (a mX y)
  := (MODULE_dist_l 1!F 2!V).
Definition distributivity': (a, b : F) (x : (carrier V)) 
  (a +' b) mX x =' (a mX x) +' (b mX x)
  := (MODULE_dist_r 1!F 2!V).
End jargon.



(* The following will be assumed throughout this file. These are defined
   outside all sections but the global one, lest we need state them 10 times *)
Variable F:field.
Variable V:(vectorspace F).
Hints Unfold carrier module_carrier.
Hints Resolve scalar_mult_comp distributivity distributivity' : algebra.



Section Lemmas1.
(** - %\intoc{\bf Proposition 1.1}%;
    the corollaries are immediate by construction/definition *)
Lemma vector_cancellation: (x, y, z : V) x +' z =' y +' z -> x =' y.
Intros.
(Apply GROUP_reg_right with z;Auto with algebra).
Qed.

(** - %\intoc{\bf Proposition 1.2}%, split into several separate lemmas *)
Lemma Zero_times_a_vector_gives_zero: (v : V)  (zero F) mX v =' (zero V).
Auto with algebra.
Qed.

Lemma a_scalar_times_zero_gives_zero: (f : F)  f mX (zero V) =' (zero V).
Auto with algebra.
Qed.
 
Section Lemmas1_2.

Lemma Mince_minus1: (f : F) (v : V)  (min f) mX v =' (min (f mX v)).
Auto with algebra.
Qed.
 
Lemma Mince_minus2: (f : F) (v : V)  (min (f mX v)) =' f mX (min v).
Auto with algebra.
Qed.
 
Lemma Mince_minus3: (f : F) (v : V) (min f) mX v =' f mX (min v).
Intros.
(Apply Trans with (min (f mX v));Auto with algebra).
Qed.

Lemma vecspace_op_reg_l : (f:F)(v:V) 
  ~f='(zero F)-> f mX v =' (zero V) -> v='(zero V).
Intros.
(Apply Trans with one mX v;Auto with algebra).
Apply Trans with ((field_inverse f)rX f) mX v.
(Apply MODULE_comp;Auto with algebra).
(Apply Sym;Auto with algebra).
(Apply Trans with (field_inverse f) mX (f mX v);Auto with algebra).
(Apply Trans with (field_inverse f) mX (zero V);Auto with algebra).
Qed.


End Lemmas1_2.
End Lemmas1.

End MAIN.

Hints Resolve vector_cancellation Zero_times_a_vector_gives_zero a_scalar_times_zero_gives_zero Mince_minus1 Mince_minus2 Mince_minus3 : algebra.
