(** * lin_comb_facts.v *)
Set Implicit Arguments.
Require Export algebraic_span_facts.
Require Export seq_set_seq.

(** - Miscellaneous facts about linear combinations:

 - Suppose $x$ is a linear combination of $W$, and all $w\in W$ are linear combinations
 of $W'$, then $x$ is a linear combination of $W'$ *)

Lemma lin_comb_casting : (F:field;V:(vectorspace F);W,W':(part_set V);x:V)
  (is_lin_comb x W) -> ((w:W)(is_lin_comb (subtype_elt w) W')) -> (is_lin_comb x W').
Intros.
Change (in_part x (span W')).
Elim (span_idempotent W' x).
Intros.
(Apply H2;Auto with algebra);Clear H1 H2.
Simpl.
Assert (w:W)(in_part (subtype_elt w) (span_set W')).
Auto.
Clear H0.
Inversion_clear H.
Inversion_clear H0.
Inversion_clear H.
Red.
Exists x0.
Exists x1.
Assert (i:(fin x0))(in_part ((Map_embed x2) i) (span_set W')).
Intro i.
Change  (in_part (subtype_elt (x2 i)) (span_set W')).
Auto.
Exists (cast_map_to_subset H).
(Apply Trans with (sum (mult_by_scalars x1 (Map_embed x2)));Auto with algebra).
Qed.


(** - If all $w\in W$ are linear combinations of $W'$ then $span(W)\subset span(W')$ *)

Lemma span_casting : (F:field;V:(vectorspace F);W,W':(part_set V)) 
  ((w:W)(is_lin_comb (subtype_elt w) W')) -> (included (span W) (span W')).
Intros;Simpl.
Red;Simpl.
Intros.
(Apply lin_comb_casting with W;Auto with algebra).
Qed.

Lemma lin_comb_scalar_multiplied :
  (F:field;V:(vectorspace F);x:V;n:Nat;a:(seq n F);v:(seq n V);c:F)
    x='c mX (sum (mult_by_scalars a v)) -> (is_lin_comb x (seq_set v)).
Intros.
Red.
Exists n.
LetTac axc_fun:=[i:(fin n)]c rX (a i).
Assert axc_comp:(fun_compatible axc_fun).
Red.
Intros.
Unfold axc_fun.
(Apply RING_comp;Auto with algebra).
LetTac axc:=((Build_Map axc_comp)::(seq??)).
Exists axc.
Exists (seq_set_seq v).
Apply Trans with (sum (mult_by_scalars axc v)).
(Apply Trans with (c mX (sum (mult_by_scalars a v)));Auto with algebra).
(Apply Trans with (sum (mult_by_scalars (const_seq n c) (mult_by_scalars a v)));Auto with algebra).
(Apply sum_comp;Auto with algebra).
Simpl.
Red;Intros.
Unfold mult_by_scalars axc.
Simpl.
Unfold axc_fun.
Auto with algebra.
(Apply sum_comp;Auto with algebra).
Qed.

Lemma lin_comb_omit :
  (F:field;V:(vectorspace F);x:V;n:Nat;a:(seq n F);v:(seq n V);i:(fin n))
    x=' (sum (omit (mult_by_scalars a v) i)) -> (is_lin_comb x (seq_set v)).
Intros.
Red.
Exists n.
Exists (modify_seq a i (zero F)).
Exists (seq_set_seq v).
Apply Trans with (sum (mult_by_scalars (modify_seq a i (zero F)) v)).
2:(Apply sum_comp;Auto with algebra).
Apply Trans with (sum (modify_seq (mult_by_scalars a v) i ((zero F)mX(v i)))).
2:(Apply sum_comp;Auto with algebra).

(Apply Trans with (sum (mult_by_scalars a v))+'(min (mult_by_scalars a v i))+'((zero F)mX(v i));Auto with algebra).

(Apply Trans with ((sum (mult_by_scalars a v)) +' (min (mult_by_scalars a v i)))+'(zero V);Auto with algebra).
(Apply Trans with ((sum (mult_by_scalars a v)) +' (min (mult_by_scalars a v i)));Auto with algebra).
(Apply Trans with (sum (omit (mult_by_scalars a v) i));Auto with algebra).
Qed.