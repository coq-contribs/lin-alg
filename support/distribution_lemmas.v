(** %\subsection*{ support :  distribution\_lemmas.v }%*)
Set Implicit Arguments.
Require Export mult_by_scalars.
Require Export const.
Require Export sums.

(** - $r\sum_i a_i = \sum_i ra_i$ (in rings),
 - $r\sum_i v_i = \sum_i rv_i$ (in modules) and 
 - $\sum_i r_i(r'_iv_i) = \sum_i (r_ir'_i)v_i$ *)

Lemma RING_sum_mult_dist_l : (R:ring;n:Nat;r:R;a:(seq n R))
  r rX (sum a) =' (sum (pointwise (uncurry (!RING_comp R)) (const_seq n r) a)).
Induction n.
Simpl.
Auto with algebra.
Intros.
((Apply Trans with r rX (sum (hdtl a)));Auto with algebra);Unfold hdtl.
(Apply Trans with r rX ((head a)+'(sum (Seqtl a)));Auto with algebra).
(Apply Trans with (r rX (head a)) +' (r rX (sum (Seqtl a)));Auto with algebra).
Apply Trans with (r rX (head a)) +' (sum (pointwise (uncurry (RING_comp 1!R)) (Seqtl (const_seq (S n0) r)) (Seqtl a))).
(Apply SGROUP_comp;Auto with algebra).
(Apply Trans with (sum (pointwise (uncurry (RING_comp 1!R)) (const_seq n0 r) (Seqtl a)));Auto with algebra).
Apply sum_comp.
Apply toMap.
(Apply pointwise_comp;Auto with algebra).
Apply Sym.
Change (Seqtl (const_seq (S n0) r))=' (const_seq (pred (S n0)) r).
Apply Seqtl_const_seq.
Apply Sym.
(Apply Trans with (sum (hdtl (pointwise (uncurry (RING_comp 1!R)) (const_seq (S n0) r) a)));Auto with algebra).
Unfold hdtl.
(Apply Trans with (head (pointwise (uncurry (RING_comp 1!R)) (const_seq (S n0) r) a)) +' (sum (pointwise (uncurry (RING_comp 1!R)) (Seqtl (const_seq (S n0) r)) (Seqtl a)));Auto with algebra).
(Apply Trans with (head (pointwise (uncurry (RING_comp 1!R)) (const_seq (S n0) r) a)) +' (sum (Seqtl (pointwise (uncurry (RING_comp 1!R)) (const_seq (S n0) r) a)));Auto with algebra).
Qed.

Lemma MODULE_sum_mult_dist_l : (R:ring;M:(module R);n:Nat;r:R;a:(seq n M))
  r mX (sum a) =' (sum (mult_by_scalars (const_seq n r) a)).
Induction n.
Simpl.
Auto with algebra.
Intros.
((Apply Trans with r mX (sum (hdtl a)));Auto with algebra);Unfold hdtl.
(Apply Trans with r mX ((head a)+'(sum (Seqtl a)));Auto with algebra).
(Apply Trans with (r mX (head a)) +' (r mX (sum (Seqtl a)));Auto with algebra).
Apply Trans with (r mX (head a)) +' (sum (mult_by_scalars (Seqtl (const_seq (S n0) r)) (Seqtl a))).
(Apply SGROUP_comp;Auto with algebra).
(Apply Trans with (sum (mult_by_scalars (const_seq n0 r) (Seqtl a)));Auto with algebra).
Apply sum_comp.
Apply toMap.
(Apply mult_by_scalars_comp;Auto with algebra).
Apply Sym.
Change (Seqtl (const_seq (S n0) r))=' (const_seq (pred (S n0)) r).
Apply Seqtl_const_seq.
(Apply Trans with (sum (hdtl (mult_by_scalars (const_seq (S n0) r) a)));Auto with algebra).
Unfold hdtl.
(Apply Trans with (head (mult_by_scalars (const_seq (S n0) r) a)) +' (sum (mult_by_scalars (Seqtl (const_seq (S n0) r)) (Seqtl a)));Auto with algebra).
(Apply Trans with (head (mult_by_scalars (const_seq (S n0) r) a)) +' (sum (Seqtl (mult_by_scalars (const_seq (S n0) r) a)));Auto with algebra).
Qed.

Hints Resolve RING_sum_mult_dist_l MODULE_sum_mult_dist_l : algebra.


Lemma pointwise_module_assoc:
  (R:ring;M:(module R); n:Nat; r,r':(seq n R); m:(seq n M))
    [rmult=(uncurry (RING_comp 1!R))]
      (mult_by_scalars r (mult_by_scalars r' m))
      =' (mult_by_scalars (pointwise rmult r r') m).
Intros.
Intro i;Simpl.
Auto with algebra.
Qed.

Hints Resolve pointwise_module_assoc : algebra.
