(** * Lin_trafos.v *)
Set Implicit Arguments.
Require Export mult_by_scalars.
Require Export sums.

(** - Linear transformations (very initial stuff only) *)

Variable F:field.
Variable V,W:(vectorspace F).

Record lin_trafo_on [T:(Map V W)] : Type :=
{ preserve_plus : (x,y:V)(T x+'y)='(T x)+'(T y)
; preserve_mX : (c:F;x:V)(T c mX x)='c mX (T x)}.

(** %\tocdef{lin\_trafo}% *)
Record lin_trafo : Type :=
{ lin_trafo_map :> (Map V W)
; lin_trafo_on_def : (lin_trafo_on lin_trafo_map)}.

Fact zerovec_preserving : (T:lin_trafo)(T (zero V))='(zero W).
Intro.
NewDestruct T.
Rename lin_trafo_map0 into T.
NewDestruct lin_trafo_on_def0.
Simpl.
(Apply Trans with (T (zero V)+'(min(zero V)));Auto with algebra).
(Apply Trans with (T (zero V))+'(T (min(zero V)));Auto with algebra).
(Apply Trans with (T (zero V))+'(min(T (zero V)));Auto with algebra).
(Apply SGROUP_comp;Auto with algebra).
(Apply Trans with (T (min (one mX(zero V))));Auto with algebra).
(Apply Trans with (T (min one) mX(zero V));Auto with algebra).
(Apply Trans with (min (one mX (T (zero V))));Auto with algebra).
(Apply Trans with (min one) mX (T (zero V));Auto with algebra).
Qed.

Hints Resolve zerovec_preserving : algebra.

Fact lin_trafo_equation: (T:(Map V W)) (lin_trafo_on T)
  -> (a:F;x,y:V)(T (a mX x)+'y)='(a mX (T x))+'(T y).
Intros.
NewDestruct X.
(Apply Trans with (T (a mX x))+'(T y);Auto with algebra).
Qed.

Hints Resolve lin_trafo_equation : algebra.

Fact lin_trafo_equation': (T:(Map V W))
  ((a:F;x,y:V)(T (a mX x)+'y)='(a mX (T x))+'(T y))
    -> (lin_trafo_on T).
Intros.
Constructor.
Intros.
(Apply Trans with (one mX (T x))+'(T y);Auto with algebra).
(Apply Trans with (T (one mX x) +' y);Auto with algebra).
Intros.
(Apply Trans with (c mX (T x))+'(zero W);Auto with algebra).
(Apply Trans with (c mX (T x))+'(T (zero V));Auto with algebra).
(Apply Trans with (T (c mX x)+'(zero V));Auto with algebra).
(Apply SGROUP_comp;Auto with algebra).
(Apply Trans with (T ((min one)mX(zero V))+'(zero V));Auto with algebra).
(Apply Ap_comp;Auto with algebra).
(Apply Trans with ((min (one mX (zero V)))+'(zero V));Auto with algebra).
(Apply Trans with (min (zero V))+'(zero V);Auto with algebra).
(Apply Trans with (min one) mX (T (zero V)) +' (T (zero V));Auto with algebra).
(Apply Trans with (min (one mX (T (zero V)))) +' (T (zero V));Auto with algebra).
(Apply Trans with (min (T (zero V))) +' (T (zero V));Auto with algebra).
Qed.

Hints Resolve lin_trafo_equation' : algebra.

Fact lin_trafo_of_lin_comb:
  (T:(Map V W)) (lin_trafo_on T) -> (n:Nat;a:(seq n F);v:(seq n V))
    (T (sum (mult_by_scalars a v)))='(sum (mult_by_scalars a (comp_map_map T v))).
Intros.
NewInduction n.
Simpl.
(Apply Trans with (Build_lin_trafo X (zero V));Auto with algebra).
Apply Trans with (T (sum (mult_by_scalars (hdtl a) (hdtl v)))).
(Apply Ap_comp;Auto with algebra).
Apply Trans with (T (sum (head a)mX(head v);;(mult_by_scalars (Seqtl a) (Seqtl v)))).
Unfold hdtl.
(Apply Ap_comp;Auto with algebra).
(Apply Trans with (T ((head a)mX(head v))+'(sum (mult_by_scalars (Seqtl a) (Seqtl v))));Auto with algebra).
NewDestruct X.
(Apply Trans with (T ((head a)mX(head v)))+'(T (sum (mult_by_scalars (Seqtl a) (Seqtl v))));Auto with algebra).
(Apply Trans with (sum (mult_by_scalars (hdtl a) (hdtl (comp_map_map T v))));Auto with algebra).
Unfold hdtl.
Apply Trans with (sum ((uncurry (MODULE_comp 1!F 2!W)) (couple (head a) (head (comp_map_map T v))));;(pointwise (uncurry (MODULE_comp 1!F 2!W)) (Seqtl a) (Seqtl (comp_map_map T v)))).
(Apply Trans with (head a)mX(head (comp_map_map T v)) +' (sum (pointwise (uncurry (MODULE_comp 1!F 2!W)) (Seqtl a)(Seqtl (comp_map_map T v))));Auto with algebra).
Apply SGROUP_comp.
(Apply Trans with ((head a) mX (T (head v)));Auto with algebra).
Fold (mult_by_scalars (Seqtl a) (Seqtl (comp_map_map T v))).
(Apply Trans with (sum (mult_by_scalars (Seqtl a) (comp_map_map T (Seqtl v))));Auto with algebra).
(Apply sum_comp;Auto with algebra).
Apply toMap.
(Apply mult_by_scalars_comp;Auto with algebra).
Intro.
Simpl.
NewDestruct x.
Unfold comp_map_fun.
(Apply Ap_comp;Auto with algebra).
(Apply sum_comp;Auto with algebra).
Qed.

