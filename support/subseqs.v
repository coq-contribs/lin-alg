(** %\subsection*{ support :  subseqs.v }%*)
Set Implicit Arguments.
Require Export conshdtl.

(** - subsequences, inductively defined *)
Section defs.
Variable A:Setoid.

Inductive is_subseq : (m:Nat;w:(seq m A); n:Nat;v:(seq n A)) Prop :=
  is_subseq_empty : (n:Nat;v:(seq n A))
     (w:(seq O A)) (is_subseq w v)
| is_subseq_of_tail : (m:Nat;w:(seq m A); n:Nat;v:(seq n A))
     (is_subseq w v)->(a:A)(is_subseq w a;;v)
| is_subseq_cons : (m:Nat;w:(seq m A); n:Nat;v:(seq n A))
     (is_subseq w v)->(a:A)(is_subseq a;;w a;;v)
| is_subseq_comp : (m:Nat;w,w':(seq m A); n:Nat;v,v':(seq n A))
     (is_subseq w' v')-> w='w'->v='v'->(is_subseq w v).

Lemma subseq_has_right_elements : (m:Nat;w:(seq m A); n:Nat;v:(seq n A))
  (is_subseq w v) -> (i:(fin m))(EXT i':(fin n) | (w i)='(v i')).
Intros.
NewInduction H.
(Apply False_ind;Auto with algebra).
Case (IHis_subseq i).
Intros.
NewDestruct x.
Exists (Build_finiteT (lt_n_S ??in_range_prf)).
(Apply Trans with (v (Build_finiteT in_range_prf));Auto with algebra).
NewDestruct i;NewDestruct index.
Exists (Build_finiteT (lt_O_Sn n)).
Auto with algebra.
Generalize (IHis_subseq (Build_finiteT (lt_S_n ?? in_range_prf)));Intro.
Inversion_clear H0.
NewDestruct x.
Exists (Build_finiteT(lt_n_S??in_range_prf0)).
(Apply Trans with (v (Build_finiteT in_range_prf0));Auto with algebra).
Generalize (IHis_subseq i).
Intros.
Inversion_clear H2.
Exists x.
(Apply Trans with (w' i);Auto with algebra).
(Apply Trans with (v' x);Auto with algebra).
Qed.

Lemma subseqs_are_not_longer : (m,n:Nat;w:(seq m A);v:(seq n A))
  (is_subseq w v)->(le m n).
Intros.
NewInduction H;Simpl;Auto with algebra arith.
Qed.
End defs.

