(** %\subsection*{ support :  sums2.v }%*)
Set Implicit Arguments.
Require Export Abelian_group_facts.
Require Export sums.
Require Export omit.
Require Export modify_seq.
Require Export const.

Lemma sum_omit_zeros : (M:monoid;n:Nat;v:(seq n M);i:(fin n))
  (v i)='(zero M) -> (sum v)='(sum (omit v i)).
NewDestruct n.
Auto with algebra.

Induction n.
Intros.
Simpl.
Generalize H.
Unfold head.
Elim i.
Intro x;Case x.
Intros.
(Apply Trans with (v (Build_finiteT (lt_O_Sn O)));Auto with algebra).
(Apply Trans with (v (Build_finiteT in_range_prf));Auto with algebra).
Intros.
Inversion in_range_prf.
Inversion H2.
Intros.
Generalize H;Clear H.
Case i.
Intro x;Case x.
Intros.
(Apply Trans with (sum (hdtl v));Auto with algebra).
Unfold hdtl.
Unfold head.
(Apply Trans with (zero M)+'(sum (Seqtl v));Auto with algebra).
(Apply Trans with (v (Build_finiteT (lt_O_Sn (S n))))+'(sum (Seqtl v));Auto with algebra).
(Apply SGROUP_comp;Auto with algebra).
(Apply Trans with (v (Build_finiteT in_range_prf));Auto with algebra).
Intros.
(Apply Trans with (sum (hdtl v));Auto with algebra).
(Apply Trans with (sum (head v);;(omit (Seqtl v) (Build_finiteT (lt_S_n ?? in_range_prf))));Auto with algebra).
Unfold hdtl.
(Apply Trans with (head v)+'(sum (Seqtl v));Auto with algebra).
(Apply Trans with (head v)+'(sum (omit (Seqtl v) (Build_finiteT (lt_S_n ?? in_range_prf))));Auto with algebra).
(Apply SGROUP_comp;Auto with algebra).
(Apply Hrecn;Auto with algebra).
(Apply Trans with (v (Build_finiteT in_range_prf));Auto with algebra).
Generalize Seqtl_to_seq.
Intro.
Apply (H0 M (S n) v n0 (lt_S_n n0 (S n) in_range_prf) in_range_prf).
Qed.

Lemma sum_modify : (AG:abelian_group; n:Nat; v:(seq n AG); i:(fin n); a:AG)
  (sum (modify_seq v i a)) =' (sum v)+'(min (v i))+'a.
Induction n.
Intros.
Inversion i.
Inversion in_range_prf.
Intros.
NewDestruct i.
NewDestruct index.
(Apply Trans with (sum a;;(Seqtl v));Auto with algebra).
Apply Trans with (sum (hdtl v))+'(min (head v))+'a.
(Apply Trans with a+'(sum (Seqtl v));Auto with algebra).
Apply Trans with (sum (Seqtl v))+'a;Auto with algebra.
(Apply SGROUP_comp;Auto with algebra).
Unfold hdtl.
(Apply Trans with (head v)+'(sum (Seqtl v))+'(min (head v));Auto with algebra).
(Apply Trans with ((sum (Seqtl v))+'(head v))+'(min(head v));Auto with algebra).
(Apply Trans with (sum (Seqtl v))+'((head v)+'(min(head v)));Auto with algebra).
(Apply Trans with (sum (Seqtl v))+'(zero AG);Auto with algebra).

(Apply SGROUP_comp;Auto with algebra).
Apply SGROUP_comp;Auto with algebra.

(Apply Trans with (sum (hdtl (modify_seq v (Build_finiteT in_range_prf) a)));Auto with algebra).
Unfold hdtl.
(Apply Trans with (head (modify_seq v (Build_finiteT in_range_prf) a))+'(sum (Seqtl (modify_seq v (Build_finiteT in_range_prf) a)));Auto with algebra).
(Apply Trans with (head v)+'(sum (Seqtl (modify_seq v (Build_finiteT in_range_prf) a)));Auto with algebra).
(Apply Trans with (sum (hdtl v))+'(min (v (Build_finiteT in_range_prf))) +' a;Auto with algebra).
Unfold hdtl.
(Apply Trans with (head v)+'(sum (Seqtl v))+'(min (v (Build_finiteT in_range_prf))) +' a;Auto with algebra).
Apply Trans with (head v)+'((sum (Seqtl v))+'(min (v (Build_finiteT in_range_prf))) +' a).
(Apply SGROUP_comp;Auto with algebra).
(Apply Trans with (sum (modify_seq (Seqtl v) (Build_finiteT (lt_S_n??in_range_prf)) a));Auto with algebra).

(Apply Trans with (((sum (Seqtl v)) +' (min (Seqtl v (Build_finiteT (lt_S_n??in_range_prf))))) +' a);Auto with algebra).
(Apply Trans with ((head v)+'((sum (Seqtl v)) +' (min (v (Build_finiteT in_range_prf)))))+'a;Auto with algebra).
Qed.

Lemma sum_of_zeros : (M:monoid;n:Nat;v:(seq n M))
  v='(const_seq n (zero M)) -> (sum v)='(zero M).
Induction n;Intros.
Simpl.
Apply Refl.
(Apply Trans with (sum (hdtl v));Auto with algebra).
Unfold hdtl.
(Apply Trans with (head v)+'(sum (Seqtl v));Auto with algebra).
Apply Trans with (zero M)+'(sum (Seqtl v)).
(Apply SGROUP_comp;Auto with algebra).
Unfold head.
Simpl in H0.
Red in H0.
(Apply Trans with (const_seq (S n0) (zero M) (Build_finiteT (lt_O_Sn n0)));Auto with algebra).
(Apply Trans with ((zero M) +'(zero M));Auto with algebra).
(Apply SGROUP_comp;Auto with algebra).
(Apply H;Auto with algebra).
Simpl;Simpl in H0.
Red;Red in H0.
Simpl;Simpl in H0.
Intro.
NewDestruct x.
Auto with algebra.
Qed.

Hints Resolve sum_omit_zeros sum_modify sum_of_zeros : algebra.