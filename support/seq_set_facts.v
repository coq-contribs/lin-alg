(** %\subsection*{ support :  seq\_set\_facts.v }%*)
Set Implicit Arguments.
Require Export concat_facts.
Require Export Union.
Require Export Singleton.
Require Export Classical_Prop.

Section MAIN.

Variable A:Setoid.
Variable n:Nat.


Lemma seq_set_conseq_union : (v:(seq n A);a:A) 
  (seq_set a;;v)='(union (seq_set v) (single a)).
Intros.
Simpl.
Red.
Split;Intros.
Simpl in H.
Inversion_clear H.
NewDestruct x0.
NewDestruct index.
Simpl.
Right;Auto.
Simpl.
Left.
Exists (Build_finiteT (lt_S_n n0 ? in_range_prf)).
Auto.
Simpl in H.
Inversion_clear H.
Inversion_clear H0.
Simpl.
NewDestruct x0.
Exists (Build_finiteT (lt_n_S??in_range_prf)).
(Apply Trans with (v (Build_finiteT in_range_prf));Auto with algebra).
Simpl.
Exists (Build_finiteT (lt_O_Sn n)).
Auto.
Qed.

Lemma seq_set_concat_union: (m:Nat;v:(seq n A);w:(seq m A))
  (seq_set v++w) =' (union (seq_set v) (seq_set w)).
Simpl.
Red.
Intros.
Split;Intros.
Simpl.
Simpl in H.
Inversion_clear H.
NewDestruct x0.
Case (classic (lt index n)).
Intro.
Left.
Exists (Build_finiteT H).
(Apply Trans with  (v++w (Build_finiteT in_range_prf));Auto with algebra).
Right.
Assert (EXT i:Nat | index = (plus i n)).
Clear H0 x w v A.
Induction m.
Assert (plus n O)=n;Auto with arith.
Rewrite H0 in in_range_prf.
Absurd (lt index n);Auto.
Assert (lt index (plus n m))\/index=(plus n m).
(Apply le_lt_or_eq;Auto with algebra).
Assert (plus n (S m))=(S (plus n m));Auto with arith.
Rewrite H0 in in_range_prf.
Auto with arith.
Inversion_clear H0.
(Apply Hrecm;Auto with algebra).
Exists m.
Apply trans_eq with (plus n m);Auto with arith.
Inversion_clear H1.
Assert (lt x0 m).
Apply simpl_lt_plus_l with n.
Replace (plus n x0) with index.
Auto.
Transitivity (plus x0 n);Auto with arith.
Exists (Build_finiteT H1).
Generalize concat_second_part;Intro p.
Assert irp':(lt (plus n x0) (plus n m)).
Replace (plus n x0)with (plus x0 n);Auto with arith.
Rewrite <- H2;Auto.
(Apply Trans with (v++w (Build_finiteT irp'));Auto with algebra).
(Apply Trans with (v++w (Build_finiteT in_range_prf));Auto with algebra).
(Apply Ap_comp;Auto with algebra).
Simpl.
Transitivity (plus x0 n);Auto with arith.

Simpl.
Simpl in H.
Inversion_clear H.
Inversion_clear H0.
NewDestruct x0.
Exists (Build_finiteT (lt_plus_trans ?? m in_range_prf)).
(Apply Trans with (v (Build_finiteT in_range_prf));Auto with algebra).
Inversion_clear H0.
NewDestruct x0.
Assert (lt (plus n index) (plus n m)).
Auto with arith.
Exists (Build_finiteT H0).
(Apply Trans with (w (Build_finiteT in_range_prf));Auto with algebra).
Qed.

Lemma seq_set_head_or_tail : (v:(seq (S n) A);a:A)
  (in_part a (seq_set v)) -> ~a='(head v)
    -> (in_part a (seq_set (Seqtl v))).
Intros.
Simpl in H.
Inversion_clear H.
NewDestruct x.
NewDestruct index.
Absurd a='(head v);Auto with algebra.
Unfold head;(Apply Trans with (v (Build_finiteT in_range_prf));Auto with algebra).
Simpl.
Exists (Build_finiteT (lt_S_n??in_range_prf)).
(Apply Trans with (v (Build_finiteT in_range_prf));Auto with algebra).
Qed.

Lemma has_index : (v:(seq n A)) (a:(seq_set v))
  (EXT i:(fin n) | ((seq_set v) a)='(v i)in A).
Intros.
Elim a.
Intros.
Rename subtype_elt into a'.
Rename subtype_prf into Ha'.
Simpl in Ha'.
Inversion_clear Ha'.
Exists x.
Simpl.
Auto.
Qed.


End MAIN.
Hints Resolve seq_set_conseq_union seq_set_head_or_tail: algebra.
Hints Resolve has_index : algebra.