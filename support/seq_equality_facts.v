(** %\subsection*{ support :  seq\_equality\_facts.v }%*)
Set Implicit Arguments. 
Require Export seq_equality.
Require Export concat_facts.
Require Export omit.
Require Export Classical_Prop.

(** - Some useful lemmas concerning seq_equal *)

Lemma seq_equal_length_equal : (A:Setoid;n,m:Nat;v:(seq n A);w:(seq m A))
  (seq_equal v w) -> n='m.
Intros.
Red in H.
Apply NNPP;Intro.
Assert (lt n m)\/(lt m n).
(Apply nat_total_order;Auto with algebra).
Inversion_clear H1.
Generalize (H n);Clear H;Intro.
Inversion_clear H.
Inversion_clear H1.
(Apply (lt_n_n n);Auto with algebra).
Inversion_clear H1.
(Apply (lt_not_le n m);Auto with algebra).
Generalize (H m);Clear H;Intro.
Inversion_clear H.
Inversion_clear H1.
Inversion_clear H.
(Apply (lt_n_n m);Auto with algebra).
Inversion_clear H1.
(Apply (le_not_lt n m);Auto with algebra).
Qed.

Hints Resolve seq_equal_length_equal : algebra.

Lemma seq_equal_equal_elements : (A:Setoid;n,m:Nat;v:(seq n A);w:(seq m A))
  (seq_equal v w) -> 
    (i:(fin n);j:(fin m)) (index i)=(index j) -> (v i)='(w j).
Intros.
Red in H.
NewDestruct i.
Rename index into i.
NewDestruct j.
Rename index into j.
Simpl in H0.
Case (H i);Clear H;Intros.
Inversion_clear H.
Inversion_clear H1.
(Apply Trans with (v (Build_finiteT x));Auto with algebra).
(Apply Trans with (w (Build_finiteT x0));Auto with algebra).
Inversion_clear H.
Apply False_ind.
(Apply (le_not_lt n i);Auto with algebra).
Qed.

Hints Resolve seq_equal_equal_elements : algebra.


(** - The interplay with other operations *)
Lemma seq_equal_head : (A:Setoid;n,m:Nat;v:(seq (S n) A);w:(seq (S m) A))
  (seq_equal v w) -> (head v)='(head w).
Intros.
Red in H.
Case (H O);Clear H;Intros.
Inversion_clear H;Inversion_clear H0.
(Apply Trans with (v (Build_finiteT x));Auto with algebra).
(Apply Trans with (w (Build_finiteT x0));Auto with algebra).
Inversion_clear H;Inversion_clear H0.
Qed.

Hints Resolve seq_equal_head : algebra.

Lemma seq_equal_seqtl : (A:Setoid;n,m:Nat;v:(seq n A);w:(seq m A))
  (seq_equal v w) -> (seq_equal (Seqtl v) (Seqtl w)).
Intros.
NewDestruct n.
Red.
Intro.
Right.
Split;Simpl;Auto with arith.
Assert O=m.
(Apply seq_equal_length_equal with A v w;Auto with algebra).
Rewrite <- H0.
Simpl;Auto with arith.
NewDestruct m.
Assert (S n)=O.
(Apply seq_equal_length_equal with A v w;Auto with algebra).
Inversion_clear H0.
Red in H.
Red.
Simpl.
Intro;Case (H (S i));Clear H;Intros.
Inversion_clear H;Inversion_clear H0.
Left.
Exists (lt_S_n ?? x).
Exists (lt_S_n ?? x0).
(Apply Trans with (v (Build_finiteT x));Auto with algebra).
(Apply Trans with  (w (Build_finiteT x0));Auto with algebra).
Right.
Inversion_clear H.
Split;Auto with arith.
Qed.

Hints Resolve seq_equal_seqtl : algebra.

Lemma seq_equal_cons : (A:Setoid;n,m:Nat;v:(seq n A);w:(seq m A);a,b:A)
  (seq_equal v w) -> a='b
    -> (seq_equal a;;v b;;w).
Intros.
Assert n='m.
(Apply (seq_equal_length_equal 4!v 5!w);Auto with algebra).
Red.
Intro.
NewDestruct i.
Left.
Exists (lt_O_Sn n).
Exists (lt_O_Sn m).
Simpl.
Auto.
Case (le_or_lt (S n) (S n0)).
Intro.
Right.
Split;Auto.
Rewrite <- H1.
Auto.
Left.
Exists H2.
Assert (lt (S n0) (S m)).
Rewrite <- H1.
Auto.
Exists H3.
Simpl.
(Apply seq_equal_equal_elements;Auto with algebra).
Qed.

Hints Resolve seq_equal_cons : algebra.

Lemma seq_equal_concat :
  (A:Setoid;n,m,p,q:Nat;v:(seq n A);w:(seq m A);a:(seq p A);b:(seq q A))
    (seq_equal v w) -> (seq_equal a b)
      -> (seq_equal v++a w++b).
Intros.
Generalize (seq_equal_length_equal H).
Generalize (seq_equal_length_equal H0).
Intros.
Red.
Intro.
Generalize (le_or_lt (plus n p) i).
Intro.
Case H3.
Right.
Split;Try Tauto.
Rewrite <- H1.
Rewrite <- H2.
Tauto.
Intro.
Left.
Exists H4.
Assert (lt i (plus m q)).
Rewrite <- H1.
Rewrite <- H2.
Tauto.
Exists H5.
Generalize (le_or_lt n i).
Intro.
Case H6;Clear H6;Intro.
2:Assert (lt i m).
2:Rewrite <- H2.
2:Auto.
2:(Apply Trans with (v (Build_finiteT H6));Auto with algebra).
2:(Apply Trans with (w (Build_finiteT H7));Auto with algebra).
Assert (EXT k:Nat | i='(plus n k)).
Exists (minus i n).
Simpl;Symmetry.
Auto with arith.
Inversion_clear H7.
Assert (lt (plus n x) (plus n p)).
Rewrite <- H8.
Auto.
Assert (lt (plus m x) (plus m q)).
Rewrite <- H2.
Rewrite <- H1.
Auto.
(Apply Trans with (v++a (Build_finiteT H7));Auto with algebra).
Apply Trans with (w++b (Build_finiteT H9)).
2:(Apply Ap_comp;Auto with algebra).
2:Simpl.
2:Symmetry.
2:Rewrite <- H2.
2:Auto.
Assert (lt x p).
(Apply simpl_lt_plus_l with n;Auto with algebra).
(Apply Trans with (a (Build_finiteT H10));Auto with algebra).
Assert (lt x q).
Rewrite <- H1.
Auto.
(Apply Trans with (b (Build_finiteT H11));Auto with algebra).
Qed.

Hints Resolve seq_equal_concat : algebra.

Lemma seq_equal_seq_set : (A:Setoid;n,m:Nat;v:(seq n A);w:(seq m A))
  (seq_equal v w) -> (seq_set v)='(seq_set w).
Intros.
Assert n='m.
(Apply seq_equal_length_equal with A v w;Auto with algebra).
Simpl.
Red.
Split;Intro.
Simpl;Simpl in H1.
Inversion_clear H1.
NewDestruct x0.
Rename index into i.
Case (H i).
Intro.
Inversion_clear H1.
Inversion_clear H3.
Exists (Build_finiteT x1).
(Apply Trans with (v (Build_finiteT in_range_prf));Auto with algebra).
Intro.
Inversion_clear H1.
(Apply False_ind;Auto with algebra).
(Apply (le_not_lt n i);Auto with algebra).
Simpl;Simpl in H1.
Inversion_clear H1.
NewDestruct x0.
Rename index into i.
Case (H i).
Intro.
Inversion_clear H1.
Inversion_clear H3.
Exists (Build_finiteT x0).
(Apply Trans with (w (Build_finiteT in_range_prf));Auto with algebra).
Intro.
Inversion_clear H1.
(Apply False_ind;Auto with algebra).
(Apply (le_not_lt m i);Auto with algebra).
Qed.


Lemma seq_equal_omit :
  (A:Setoid;n,m:Nat;v:(seq n A);w:(seq m A);i:(fin n);j:(fin m))
    (index i)=(index j) -> (seq_equal v w)
      -> (seq_equal (omit v i) (omit w j)).
Intros.
Assert n='m.
(Apply seq_equal_length_equal with A v w;Auto with algebra).
Generalize Dependent j.
Generalize Dependent i.
Generalize Dependent w.
Generalize Dependent v.

NewDestruct n;NewDestruct m.
Simpl.
Auto.
Inversion_clear H1.
Inversion_clear H1.

Rename n0 into m.
Intros.
Generalize Dependent H.
Clear H1.
Generalize n m v w H0 i j.
Clear j i H0 w v m n.
NewInduction n;NewInduction m;Intros.
Simpl.
Apply seq_equal_refl.

Assert (S O)=(S (S m)).
(Apply seq_equal_length_equal with A v w;Auto with algebra).
Inversion_clear H1.

Assert (S (S n))=(S O).
(Apply seq_equal_length_equal with A v w;Auto with algebra).
Inversion_clear H1.

NewDestruct i;NewDestruct j.
NewDestruct index;NewDestruct index0.
Apply seq_equal_trans with (S n) (Seqtl v).
Apply Map_eq_seq_equal.
Auto with algebra.
Apply seq_equal_trans with (S m) (Seqtl w).
(Apply seq_equal_seqtl with v:=v w:=w;Auto with algebra).
Apply Map_eq_seq_equal.
Apply Sym.
Auto with algebra.
Inversion_clear H.
Inversion_clear H.

Apply seq_equal_trans with (S n) (head v);;(omit (Seqtl v) (Build_finiteT (lt_S_n??in_range_prf))).
Apply Map_eq_seq_equal.
Auto with algebra.
Apply seq_equal_trans with (S m) (head w);;(omit (Seqtl w) (Build_finiteT (lt_S_n??in_range_prf0))).
Apply seq_equal_cons.

3:Apply seq_equal_symm.
3:Apply Map_eq_seq_equal.
3:Auto with algebra.

Generalize (IHn ? (Seqtl v) (Seqtl w)).
Intros.
Assert (seq_equal (Seqtl v) (Seqtl w)).
(Apply seq_equal_seqtl;Auto with algebra).
Generalize (H1 H2).
Intro.
Generalize (H3 (Build_finiteT (lt_S_n n0 (S n) in_range_prf)) (Build_finiteT (lt_S_n n1 (S m) in_range_prf0))).
Intuition.

Generalize (H0 O).
Intro p;Inversion_clear p.
Inversion_clear H1.
Inversion_clear H2.
Unfold head.
Apply Trans with (v (Build_finiteT x)).
(Apply Ap_comp;Auto with algebra).
(Apply Trans with (w (Build_finiteT x0));Auto with algebra).
Inversion_clear H.
Inversion_clear H1.
Inversion_clear H.
Qed.