(** %\subsection*{ support :  modify\_seq.v }%*)
(** - if $v=\langle v_0...v_i...v_{n-1}\rangle$ then (modify v i a) =
 $\langle v_0...a...v_{n-1}\rangle$ *)
Set Implicit Arguments.
Require Export conshdtl.

(** %\label{modifyseq}% *)
Definition modify_seq : (A:Setoid)(n:Nat)(seq n A)->(fin n)->A->(seq n A).
NewInduction n.
Intros.
Auto.
Intros.
NewDestruct X0.
NewDestruct index.
Exact X1;;(Seqtl X).
Exact (head X);;(IHn (Seqtl X) (Build_finiteT (lt_S_n ?? in_range_prf)) X1).
Defined.

Lemma modify_comp : (A:Setoid;n:Nat;a,a':A;v,v':(seq n A);i,i':(fin n)) 
  a='a' -> v='v' -> i='i'
    -> (modify_seq v i a)='(modify_seq v' i' a').
NewInduction n.
Intros.
(Apply False_ind;Auto with algebra).
Intros.
NewDestruct i.
NewDestruct i'.
NewDestruct index.
NewDestruct index0.
(Apply split_hd_tl_equality;Auto with algebra).
Intro.
NewDestruct x.
Simpl.
(Apply Ap_comp;Auto with algebra).
Inversion H1.
NewDestruct index0.
Inversion H1.
Unfold modify_seq.
Unfold nat_rect.
(Apply cons_comp;Auto with algebra).
Unfold modify_seq in IHn.
(Apply IHn;Auto with algebra).
Change   (Seqtl v) =' (Seqtl v').
(Apply Seqtl_comp;Auto with algebra).
Qed.

Hints Resolve modify_comp : algebra.

Lemma modify_hd_hd : (A:Setoid;n:Nat;v:(seq (S n) A);H:(lt O (S n));a:A)
  (head (modify_seq v (Build_finiteT H) a))='a.
Intros.
Simpl.
Auto with algebra.
Qed.

Hints Resolve modify_hd_hd : algebra.

Lemma modify_hd_tl :(A:Setoid;n:Nat;v:(seq (S n) A);H:(lt O (S n));a:A)
  (Seqtl (modify_seq v (Build_finiteT H) a))='(Seqtl v).
Intros.
Unfold modify_seq nat_rect.
Auto with algebra.
Qed.

Hints Resolve modify_hd_tl : algebra.

Lemma modify_tl_hd : (A:Setoid;n:Nat;v:(seq (S n) A);m:Nat;H:(lt (S m) (S n));a:A)
  (head (modify_seq v (Build_finiteT H) a))='(head v).
Intros.
Simpl;Auto with algebra.
Qed.

Hints Resolve modify_tl_hd : algebra.

Lemma modify_tl_tl :
  (A:Setoid;n:Nat;v:(seq (S n) A);m:Nat;HS:(lt (S m) (S n));H:(lt m n);a:A)
    (Seqtl (modify_seq v (Build_finiteT HS) a))
      =' (modify_seq (Seqtl v) (Build_finiteT H) a).
Intros;Intro.
Unfold Seqtl.
Simpl.
Case x.
Intros.
(Apply Ap_comp;Auto with algebra).
Qed.

Hints Resolve modify_tl_tl : algebra.

Lemma Seqtl_modify_seq : (A:Setoid;n:Nat;v:(seq (S n) A);a:A;H:(lt O (S n)))
  (modify_seq v (Build_finiteT H) a)='a;;(Seqtl v).
Intros;Intro.
Simpl.
Auto with algebra.
Qed.

Hints Resolve Seqtl_modify_seq.

Lemma modify_seq_defprop : (A:Setoid;n:Nat;v:(seq n A);i:(fin n);a:A)
  ((modify_seq v i a) i)='a.
NewInduction n.
Intros.
(Apply False_ind;Auto with algebra).
Intros.
Case i.
NewDestruct index.
Simpl.
Auto with algebra.
Intro.
(Apply Trans with (modify_seq (Seqtl v) (Build_finiteT (lt_S_n??in_range_prf)) a (Build_finiteT (lt_S_n??in_range_prf)));Auto with algebra).
Qed.

Hints Resolve modify_seq_defprop : algebra.

Lemma modify_seq_modifies_one_elt : (A:Setoid;n:Nat;v:(seq n A);i:(fin n);a:A)
  (j:(fin n))  ~j='i -> ((modify_seq v i a) j)='(v j).
NewInduction n.
Intros v i.
(Apply False_ind;Auto with algebra).
Intros until j.
NewDestruct i;NewDestruct j.
NewDestruct index;NewDestruct index0;Simpl.
Intros;Absurd O=O;Auto.
Intros _.
(Apply Ap_comp;Auto with algebra).
Intros _.
Auto with algebra.
Intros.
Rename in_range_prf0 into l.
Apply Trans with ((head v);;(Seqtl v) (Build_finiteT l)).
2:(Apply Trans with ((hdtl v) (Build_finiteT l));Auto with algebra).
(Apply Trans with ((Seqtl v) (Build_finiteT (lt_S_n??l)));Auto with algebra).
Qed.

Hints Resolve modify_seq_modifies_one_elt : algebra.
