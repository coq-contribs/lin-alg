(** %\subsection*{ support :  random\_facts.v }%*)
Set Implicit Arguments.
Section MAIN.
Require Export concat_facts.
Require Export sums2.
Require Export mult_by_scalars.
Require Export vecspace_Fn.

Lemma inject_map_embed_seq_set : (A:Setoid;B:(part_set A);n:Nat;v:(seq n B))
  (inject_subsets (seq_set v))='(seq_set (Map_embed v)).
Simpl.
Red.
Split;Intros.
Rename x into a.
Simpl.
Simpl in H.
Inversion_clear H.
NewDestruct x.
Rename subtype_elt into b.
Rename subtype_prf into Hb.
Simpl in Hb.
Inversion_clear Hb.
Rename x into i.
Exists i.
Red in H.
Simpl in H0.
(Apply Trans with (subtype_elt b);Auto with algebra).

Simpl.
Rename x into a.
Assert (in_part a B).
Simpl in H.
Inversion_clear H.
(Apply in_part_comp_l with (subtype_elt (v x));Auto with algebra).
Red in H0.
LetTac b:=((Build_subtype H0)::B).
Assert (in_part b (seq_set v)).
Simpl.
Simpl in H.
Inversion_clear H.
Rename x into i.
Exists i.
Red.
(Apply Trans with a;Auto with algebra).
Red in H1.
Exists (Build_subtype H1).
Simpl.
Auto with algebra.
Qed.

Section concat_const_seq.
Variable A:Setoid.
Local eqa : (a:A)(Predicate A).
Intro; Apply Build_Predicate with [a']a'='a.
Red;Simpl.
Intros;Apply Trans with x;Auto with algebra.
Defined.

Lemma concat_const_seq : (n,m:Nat;a,a',a'':A)
  a='a'-> a'='a'' ->
    (const_seq n a)++(const_seq m a') =' (const_seq (plus n m) a'').
Intros.
Intro.
Apply Trans with a;Auto with algebra.
2:Simpl.
2:Apply Trans with a';Auto with algebra.
Generalize (!concat_prop_per_part A n m (const_seq n a) (const_seq m a') (eqa a));Intro.
Simpl in H1.
NewDestruct x.
Apply H1;Auto with algebra.
Qed.
End concat_const_seq.

Section mult_facts.
Variable F:field.
Variable V:(vectorspace F).
Lemma mult_const_Zero : (n:Nat;v:(seq n V))
  (mult_by_scalars (const_seq n (zero F)) v) =' (const_seq n (zero V)) in (seq??).
Induction n.
Simpl.
Red.
Intros.
Inversion x.
Inversion in_range_prf.
Intros.
Simpl.
Red.
Intro x; Elim x; Intro i; Case i.
Simpl.
Intro.
(Apply Zero_times_a_vector_gives_zero;Auto with algebra).
Simpl.
Intros.
(Apply Zero_times_a_vector_gives_zero;Auto with algebra).
Qed.

Lemma mult_const_zero : (n:Nat; a:(seq n F))
  (mult_by_scalars a (const_seq n (zero V))) =' (const_seq n (zero V)) in(seq??).
Intros.
Simpl.
Red.
Intro x.
Simpl.
(Apply a_scalar_times_zero_gives_zero;Auto with algebra).
Qed.
End mult_facts.

Hints Resolve mult_const_Zero mult_const_Zero : algebra.

Section proj_via_mult_by_scalars.

Local basisvec0prop : (F:field;n:Nat;H:(lt O (S n)))
  (Seqtl (Basisvec_Fn F H)) =' (const_seq n (zero F)).
Intros.
Simpl.
Red.
Simpl.
Intro.
Case x.
Auto with algebra.
Qed.

Local basisvecprop2 : (F:field;n,i:Nat;H:(lt i n);HS:(lt (S i) (S n)))
  (Seqtl (Basisvec_Fn F HS))=' (Basisvec_Fn F H).
Intros.
Simpl.
Red.
Intro x;Case x.
Intros.
(Apply Ap_comp;Auto with algebra).
Qed.

(** - $v_i = \vec e_i\cdot \vec v$ *)

Lemma projection_via_mult_by_scalars :
  (F:field;M:(module F);n,i:Nat;Hi,Hi':(lt i n);v:(seq n M))
    (v (Build_finiteT Hi)) =' (sum (mult_by_scalars (Basisvec_Fn F Hi') v)).
Intros F M n. 
Induction n.
Intros.
Inversion Hi.
Intros.
(Apply Trans with (sum (hdtl (mult_by_scalars (Basisvec_Fn F Hi) v)));Auto with algebra).
Unfold hdtl.
Generalize Hi;Clear Hi.
Generalize Hi';Clear Hi'.
Elim i.
Intros Hi' Hi.
Apply Trans with (head (mult_by_scalars (Basisvec_Fn F Hi) v))+'(zero M).
(Apply Trans with (head (mult_by_scalars (Basisvec_Fn F Hi) v));Auto with algebra).
Simpl.
(Apply Trans with (head v);Auto with algebra).
(Apply Trans with (head (mult_by_scalars (Basisvec_Fn F Hi) v))+'(sum (Seqtl (mult_by_scalars (Basisvec_Fn F Hi) v)));Auto with algebra).
(Apply SGROUP_comp;Auto with algebra).
Apply Trans with (sum (const_seq n (zero M))).
Apply Sym.
Apply sum_of_zeros;Auto with algebra.
Apply sum_comp.
Apply Trans with (mult_by_scalars (Seqtl (Basisvec_Fn F Hi)) (Seqtl v)).
(Apply Trans with (!mult_by_scalars F M n (const_seq n (zero F))::(Map??) (Seqtl v)::(Map??));Auto with algebra).
Unfold mult_by_scalars.
(Apply pointwise_Seqtl;Auto with algebra).
(**)
Intros.
Apply Trans with ((hdtl v) (Build_finiteT Hi)).
(Apply Ap_comp;Auto with algebra).
Apply Trans with (sum (zero M);;(Seqtl(mult_by_scalars (Basisvec_Fn F Hi) v))).
(Apply Trans with (zero M)+'(sum(Seqtl (mult_by_scalars (Basisvec_Fn F Hi) v)));Auto with algebra).
(Apply Trans with (sum (Seqtl (mult_by_scalars (Basisvec_Fn F Hi) v)));Auto with algebra).
Unfold hdtl.
(Apply Trans with ((Seqtl v) (Build_finiteT (lt_S_n ?? Hi)));Auto with algebra).
Apply Trans with (sum (mult_by_scalars (Seqtl (Basisvec_Fn F Hi)) (Seqtl v))).
(Apply Trans with (sum (mult_by_scalars (Basisvec_Fn F (lt_S_n ?? Hi)) (Seqtl v)));Auto with algebra).
2:Apply sum_comp.
2:Simpl.
2:Red.
2:Auto with algebra.
Apply sum_comp.
Simpl.
Red.
Simpl.
Intro x;Case x.
Auto with algebra.
Qed.

End proj_via_mult_by_scalars.

(** - $\sum_i (v_i+v'_i) = \sum_i v_i + \sum_i v'_i$ *)

Lemma sum_of_sums : (n:Nat;M:abelian_monoid;v,v':(seq n M))
  (sum (pointwise (sgroup_law_map M) v v')) =' (sum v) +' (sum v').
Induction n.
Intros.
Simpl.
Auto with algebra.
Intros.
(Apply Trans with (sum (hdtl v))+' (sum (hdtl v'));Auto with algebra).
Apply Trans with (sum (pointwise (sgroup_law_map (M)) (hdtl v) (hdtl v'))).
Apply sum_comp.
Apply toMap.
(Apply pointwise_comp;Auto with algebra).
Unfold hdtl.
(Apply Trans with ((head v)+'(sum (Seqtl v)))+'((head v')+'(sum (Seqtl v')));Auto with algebra).
(Apply Trans with (sum ((!sgroup_law_map M M) (couple (head v) (head v')));; (pointwise (sgroup_law_map M) (Seqtl v) (Seqtl v')));Auto with algebra).
(Apply Trans with ((sgroup_law_map M) (couple (head v) (head v')))+'(sum (pointwise (sgroup_law_map M) (Seqtl v) (Seqtl v')));Auto with algebra).
(Apply Trans with ((sgroup_law_map M) (couple (head v) (head v')))+'(sgroup_law M (sum (Seqtl v)) (sum (Seqtl v')));Auto with algebra).
(Apply Trans with ((head v)+'(head v'))+'((sum (Seqtl v))+'(sum (Seqtl v')));Auto with algebra).
Qed.

End MAIN.