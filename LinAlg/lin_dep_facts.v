(** * lin_dep_facts.v *)
Set Implicit Arguments.
Require Export lin_dependence.
Require Export lin_comb_facts.
Require Export subseqs.
Require Export seq_set_facts.
Require Export distinct_facts.

(** - If $a_i\neq0$ and $\sum_ka_kv_k=0$, then $v_i=-a_i^{-1}\sum_{k\neq i}a_kv_k$ *)

Lemma rewrite_lin_comb_term :
  (F:field;V:(vectorspace F);n:Nat;a:(seq (S n) F);v:(seq (S n) V);i:(fin (S n)))
    ~(a i)='(zero F) -> (sum (mult_by_scalars a v))='(zero V) ->
      (v i)='((field_inverse (a i)) mX (min (sum (omit (mult_by_scalars a v) i)))).
Intros.
Assert (a i)mX(v i) =' (a i)mX((field_inverse (a i)) mX (min (sum (omit (mult_by_scalars a v) i)))).

(Apply Trans with ((mult_by_scalars a v) i);Auto with algebra).
(Apply Trans with ((a i)rX(field_inverse (a i)))mX(min (sum (omit (mult_by_scalars a v) i)));Auto with algebra).
(Apply Trans with one mX (min (sum (omit (mult_by_scalars a v) i)));Auto with algebra).

(Apply Trans with (min (sum (omit (mult_by_scalars a v) i)));Auto with algebra).
Assert ((mult_by_scalars a v) i)+'(sum (omit (mult_by_scalars a v) i))='(zero V).

(Apply Trans with (sum (mult_by_scalars a v));Auto with algebra).
Apply Sym.
Apply (seqsum_is_elt_plus_omitseq 2!(V::abelian_monoid) (mult_by_scalars a v)).

2:(Apply MODULE_comp;Auto with algebra).
2:Apply Sym.
2:(Apply FIELD_inverse_r;Auto with algebra).

Apply Sym.
Apply GROUP_law_inverse.
(Apply Trans with (sum (mult_by_scalars a v));Auto with algebra).
(Apply Trans with ((mult_by_scalars a v) i)+'(sum (omit (mult_by_scalars a v) i));Auto with algebra).
Apply Sym.
(Apply (seqsum_is_elt_plus_omitseq 2!(V::abelian_monoid) (mult_by_scalars a v));Auto with algebra).

LetTac expr:=(field_inverse (a i))
                mX (min (sum (omit (mult_by_scalars a v) i))).

Cut one mX (v i) =' one mX expr.
Intro.
(Apply Trans with one mX expr;Auto with algebra).
(Apply Trans with one mX (v i);Auto with algebra).
Apply Trans with ((field_inverse (a i))rX(a i))mX(v i).
(Apply MODULE_comp;Auto with algebra).
Apply Sym.
Auto with algebra.
(Apply Trans with ((field_inverse (a i))rX(a i))mX expr;Auto with algebra).
(Apply Trans with (field_inverse (a i))mX((a i)mX expr);Auto with algebra).
(Apply Trans with (field_inverse (a i))mX((a i)mX (v i));Auto with algebra).
Qed.

(** - If $y\in W\cup\{x\}$ but $y\neq x$ then $y\in W$ *)
Lemma another_small_lemma : (V:Setoid;W:(part_set V);x:V)
  [Wx=(union W (single x))]
    (y:Wx) ~(subtype_elt y)='x -> (in_part (subtype_elt y) W).
Simpl.
Intros.
Generalize H;Elim y.
Intros yv yp Hy.
Simpl in yp.
Simpl in Hy.
Simpl.
Unfold not in Hy.
Case yp;Auto.
Tauto.
Qed.

(** - %\intoc{\bf Theorem 1.8}%: If $S\subset V$ is linearly independent and $x\not\in S$
 then $S\cup\{x\}$ is linearly dependent iff $x\in span(S)$

 (By the by - this innocent-looking lemma was extremely hard to prove) *)
Lemma lin_dep_vs_span_lemma : (F:field;V:(vectorspace F);s:(part_set V))
  (lin_indep s)->(x:V) ~(in_part x s) ->
    ( (lin_dep (union s (single x))) <-> (in_part x (span s)) ).  
Intros.
LetTac Sx:=(union s (single x)).
Split.
Intro.
Unfold lin_dep in H1.
Elim H1;Clear H1;Intros.
Elim H1;Clear H1;Intros.
Elim H1;Clear H1;Intros.
Elim H1;Clear H1;Intros.
Elim H2;Clear H2;Intros.
Generalize x0 x1 x2 H1 H2 H3.
Clear H3 H2 H1 x2 x1 x0;Intros n a x' Hx' Ha Hlc.
Assert ~(i:(fin (S n)))(in_part (Map_embed x' i) s).
Red;Intro.
Assert (EXT y:(seq (S n) s) | (Map_embed y)='(Map_embed x')).
Unfold seq.
(Apply subset_seq_castable;Auto with algebra).
Inversion H2.
Repeat Red in H;Apply H.
Red.
Exists n.
Exists a.
Exists x0.
Split.
Assert (distinct (Map_embed x')).
(Apply Map_embed_preserves_distinct;Auto with algebra).
Assert (distinct (Map_embed x0)).
(Apply distinct_comp with (Map_embed x');Auto with algebra).
(Apply Map_embed_reflects_distinct;Auto with algebra).
Split.
Auto.
(Apply Trans with (sum (mult_by_scalars a (Map_embed x')));Auto with algebra).
Assert (EXT i:(fin (S n)) | ~(in_part (Map_embed x' i) s)).
Apply NNPP.
Red;Red in H1.
Intro;Apply H1.
Intro.
Red in H2.
Apply NNPP.
Red.
Intro.
Apply H2.
Exists i;Auto.
Elim H2;Intros.
Generalize x0 H3;Clear H3 x0;Intros i Hi.
Assert (in_part (Map_embed x' i) Sx).
(Apply Map_embed_prop;Auto with algebra).
Assert (in_part (Map_embed x' i) (single x)).
(Apply union_not_in_l with s;Auto with algebra).
Assert (Map_embed x' i)=' x.
(Apply single_prop_rev;Auto with algebra).
Cut ~(a i)='(zero F).
Intro.
Assert (Map_embed x' i)='((field_inverse (a i)) mX (min (sum (omit (mult_by_scalars a (Map_embed x'))::(seq??) i)))).
(Apply rewrite_lin_comb_term;Auto with algebra).
Assert (j:(fin n))(in_part ((omit (Map_embed x') i) j) s).
Intro.
Assert (distinct (Map_embed x')).
(Apply Map_embed_preserves_distinct;Auto with algebra).
Assert ~(omit (Map_embed x') i j)='(Map_embed x' i).
(Apply distinct_omit_removes_all;Auto with algebra).
Assert ~(omit (Map_embed x') i j)='x. 
Red;Red in H9;Intro;Apply H9.
(Apply Trans with x;Auto with algebra).
Assert ~(in_part (omit (Map_embed x') i j) (single x)).
Red;Red in H10;Intro;Apply H10.
(Apply single_prop_rev;Auto with algebra).
Assert (in_part (omit (Map_embed x') i j) Sx).
(Apply in_part_comp_l with ((Map_embed (omit x' i)) j);Auto with algebra).
(Apply Map_embed_prop;Auto with algebra).
Assert (in_part (omit (Map_embed x') i j) (union (single x) s)).
(Apply in_part_comp_r with Sx;Auto with algebra).
Simpl.
Red.
Simpl.
Split.
Tauto.
Tauto.
(Apply union_not_in_l with (single x);Auto with algebra).
Assert x =' (sum (mult_by_scalars (pointwise (uncurry (RING_comp 1!F)) (const_seq n (min (field_inverse (a i)))) (omit a i)) (omit (Map_embed x') i))).
(Apply Trans with (Map_embed x' i);Auto with algebra).
Cut ((field_inverse (a i))  mX (min (sum (omit (mult_by_scalars a (Map_embed x')) ::(seq (S n) V) i)))) =' (sum (mult_by_scalars (pointwise (uncurry (RING_comp 1!F)) (const_seq n (min (field_inverse (a i)))) (omit a i)) (omit (Map_embed x') i))).
Intro.
(Apply Trans with ((field_inverse (a i)) mX (min (sum (omit (mult_by_scalars a (Map_embed x')) i))));Auto with algebra).
Apply Trans with (sum (mult_by_scalars (const_seq n (min (field_inverse (a i)))) (mult_by_scalars (omit a i)(omit (Map_embed x') i)))).

2:(Apply sum_comp;Auto with algebra).
(Apply Trans with (min (field_inverse (a i))) mX (sum (mult_by_scalars (omit a i) (omit (Map_embed x') i)));Auto with algebra).
(Apply Sym;Auto with algebra).
(Apply Trans with ((min (field_inverse (a i))) mX (sum(omit (mult_by_scalars a (Map_embed x')) i)));Auto with algebra).
Assert (EXT y:(seq n s) | (Map_embed y)='(omit (Map_embed x') i)).
Unfold seq.
(Apply seq_castable;Auto with algebra).
Elim H10;Intros.
Assert  x =' (sum (mult_by_scalars (pointwise (uncurry (RING_comp 1!F)) (const_seq n (min (field_inverse (a i)))) (omit a i)) (Map_embed x0))).
(Apply Trans with (sum (mult_by_scalars (pointwise (uncurry (RING_comp 1!F))(const_seq n (min (field_inverse (a i)))) (omit a i)) (omit (Map_embed x') i)));Auto with algebra).
Simpl.
Red.
Exists n.
Exists (pointwise (uncurry (RING_comp 1!F)) (const_seq n (min (field_inverse (a i)))) (omit a i)).
Exists x0.
Auto.

Generalize a x' Hx' Ha Hlc i H5; Clear H5 H4 H3 Hi i H2 H1 Hlc Ha Hx' x' a;Case n.
Intros.
Red;Red in Ha;Intro;Apply Ha.
Assert (head a)='(zero F).
(Apply Trans with (a i);Auto with algebra).
(Apply Sym;Auto with algebra).

Intros.
Red;Intro.
Assert (sum (mult_by_scalars (omit a i) (omit (Map_embed x') i))) =' (zero V).
(Apply Trans with (sum (omit (mult_by_scalars a (Map_embed x')) i));Auto with algebra).
(Apply Trans with (sum (mult_by_scalars a (Map_embed x')));Auto with algebra).
Apply Sym.
(Apply sum_omit_zeros;Auto with algebra).
Simpl.
(Apply Trans with (zero F) mX (subtype_elt (x' i));Auto with algebra).
Assert (EXT y:(seq (S n0) s) | (Map_embed y)='(omit (Map_embed x') i)).
(* copy'n'paste *)
Assert (j:(fin (S n0)))(in_part ((omit (Map_embed x') i) j) s).
Intro.
Assert (distinct (Map_embed x')).
(Apply Map_embed_preserves_distinct;Auto with algebra).
Assert ~(omit (Map_embed x') i j)='(Map_embed x' i).
(Apply distinct_omit_removes_all;Auto with algebra).
Assert ~(omit (Map_embed x') i j)='x. 
Red;Red in H4;Intro;Apply H4.
(Apply Trans with x;Auto with algebra).
Assert ~(in_part (omit (Map_embed x') i j) (single x)).
Red;Red in H6;Intro;Apply H6.
(Apply single_prop_rev;Auto with algebra).
Assert (in_part (omit (Map_embed x') i j) Sx).
(Apply in_part_comp_l with ((Map_embed (omit x' i)) j);Auto with algebra).
(Apply Map_embed_prop;Auto with algebra).
Assert (in_part (omit (Map_embed x') i j) (union (single x) s)).
(Apply in_part_comp_r with Sx;Auto with algebra).
Simpl.
Red.
Simpl.
Split.
Tauto.
Tauto.
(Apply union_not_in_l with (single x);Auto with algebra).
Unfold seq.
(Apply seq_castable;Auto with algebra).
Elim H3;Intros.
Assert (sum (mult_by_scalars (omit a i) (Map_embed x0)))='(zero V).
(Apply Trans with (sum (mult_by_scalars (omit a i) (omit (Map_embed x') i)));Auto with algebra).
Red in H.
Red in H.
(Apply H;Auto with algebra).
Red.
Exists n0.
Exists (omit a i).
Exists x0.
Split.
(Apply Map_embed_reflects_distinct;Auto with algebra).
(Apply distinct_comp with (omit (Map_embed x') i);Auto with algebra).
(Apply (omit_preserves_distinct 3! (Map_embed x'));Auto with algebra).
Split.
Red;Red in Ha;Intro;Apply Ha.
2:Auto.
Clear H6 H4 x0 H3 H2 H5 Hlc Hx' x' n Sx H0 x H s V.
Simpl;Red.
Simpl.
Intro j.
Elim (fin_decidable i j).
Intro.
(Apply Trans with (a i);Auto with algebra).
Change (Map_eq (omit a i) (const_seq (S n0) (zero F))) in H7.
Red in H7.
Intro.
Generalize omit_removes'.
Intro p.
Case (p??a??H).
Intros.
(Apply Trans with (omit a i x);Auto with algebra).
(Apply Trans with (const_seq (S n0) (zero F) x);Auto with algebra).
(* My gods that was painful *)

(* Now the other direction *)
Intro.
Simpl in H1.
Generalize (lin_comb_with_distinct_vectors H1).
Clear H1.
Intro H1.
Elim H1;Clear H1;Intros.
Elim H1;Clear H1;Intros.
Elim H1;Clear H1;Intros.
Elim H1;Clear H1;Intros.
Rename H2 into Dx2.
Assert (EXT v:(seq x0 Sx) | (Map_embed v)='(Map_embed x2)).
Unfold seq.
(Apply subset_seq_castable;Auto with algebra).
Intro.
Assert (in_part (Map_embed x2 i) s).
(Apply Map_embed_prop;Auto with algebra).
Unfold Sx.
(Apply in_part_union_l;Auto with algebra).
Elim H2;Clear H2;Intros.
Assert x=' (sum (mult_by_scalars x1 (Map_embed x3))).
(Apply Trans with (sum (mult_by_scalars x1 (Map_embed x2)));Auto with algebra).
Assert (EXT x':Sx | (Sx x')='x).
Simpl.
Assert (in_part x Sx).
Simpl.
Right;Auto with algebra.
Assert (Pred_fun Sx x);Auto with algebra.
Exists (Build_subtype H5).
Simpl.
Auto with algebra.
Elim H4;Clear H4;Intros.
Assert (sum (mult_by_scalars (min one);;x1 (Map_embed (x4;;x3))))=' (zero V).
Apply Trans with (sum (mult_by_scalars ((min one);;x1) (Sx x4);;(Map_embed x3))).
(Apply sum_comp;Auto with algebra).
Unfold mult_by_scalars.
Apply Trans with (sum (uncurry (MODULE_comp 2!V) (couple (min one) (Sx x4)));;(mult_by_scalars x1 (Map_embed x3))).
Unfold mult_by_scalars.
(Apply sum_comp;Auto with algebra).
(Apply Trans with (uncurry (MODULE_comp 1!F 2!V) (couple (min one) (Sx x4))) +' (sum (mult_by_scalars x1 (Map_embed x3)));Auto with algebra).
Simpl.
(Apply Trans with (min (one mX (Sx x4))) +' (sum (mult_by_scalars x1 (Map_embed x3)));Auto with algebra).
(Apply Trans with (min (one mX (Sx x4))) +' x;Auto with algebra).
(Apply Trans with (min (Sx x4))+' x;Auto with algebra).
(Apply Trans with (min x) +' x;Auto with algebra).
Red.
Exists x0.
Exists (min one);;x1.
Exists x4;;x3.
Split.
Red.

Assert (distinct x3).
Apply Map_embed_reflects_distinct.
(Apply distinct_comp with (Map_embed x2);Auto with algebra).
Intros i j;Case i;Case j.
Intros ni Hi nj Hj;Generalize Hi Hj;Clear Hj Hi;Case ni;Case nj.
Simpl.
Intros;Absurd O=O;Auto.
3:Intros.
3:Simpl.
3:Red in H6.
3:Simpl in H6.
3:(Apply H6;Auto with algebra).
Simpl.
Intros.
Change ~(x3 (Build_finiteT (lt_S_n??Hj)))='x4.
Red;Intro.
Assert (in_part (Sx (x3 (Build_finiteT (lt_S_n??Hj)))) s).
(Apply in_part_comp_l with ((Map_embed x3) (Build_finiteT (lt_S_n??Hj)));Auto with algebra).
(Apply in_part_comp_l with ((Map_embed x2) (Build_finiteT (lt_S_n??Hj)));Auto with algebra).
(Apply Map_embed_prop;Auto with algebra).
Assert ~(in_part (Sx x4) s).
Red;Intro.
Assert (in_part x s).
(Apply in_part_comp_l with (Sx x4);Auto with algebra).
Absurd (in_part x s);Auto.
Red in H10;(Apply H10;Auto with algebra).
(Apply in_part_comp_l with (Sx (x3 (Build_finiteT (lt_S_n??Hj))));Auto with algebra).
Simpl.
Intros.
Change ~x4='(x3 (Build_finiteT (lt_S_n??Hi))).
Red;Intro.
Assert (in_part (Sx (x3 (Build_finiteT (lt_S_n??Hi)))) s).
(Apply in_part_comp_l with ((Map_embed x3) (Build_finiteT (lt_S_n??Hi)));Auto with algebra).
(Apply in_part_comp_l with ((Map_embed x2) (Build_finiteT (lt_S_n??Hi)));Auto with algebra).
(Apply Map_embed_prop;Auto with algebra).
Assert ~(in_part (Sx x4) s).
Red;Intro.
Assert (in_part x s).
(Apply in_part_comp_l with (Sx x4);Auto with algebra).
Absurd (in_part x s);Auto.
Red in H10;(Apply H10;Auto with algebra).
(Apply in_part_comp_l with (Sx (x3 (Build_finiteT (lt_S_n??Hi))));Auto with algebra).

Split.
Simpl.
Red;Intro.
Red in H6.
Generalize (H6 (Build_finiteT (lt_O_Sn x0))).
Simpl.
Intro.
Absurd one='(zero F);Auto with algebra.
(Apply Trans with (min (zero F));Auto with algebra).
(Apply Trans with ((min (min one))::F);Auto with algebra).
Auto.
Qed.

(** - Remember how max_lin_dep was defined with respect to arbitrary sets instead of
 just subspaces. So (max_lin_indep W' W) need not mean span(W')=W *)

Lemma max_lin_indep_subset_generates_set :
  (F:field;V:(vectorspace F);W,W':(part_set V))
    (max_lin_indep W' W) -> (w:W)(is_lin_comb (subtype_elt w) W').
Intros.
Red in H.
Elim H;Clear H;Intros.
Elim H0;Clear H0;Intros.
Case (classic (in_part (subtype_elt w) W')).
Intro;Red.
Exists (1).
Exists (!const_seq F (1) one).
Exists (!const_seq W' (1) (Build_subtype H2)).
Simpl.
(Apply Trans with (one mX (subtype_elt w));Auto with algebra).
Intro.
Generalize (!lin_dep_vs_span_lemma F V W').
Intros.
Generalize (H3 H0 (subtype_elt w) H2).
Intro.
Clear H3;Inversion_clear H4.
(Apply H3;Auto with algebra).
Qed.

(** - But of course we do have span(W')=span(W): *)
Lemma max_lin_indep_subset_has_same_span :
  (F:field;V:(vectorspace F);W,W':(part_set V))
    (max_lin_indep W' W) -> (span W)='(span W') in (part_set V).
Intros.
Simpl.
Red.
Simpl.
Split;Intros.
(Apply lin_comb_casting with W;Auto with algebra).
(Apply max_lin_indep_subset_generates_set;Auto with algebra).
Red in H.
Inversion_clear H.
Assert (included (span W') (span W)).
(Apply span_preserves_inclusion;Auto with algebra).
Change (in_part x (span W)).
Change (in_part x (span W')) in H0.
Red in H.
(Apply H;Auto with algebra).
Qed.

(** - The seq_set in this lemma is needed to transform seqs into sets: *)
Lemma seq_has_max_lin_indep_subseq : (F:field;V:(vectorspace F);n:Nat;v:(seq n V)) 
  (EXT k:Nat | (EXT w:(seq k V) | 
    (is_subseq w v) /\ (max_lin_indep (seq_set w) (seq_set v)))).
Induction n.
Intro.
Exists O.
Exists v.
Split.
EApply is_subseq_comp.
(Apply is_subseq_empty;Auto with algebra).
Auto with algebra.
Apply Refl.
Split.
Auto with algebra.
Split.
(Apply lin_indep_comp with (seq_set (empty_seq V));Auto with algebra).

(Apply lin_indep_comp with (empty V);Auto with algebra).
(Apply empty_lin_indep;Auto with algebra).
Intros;(Apply False_ind;Auto with algebra).

Clear n.
Intros.
Generalize (H (Seqtl v)).
Intro.
Clear H.
Inversion_clear H0.
Inversion_clear H.
Inversion_clear H0.
Assert (lin_dep (seq_set (head v);;x0))\/(lin_indep (seq_set (head v);;x0)).
Unfold lin_indep.
(Apply classic;Auto with algebra).
Case H0;Clear H0.
Intro.
Exists x.
Exists x0.
Split.
(Apply is_subseq_comp with x0 (hdtl v);Auto with algebra);Unfold hdtl.
(Apply is_subseq_of_tail;Auto with algebra).
Split.
Inversion_clear H1.
Red in H2.
Red;Intros.
Generalize (H2 x1 H1);Clear H2;Intro;Simpl in H2.
Inversion_clear H2.
NewDestruct x2.
Simpl.
Exists (Build_finiteT (lt_n_S index n in_range_prf)).
Auto.
Split.
Inversion_clear H1.
Inversion_clear H3.
(Apply H1;Auto with algebra).
Intro.
Intro.
Case (classic y='(head v)).
Intros.
(Apply lin_dep_comp with (seq_set (y;;x0));Auto with algebra).
(Apply lin_dep_comp with (seq_set ((head v);;x0));Auto with algebra).
Intros.
Assert (in_part y (seq_set (Seqtl v))).
Auto with algebra.
Inversion_clear H1.
Inversion_clear H7.
(Apply H8;Auto with algebra).

Intro.
Exists (S x).
Exists (head v);;x0.
Split;Try Split.
(Apply is_subseq_comp with ((head v);;x0) (hdtl v);Auto with algebra).
Unfold hdtl.
(Apply is_subseq_cons;Auto with algebra).
Red.
Intros.
Simpl in H2.
Inversion_clear H2.
NewDestruct x2.
NewDestruct index.
Simpl.
Exists (Build_finiteT (lt_O_Sn n)).
(Apply Trans with (head v);Auto with algebra).
Generalize (subseq_has_right_elements H (Build_finiteT (lt_S_n n0 x in_range_prf))).
Intro.
Inversion_clear H2.
Simpl.
NewDestruct x2.
Exists (Build_finiteT (lt_n_S??in_range_prf0)).
(Apply Trans with (x0 (Build_finiteT (lt_S_n n0 x in_range_prf)));Auto with algebra).
Split.
Auto.
Intro.
Case (classic y='(head v)).
Intros.
Absurd (in_part y (seq_set ((head v);;x0)));Auto.
Simpl.
Exists (Build_finiteT (lt_O_Sn x)).
Auto.
Intros.
Inversion_clear H1.
(Apply lin_dep_include with (union (seq_set x0) (single y));Auto with algebra).
Red.
Intros.
Simpl in H1.
Simpl.
Inversion_clear H1.
Inversion_clear H7.
NewDestruct x2.
Left.
Exists (Build_finiteT (lt_n_S ?? in_range_prf)).
(Apply Trans with (x0 (Build_finiteT in_range_prf));Auto with algebra);(Apply Ap_comp;Auto with algebra);Simpl;Auto.
Right;Auto.
Inversion_clear H6.
(Apply H7;Auto with algebra).
Change  (in_part y (seq_set (Seqtl v))).
(Apply seq_set_head_or_tail;Auto with algebra). 
Red;Red in H4;Intro;(Apply H4;Auto with algebra).
(Apply in_part_included with (seq_set x0);Auto with algebra).
Red.
Simpl.
Intros.
Inversion_clear H8.
NewDestruct x2.
Exists (Build_finiteT (lt_n_S??in_range_prf)).
(Apply Trans with (x0 (Build_finiteT in_range_prf));Auto with algebra);(Apply Ap_comp;Auto with algebra);Simpl;Auto.
Qed.
