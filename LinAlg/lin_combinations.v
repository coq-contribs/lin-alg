(** * lin_combinations.v *)
Set Implicit Arguments.
Require Export distinct.
Require Export distribution_lemmas.
Require Export sums2.
Require Export omit_facts.
Require Export cast_between_subsets.

Section lin_dep_def.

(** %\tocdef{is\_lin\_comb}% *)
Definition is_lin_comb [F:field;V:(vectorspace F);x:V;S:(part_set V)] := 
  (EXT n:Nat | (EXT a:(seq n F) | (EXT v:(seq n S) |
     x=' (sum (mult_by_scalars a (Map_embed v))) ))).

Lemma is_lin_comb_comp : (F:field;V:(vectorspace F);x,y:V;S,T:(part_set V))
  S='T -> x='y -> (is_lin_comb x S)->(is_lin_comb y T).
Intros.
Assert (is_lin_comb x T).
Red;Red in H1.
Inversion_clear H1.
Exists x0.
Inversion_clear H2.
Exists x1.
Inversion_clear H1.
Exists (Map_to_equal_subsets H x2).
(Apply Trans with (sum (mult_by_scalars x1 (Map_embed x2)));Auto with algebra).
Red.
Red in H2.
Inversion H2.
Inversion H3.
Inversion H4.
Exists x0.
Exists x1.
Exists x2.
(Apply Trans with x;Auto with algebra).
Qed.

Hints Resolve is_lin_comb_comp : algebra.

(** - Being a linear combination is in fact a setoid-Predicate. *)
Definition is_lin_comb_pred : (F:field;V:(vectorspace F))(part_set V)->(Predicate V).
Intros.
Apply (Build_Predicate 2![x:V](is_lin_comb x X)).
Red.
Intros.
(Apply is_lin_comb_comp with x X;Auto with algebra).
Defined.
End lin_dep_def.


Section condensing.

(** - Easy to see but not easy to prove: if $x=\sum_{i=1}^n a_ib_i$ then in fact
 $x=\sum_{i=1}^{n'} a_ib'_i$ where all $b'_i$ are distinct vectors.*)

Lemma lin_comb_with_distinct_vectors : (F:field;V:(vectorspace F);x:V;B:(part_set V))
  (is_lin_comb x B)
    ->(EXT n:Nat | (EXT a:(seq n F) | (EXT v:(seq n B) |
       x='(sum (mult_by_scalars a (Map_embed v)))/\(distinct v)))).
Intros.
Red in H.
Inversion_clear H.
Generalize x0 H0;Clear H0 x0.
Intro n;Induction n.
Intros.
Inversion_clear H0.
Inversion_clear H.
Exists O.
Exists x0.
Exists x1.
Split.
Auto.
Red.
Intros.
(Apply False_ind;Auto with algebra).
Intros.
Inversion_clear H0.
Inversion_clear H.
Assert (distinct x1)\/~(distinct x1).
Apply classic.
Case H.
Intro.
Exists (S n).
Exists x0;Exists x1;Split;Auto.
Intro.
Unfold distinct in H1.
Assert (EXT i:(fin (S n)) | (EXT j:(fin (S n)) |~i='j/\ (x1 i)='(x1 j))).
Apply NNPP.
Red.
Red in H1.
Intros;Apply H1.
Intros.
Red;Red in H2.
Intro;Apply H2.
Exists i;Exists j;Auto.
Inversion_clear H2;Inversion_clear H3.
Inversion_clear H2.
Apply Hrecn.
Exists (omit (modify_seq x0 x2 (x0 x2)+'(x0 x3)) x3).
Exists (omit x1 x3).
Apply Trans with (sum
          (mult_by_scalars
            (omit (modify_seq x0 x2 ((x0 x2) +' (x0 x3))) x3)
            (omit (Map_embed x1) x3))).
(Apply Trans with (sum (omit (mult_by_scalars (modify_seq x0 x2 ((x0 x2) +' (x0 x3)))(Map_embed x1)) x3));Auto with algebra).
(Apply Trans with (sum (mult_by_scalars (modify_seq x0 x2 ((x0 x2) +' (x0 x3)))(Map_embed x1)))+'(min ((mult_by_scalars (modify_seq x0 x2 ((x0 x2) +' (x0 x3)))(Map_embed x1)) x3));Auto with algebra).
Apply Trans with (sum (mult_by_scalars (modify_seq x0 x2 ((x0 x2) +' (x0 x3)))(Map_embed x1)))+'(min ((x0 x3)mX((Map_embed x1) x3))).
(Apply Trans with ((sum (modify_seq (mult_by_scalars x0 (Map_embed x1)) x2 (((x0 x2)+'(x0 x3))mX(Map_embed x1 x2))))+'(min((x0 x3)mX(Map_embed x1 x3))));Auto with algebra).

(Apply Trans with (sum (mult_by_scalars x0 (Map_embed x1)))+'(min ((mult_by_scalars x0 (Map_embed x1)) x2)) +' (((x0 x2) +' (x0 x3)) mX (Map_embed x1 x2)) +' (min ((x0 x3) mX (Map_embed x1 x3)));Auto with algebra).

Apply Trans with (sum (mult_by_scalars x0 (Map_embed x1)))+'((min (mult_by_scalars x0 (Map_embed x1) x2)) +' (((x0 x2) +' (x0 x3)) mX (Map_embed x1 x2))+' (min ((x0 x3) mX (Map_embed x1 x3)))).
2:(Apply Trans with ((sum (mult_by_scalars x0 (Map_embed x1)))
        +' (((min (mult_by_scalars x0 (Map_embed x1) x2))
                 +' (((x0 x2) +' (x0 x3)) mX (Map_embed x1 x2)))))+'(min ((x0 x3) mX (Map_embed x1 x3)));Auto with algebra).

(Apply Trans with (sum (mult_by_scalars x0 (Map_embed x1)));Auto with algebra).
(Apply Trans with (sum (mult_by_scalars x0 (Map_embed x1)))+'(zero V);Auto with algebra).
(Apply SGROUP_comp;Auto with algebra).
Unfold mult_by_scalars.
Simpl.
Apply GROUP_reg_right with ((x0 x3) mX (subtype_elt (x1 x3))).
(Apply Trans with ((x0 x3) mX (subtype_elt (x1 x3)));Auto with algebra).
(Apply Trans with ((min ((x0 x2) mX (subtype_elt (x1 x2)))) +' (((x0 x2) +' (x0 x3)) mX (subtype_elt (x1 x2))))+'((min ((x0 x3) mX (subtype_elt (x1 x3)))) +' ((x0 x3) mX (subtype_elt (x1 x3))));Auto with algebra).
(Apply Trans with ((min ((x0 x2) mX (subtype_elt (x1 x2)))) +' (((x0 x2) +' (x0 x3)) mX (subtype_elt (x1 x2))))+'(zero V);Auto with algebra).
(Apply Trans with ((min ((x0 x2) mX (subtype_elt (x1 x2)))) +' (((x0 x2) +' (x0 x3)) mX (subtype_elt (x1 x2))));Auto with algebra).
(* mind the change x3->x2 *)
(Apply Trans with  ((x0 x3) mX (subtype_elt (x1 x2)));Auto with algebra).
(Apply Trans with ((min (x0 x2)) mX (subtype_elt (x1 x2))) +' (((x0 x2) +' (x0 x3)) mX (subtype_elt (x1 x2)));Auto with algebra).
(Apply Trans with ((min (x0 x2))+'((x0 x2)+'(x0 x3)))mX(subtype_elt (x1 x2));Auto with algebra).
(Apply MODULE_comp;Auto with algebra).
(Apply Trans with (((min (x0 x2))+'(x0 x2))+'(x0 x3));Auto with algebra).
(Apply Trans with (zero F)+'(x0 x3);Auto with algebra).

(Apply SGROUP_comp;Auto with algebra).
(Apply GROUP_comp;Auto with algebra).
Unfold mult_by_scalars.
(Apply Trans with ((modify_seq x0 x2 ((x0 x2) +' (x0 x3)) x3)mX(Map_embed x1 x3));Auto with algebra).
(Apply MODULE_comp;Auto with algebra).
Apply Sym.
(Apply modify_seq_modifies_one_elt;Auto with algebra).

Unfold mult_by_scalars.
Apply sum_comp.
Apply toMap.
(Apply pointwise_comp;Auto with algebra).
Change    (omit (Map_embed x1) x3) =' (Map_embed (omit x1 x3)).
Apply omit_Map_embed.
Qed.

(** - Similarly easy to see, not easy to prove: if $B=\{b_0...b_{n-1}\}$, then
 any linear combination $x=\sum_{i=0}^{p-1} a_i b_{k_i}$ can be written as
 $x=\sum_{i=01}^{n-1} a_ib_i$*)

Lemma lin_comb_condensed : (F:field;V:(vectorspace F);B:(part_set V);n:Nat;b:(seq n V))
  B='(seq_set b) -> (x:V)(is_lin_comb x B)
    -> (EXT a:(seq n F) | x='(sum (mult_by_scalars a b))).
Intros.
Red in H0.
Inversion_clear H0.
Generalize x H1;Clear H1 x.
NewInduction x0.
Intros.
Exists (const_seq n (zero F)).
Inversion_clear H1.
Inversion_clear H0.
Simpl in H1.
(Apply Trans with (zero V);Auto with algebra).
(Apply Trans with (sum (const_seq n (zero V)));Auto with algebra).
Apply Sym.
(Apply sum_of_zeros;Auto with algebra).
Unfold const_seq.
Apply sum_comp.
Intro;Simpl;Auto with algebra.

Intros.
Inversion_clear H1.
Inversion_clear H0.
Assert (EXT i:(fin n) | (B (head x2))='(b i)).
Simpl in H.
Red in H.
Simpl in H.
Generalize (H (B (head x2)));Intros (p,q).
(Apply p;Auto with algebra).
(Apply in_part_comp_l with (subtype_elt (head x2));Auto with algebra).
Inversion_clear H0.
Assert x='(head x1)mX(B (head x2))+'(sum (mult_by_scalars (Seqtl x1) (Map_embed (Seqtl x2)))).
(Apply Trans with (sum (mult_by_scalars x1 (Map_embed x2)));Auto with algebra).
Apply Trans with (sum (mult_by_scalars (hdtl x1) (Map_embed (hdtl x2)))).
Unfold hdtl mult_by_scalars.
Apply sum_comp.
Unfold head.
Apply toMap.
(Apply pointwise_comp;Auto with algebra).
Unfold hdtl.
(Apply Trans with (sum ((uncurry (MODULE_comp 2!V)) (couple (head x1) (B (head x2))));;(mult_by_scalars (Seqtl x1) (Map_embed (Seqtl x2))));Auto with algebra).

Assert (EXT a:(seq x0 F) | (EXT v:(seq x0 B) | x+'(min((head x1) mX (B (head x2)))) =' (sum (mult_by_scalars a (Map_embed v))))).
Exists (Seqtl x1).
Exists (Seqtl x2).
(Apply Trans with (((head x1) mX (B (head x2))) +' (sum (mult_by_scalars (Seqtl x1) (Map_embed (Seqtl x2)))))+' (min ((head x1) mX (B (head x2))));Auto with algebra).
(Apply Trans with ((sum (mult_by_scalars (Seqtl x1) (Map_embed (Seqtl x2))))+' ((head x1) mX (B (head x2)))) +' (min ((head x1) mX (B (head x2))));Auto with algebra).
(Apply Trans with (sum (mult_by_scalars (Seqtl x1) (Map_embed (Seqtl x2))))+' (((head x1) mX (B (head x2))) +' (min ((head x1) mX (B (head x2)))));Auto with algebra).
(Apply Trans with (sum (mult_by_scalars (Seqtl x1) (Map_embed (Seqtl x2))))+'(zero V);Auto with algebra).
Generalize (IHx0?H3).
Intro.
Inversion_clear H4.
Exists (modify_seq x4 x3 (x4 x3)+'(head x1)).
(Apply Trans with (sum (modify_seq (mult_by_scalars x4 b) x3 ((x4 x3)+'(head x1))mX(b x3)));Auto with algebra).
Apply Trans with ((sum (mult_by_scalars x4 b))+'(min ((mult_by_scalars x4 b) x3)))+'(((x4 x3) +' (head x1)) mX (b x3)).
2:(Apply Sym;Auto with algebra).

(Apply Trans with (x +' (min ((head x1) mX (B (head x2))))) +' (min (mult_by_scalars x4 b x3))
             +' (((x4 x3) +' (head x1)) mX (b x3));Auto with algebra).
Unfold mult_by_scalars.
Simpl.
(Apply Trans with ((x +' (min ((head x1) mX (subtype_elt (head x2)))))
              +' (min ((x4 x3) mX (b x3))))
             +' (((x4 x3)mX (b x3))+'((head x1)mX(b x3)));Auto with algebra).
(Apply Trans with (x +' (min ((head x1) mX (subtype_elt (head x2)))))+'((min ((x4 x3) mX (b x3))) +' (((x4 x3) mX (b x3)) +' ((head x1) mX (b x3))));Auto with algebra).
(Apply Trans with (x +' (min ((head x1) mX (subtype_elt (head x2)))))+'(((min ((x4 x3) mX (b x3))) +' ((x4 x3)mX (b x3)))+'((head x1)mX(b x3)));Auto with algebra).
(Apply Trans with (x +' (min ((head x1) mX (subtype_elt (head x2)))))+'((zero V)+'((head x1)mX(b x3)));Auto with algebra).
(Apply Trans with (x +' (min ((head x1) mX (subtype_elt (head x2)))))+'((head x1)mX(b x3));Auto with algebra).
(Apply Trans with (x +' (min ((head x1) mX (subtype_elt (head x2)))))+'((head x1)mX(subtype_elt (head x2)));Auto with algebra).
(Apply Trans with x +' ((min ((head x1) mX (subtype_elt (head x2))))+'((head x1)mX(subtype_elt (head x2))));Auto with algebra).
(Apply Trans with x+'(zero V);Auto with algebra).
Qed.




End condensing.

