(** * replacement_theorem.v *)
Set Implicit Arguments.
Require Export has_n_elements.
Require Export bases.
Require Export lin_dep_facts.

(** - %\intoc{\bf Theorem 1.10}% in this file, nothing else *)
Lemma replacement_theorem : (F:field;V:(vectorspace F);beta:(basis V);n:Nat)
  (has_n_elements n beta) ->
  (Sset:(part_set V)) (lin_indep Sset) ->
  (m:Nat) (le m n) -> (has_n_elements m Sset) ->

  (EXT S1:(part_set beta) | (has_n_elements (minus n m) S1) /\ 
                            (generates (union Sset (inject_subsets S1)) (full V))).
(* If you thought that was bad - the original formulation of this lemma said

Lemma replacement_theorem : (F:field;V:(vectorspace F);n:Nat;beta:(basis V);
  Hbeta:(has_n_elements n beta);m:Nat;Hmn:(le m n);
  Sset:(part_set V);HSset:(lin_indep Sset);H'Sset:(has_n_elements m Sset))
  (EXT S1:(part_set beta) | (has_n_elements (minus n m) S1) /\ 
                            (generates (union Sset (inject_subsets S1)))).

Anyways - hence first some renaming to get the original script running
*)

Intros.
Rename H into Hbeta.
Rename H0 into HSset.
Rename H1 into Hmn.
Rename H2 into H'Sset.
Generalize Dependent Sset.
Generalize Dependent m.
Induction m.
Intros.
Simpl in n.
Exists (full beta).
Split.
Replace (minus n O) with n;Auto with arith.
(Apply full_preserves_has_n_elements;Auto with algebra).
Red.
Elim (is_basis_prf beta).
Intros.
Red in H.
(Apply Trans with ((span beta)::(part_set?));Auto with algebra).
Apply Trans with ((span (inject_subsets (full beta)))::(part_set?)).
(Apply span_comp;Auto with algebra).
(Apply Trans with (union (empty?) (inject_subsets (full beta)));Auto with algebra).
(Apply span_comp;Auto with algebra).

Clear m;Intro m;Intros.
Generalize (n_element_subset_sequence H'Sset).
Intro.
Inversion_clear H0.
Rename x into ys.
Inversion_clear H1.
Assert (le m n);Auto with arith.
LetTac Sset':=(seq_set (Seqtl ys)).

Assert (lin_indep Sset').
(Apply lin_indep_include with Sset;Auto with algebra).
(Apply included_comp with(seq_set (Seqtl ys))  (seq_set ys);Auto with algebra). 
Red.
Simpl.
Intros.
Inversion_clear H3.
NewDestruct x0.
Exists (Build_finiteT (lt_n_S??in_range_prf)).
Assumption.

Assert (has_n_elements m Sset').
(Apply seq_set_n_element_subset;Auto with algebra).
Exists (Seqtl ys).
Split.
Auto with algebra.
(Apply Seqtl_preserves_distinct with v:=ys;Auto with algebra).

Generalize (H H1 Sset' H3 H4).
Intro.
Inversion_clear H5.
Rename x into XS.
Inversion_clear H6.
Generalize (n_element_subset_sequence H5).
Intro.
Inversion_clear H6.
Rename x into xs.
Inversion_clear H8.
Assert (generates (union (seq_set (Seqtl ys)) (seq_set (Map_embed xs))) (full V)).
(Apply generates_comp with (union Sset' (inject_subsets XS)) (full V);Auto with algebra).
(Apply union_comp;Auto with algebra).
(Apply Trans with (inject_subsets (seq_set xs));Auto with algebra).
(Apply inject_map_embed_seq_set;Auto with algebra).
Assert (generates (seq_set (Seqtl ys)++(Map_embed xs)) (full V)).
(Apply generates_comp with (union (seq_set (Seqtl ys)) (seq_set (Map_embed xs))) (full V);Auto with algebra).
Apply Sym.
Apply seq_set_concat_union.

Assert (EXT a:(seq m F) | (EXT b:(seq (minus n m) F) | (head ys)='(sum (mult_by_scalars a++b (Seqtl ys)++(Map_embed xs))))).
Assert (is_lin_comb (head ys) (seq_set (Seqtl ys)++(Map_embed xs))).
(Apply is_lin_comb_from_generates with (full V);Auto with algebra).
Generalize (lin_comb_condensed (Refl (seq_set (Seqtl ys)++(Map_embed xs))) H11).
Intro.
Inversion_clear H12.
Assert (sigT (seq m F) [a](sigT (seq (minus n m) F) [b]x='a++b)).
(Apply split_to_concat;Auto with algebra).
Inversion_clear X.
Exists x0.
Inversion_clear X0.
Exists x1.
(Apply Trans with (sum (mult_by_scalars x (Seqtl ys)++(Map_embed xs)));Auto with algebra).

Inversion_clear H11.
Rename x into As.
Inversion_clear H12.
Rename x into Bs.

Assert (EXT i:(fin (minus n m)) | ~(Bs i) =' (zero F)).
Apply NNPP.
Intro.
Assert (i:(fin (minus n m)))(Bs i)='(zero F).
Intro.
Apply NNPP.
Intro.
Apply H12.
Exists i;Auto with algebra.
Assert (head ys)='(sum (mult_by_scalars As (Seqtl ys))).
(Apply Trans with (sum (mult_by_scalars As++Bs (Seqtl ys)++(Map_embed xs)));Auto with algebra).
Apply Trans with (sum (mult_by_scalars As (Seqtl ys))++(mult_by_scalars Bs (Map_embed xs))).
Unfold mult_by_scalars.
(Apply sum_comp;Auto with algebra).
Apply Trans with (sum (mult_by_scalars As (Seqtl ys))++(const_seq (minus n m) (zero V))).
Unfold mult_by_scalars.
Apply sum_comp.
(Apply concat_comp;Auto with algebra).
Simpl.
Red.
Simpl.
Intro i.
(Apply Trans with (zero F)mX(subtype_elt (xs i));Auto with algebra).
(Apply Trans with (sum (mult_by_scalars As (Seqtl ys)))+'(zero V);Auto with algebra).
(Apply Trans with (sum (mult_by_scalars As (Seqtl ys)))+'(sum (const_seq (minus n m) (zero V)));Auto with algebra).
Assert (lin_indep (seq_set ys)).
(Apply lin_indep_comp with Sset;Auto with algebra).
Red in H15.
Unfold lin_dep in H15.
Apply H15.
Exists m.
Exists (min one);;As.
Exists (seq_set_seq ys).
Split.
Red;Red;Intros;Red in H2;Red in H2.
Apply (H2 i j H16).
Simpl in H17.
Red in H17.
Simpl in H17.
Auto.
Split.
Intro.
Simpl in H16.
Red in H16.
Generalize (H16 (Build_finiteT (lt_O_Sn m))).
Simpl.
Intro.
Assert one='(zero F).
Apply min_inj.
(Apply Trans with (zero F);Auto with algebra).
Generalize H18.
Elim F.
Intros Fr Fd;Elim Fd.
Simpl.
Tauto.
Apply Trans with (sum (mult_by_scalars ((min one);;As) ys)).
(Apply sum_comp;Auto with algebra).

Apply Trans with (sum (mult_by_scalars ((min one);;As) (hdtl ys))).
Unfold mult_by_scalars;(Apply sum_comp;Auto with algebra);(Apply pointwise_comp;Auto with algebra).
Unfold mult_by_scalars hdtl.
(Apply Trans with (sum ((uncurry (MODULE_comp 1!F 2!V)) (couple (min one) (head ys)));; (pointwise (uncurry (MODULE_comp 1!F 2!V)) As (Seqtl ys)));Auto with algebra).
(Apply Trans with  ((uncurry (MODULE_comp 1!F 2!V)) (couple (min one) (head ys))) +' (sum (pointwise (uncurry (MODULE_comp 1!F 2!V)) As (Seqtl ys)));Auto with algebra).
(Apply Trans with ((min one) mX (head ys))+'(sum (pointwise (uncurry (MODULE_comp 1!F 2!V)) As (Seqtl ys)));Auto with algebra).
(Apply Trans with (min (one mX(head ys)))+'(sum (pointwise (uncurry (MODULE_comp 1!F 2!V)) As (Seqtl ys)));Auto with algebra).
(Apply Trans with (min (head ys))+'(sum (pointwise (uncurry (MODULE_comp 1!F 2!V)) As (Seqtl ys)));Auto with algebra).
(Apply Trans with (min (sum (mult_by_scalars As (Seqtl ys))))+'(sum (pointwise (uncurry (MODULE_comp 1!F 2!V)) As (Seqtl ys)));Auto with algebra).

Inversion_clear H12.
Rename x into i.
Generalize (!rewrite_lin_comb_term F V).
Intro.
LetTac asbs:=As++Bs.
LetTac ys'xs:=(Seqtl ys)++(Map_embed xs).

Generalize (H12 ? (min one);;asbs (head ys);;ys'xs).
Clear H12;Intro.
NewDestruct i.
Rename index into i.
Rename in_range_prf into ip.
LetTac i_AsBs:=(Build_finiteT (lt_n_S ?? (lt_reg_l ?? m ip))).
Assert ~((min one);;asbs i_AsBs) =' (zero F). 
Simpl.
Unfold i_AsBs.
Unfold asbs.
Intro.
Apply H13.
(Apply Trans with  (As++Bs
          (Build_finiteT
            (lt_S_n (plus m i) (plus m (minus n m))
              (lt_n_S (plus m i) (plus m (minus n m))
                (lt_reg_l i (minus n m) m ip)))));Auto with algebra).
Generalize (H12 ? H14);Clear H12 H14;Intro.
Assert  (sum (mult_by_scalars ((min one);;asbs) ((head ys);;ys'xs)))
          =' (zero V).
Apply Trans with ((min one) mX (head ys))+'(sum (mult_by_scalars asbs ys'xs)).
(Apply Trans with ((uncurry (MODULE_comp 2!V)) (couple (min one) (head ys)))+'(sum (mult_by_scalars asbs ys'xs));Auto with algebra).
(Apply Trans with (sum ((uncurry (MODULE_comp 2!V)) (couple (min one) (head ys)));;(mult_by_scalars asbs ys'xs));Auto with algebra).
Unfold mult_by_scalars.
Auto with algebra.
(Apply Trans with (min (head ys))+'(head ys);Auto with algebra).
(Apply SGROUP_comp;Auto with algebra).
(Apply Trans with (min (one mX (head ys)));Auto with algebra).
Generalize (H12 H14);Clear H12 H14;Intro.
LetTac i_Bs:=(Build_finiteT ip).
Assert (Map_embed xs i_Bs)='((head ys);;ys'xs i_AsBs).
Simpl.
Unfold i_AsBs.
Unfold ys'xs.
(Apply Trans with (Map_embed xs i_Bs);Auto with algebra).
(Apply Sym;Auto with algebra).
Generalize concat_second_part;Intro p.
Unfold i_Bs.
Apply p.
Assert (Map_embed xs i_Bs) ='((field_inverse ((min one);;asbs i_AsBs))
                  mX (min (sum
                            (omit
                              (mult_by_scalars ((min one);;asbs)
                                ((head ys);;ys'xs)) i_AsBs)))).
(Apply Trans with  ((head ys);;ys'xs i_AsBs);Auto with algebra).
Clear H12.
LetTac asbs' := (pointwise (uncurry (RING_comp 1!F)) (const_seq ? (field_inverse ((min one);;asbs i_AsBs))) (pointwise (uncurry (RING_comp 1!F)) (const_seq ? (min one)) (omit (min one);;asbs i_AsBs))).
LetTac ysxs' := (omit (head ys);;ys'xs i_AsBs).
Assert (in_part  (Map_embed xs i_Bs) (span (seq_set ysxs'))).
Simpl.
Red.
Exists (plus m (minus n m)).
Exists asbs'.
Assert (i:(fin?))(in_part (ysxs' i) (seq_set ysxs')).
Intro.
Unfold ysxs'.
Simpl.
Exists i0.
Auto with algebra.
Exists (cast_map_to_subset H12).
Apply Trans with (sum (mult_by_scalars asbs' ysxs')).
2:Unfold mult_by_scalars;Apply sum_comp;Apply toMap;(Apply pointwise_comp;Auto with algebra).
(Apply Trans with (Map_embed xs i_Bs);Auto with algebra).
(Apply Trans with ((field_inverse ((min one);;asbs i_AsBs))
                  mX (min (sum
                            (omit
                              (mult_by_scalars ((min one);;asbs)
                                ((head ys);;ys'xs)) i_AsBs))));Auto with algebra).
(Apply Trans with ((field_inverse ((min one);;asbs i_AsBs))
        mX (min (one mX (sum
                  (omit
                    (mult_by_scalars ((min one);;asbs) ((head ys);;ys'xs))
                    i_AsBs)))));Auto with algebra).
(Apply Trans with ((field_inverse ((min one);;asbs i_AsBs))
        mX ((min one) mX (sum
                  (omit
                    (mult_by_scalars ((min one);;asbs) ((head ys);;ys'xs))
                    i_AsBs))));Auto with algebra).
(Apply Trans with ((field_inverse ((min one);;asbs i_AsBs))
        mX (sum (mult_by_scalars (const_seq ? (min one))
                  (omit  (mult_by_scalars ((min one);;asbs) ((head ys);;ys'xs))  i_AsBs))));Auto with algebra).
(Apply Trans with (sum (mult_by_scalars (const_seq ? (field_inverse ((min one);;asbs i_AsBs))) (mult_by_scalars (const_seq ? (min one))
                  (omit
                    (mult_by_scalars ((min one);;asbs) ((head ys);;ys'xs))
                    i_AsBs))));Auto with algebra).
Apply Trans with (sum (mult_by_scalars (const_seq ? (field_inverse ((min one);;asbs i_AsBs))) (mult_by_scalars (const_seq ? (min one)) (mult_by_scalars (omit ((min one);;asbs) i_AsBs) (omit (head ys);;ys'xs i_AsBs))))).
(Apply sum_comp;Auto with algebra).
Apply sum_comp.
Unfold asbs' ysxs'.
Apply Trans with (mult_by_scalars (const_seq (plus m (minus n m)) (field_inverse ((min one);;asbs i_AsBs))) (mult_by_scalars (pointwise (uncurry (RING_comp 1!F)) (const_seq (plus m (minus n m)) (min one)) (omit ((min one);;asbs) i_AsBs)) (omit ((head ys);;ys'xs) i_AsBs))).
Apply toMap.
(Apply mult_by_scalars_comp;Auto with algebra).
Apply toMap.
(Apply pointwise_module_assoc;Auto with algebra).

Assert (minus n m)=(S (minus n (S m))).
Transitivity (minus (S n) (S m));Auto.
Symmetry;Auto with arith.

Cut (included (seq_set ys'xs) (span (seq_set ysxs'))).
Intros.
Assert (included (span (seq_set ys'xs)) (span (seq_set ysxs'))).
(Apply span_smallest_subspace_containing_subset;Auto with algebra).
Assert (included (full V) (span (seq_set ysxs'))).
(Apply included_comp with ((span (seq_set ys'xs))::(part_set?)) ((span (seq_set ysxs'))::(part_set?));Auto with algebra).

Exists (seq_set (omit (cast_seq xs H16) (cast_fin i_Bs H16))).
Split.
Red.
Exists (seq_set_seq  (omit (cast_seq xs H16) (cast_fin i_Bs H16))).
Split.
(Apply included_antisym;Auto with algebra).
Red.
Intros.
Clear H20.
Elim x.
Intros x' x'p.
Unfold in_part.
Inversion_clear x'p.
Exists x0.
Simpl.
Red.
(Apply Trans with (subtype_elt (omit (cast_seq xs H16) (cast_fin i_Bs H16) x0));Auto with algebra).
(Apply seq_set_seq_preserves_distinct;Auto with algebra).
Red.
Apply Trans with ((span (seq_set ysxs'))::(part_set?)).
2:(Apply included_antisym;Auto with algebra).
(Apply span_comp;Auto with algebra).
Apply Trans with (union (seq_set ys) (inject_subsets (seq_set (omit xs i_Bs)))).

Apply Trans with (union Sset (inject_subsets (seq_set (omit xs i_Bs)))).
(Apply union_comp;Auto with algebra).
(Apply inject_subsets_comp;Auto with algebra).
Apply seq_equal_seq_set.
(Apply seq_equal_omit;Auto with algebra).

(Apply union_comp;Auto with algebra).


Apply Trans with (seq_set ys++(Map_embed (omit xs i_Bs))).
Apply Sym.
Apply Trans with (union (seq_set ys) (seq_set (Map_embed (omit xs i_Bs)))).
Apply seq_set_concat_union.
(Apply union_comp;Auto with algebra).
Apply Sym.
Apply inject_map_embed_seq_set.
Unfold ysxs' ys'xs.
(Apply Trans with (seq_set (omit ys++(Map_embed xs) i_AsBs));Auto with algebra).
(Apply Trans with (seq_set ys++(omit (Map_embed xs) i_Bs));Auto with algebra).
Change (eq_part (seq_set ys++(omit (Map_embed xs) i_Bs)) (seq_set (omit ys++(Map_embed xs) i_AsBs))).
Split;Intros.
Inversion_clear H20.
Change (EXT i:(fin?) | x='(omit  ys++(Map_embed xs) i_AsBs i)).
Assert (plus (S m) (pred (minus n m)))=(plus m (minus n m)).
Rewrite H16.
Simpl.
Auto with arith.
Exists (cast_fin x0 H20).
(Apply Trans with (ys++(omit (Map_embed xs) i_Bs) x0);Auto with algebra).
Generalize seq_equal_equal_elements.
Intro p;(Apply p;Auto with algebra).
Generalize omit_concat_second_part'.
Intro.
Apply seq_equal_symm.
Unfold i_AsBs i_Bs.
Generalize (H22???ys(Map_embed xs));Clear H22;Intro.
Generalize (H22?ip(lt_n_S (plus m i) (plus m (minus n m))
           (lt_reg_l i (minus n m) m ip)));Clear H22;Intro.
Apply H22.
Transitivity (plus m (S (pred (minus n m)))).
Apply plus_Snm_nSm.
Simpl.
(Apply (f_equal2???plus);Auto with algebra).
Symmetry.
(Apply S_pred with i;Auto with algebra).
NewDestruct x0.
Simpl.
Auto.

LApply (seq_equal_seq_set 4!(omit ys++(Map_embed xs) i_AsBs) 5!ys++(omit (Map_embed xs) i_Bs)).
Intro.
Change (eq_part (seq_set (omit ys++(Map_embed xs) i_AsBs)) (seq_set ys++(omit (Map_embed xs) i_Bs))) in H21.
Red in H21.
Generalize (H21 x);Intro p;Inversion_clear p;Auto with algebra.
Generalize omit_concat_second_part'.
Intro.
Unfold i_AsBs i_Bs.
Generalize (H21???ys(Map_embed xs));Clear H21;Intro.
Generalize (H21?ip(lt_n_S (plus m i) (plus m (minus n m))
           (lt_reg_l i (minus n m) m ip)));Clear H21;Intro.
Apply H21.
Transitivity (plus m (S (pred (minus n m)))).
Apply plus_Snm_nSm.
Simpl.
(Apply (f_equal2???plus);Auto with algebra).
Symmetry.
(Apply S_pred with i;Auto with algebra).



Red.
Intros.
Simpl in H17.
Elim H17;Clear H17;Intros x0.
Elim x0;Clear x0;Intros.
Rename H17 into H18.

Rename index into ix.
Case (le_or_lt m ix).

Intro.
Assert (EXT q:Nat | ix=(plus m q)).
Exists (minus ix m).
(Apply le_plus_minus;Auto with algebra).
Elim H19;Clear H19;Intro;Intro H20.
Rename x0 into ix_xs.
Assert (lt ix_xs (minus n m)).
Clear H18.
Rewrite H20 in in_range_prf.
(Apply simpl_lt_plus_l with m;Auto with algebra).

Assert x='(Map_embed xs (Build_finiteT H19)).
(Apply Trans with (ys'xs (Build_finiteT in_range_prf));Auto with algebra).
Unfold ys'xs.
Generalize concat_second_part.
Intro p.
Generalize (p???(Seqtl ys)(Map_embed xs)).
Clear p;Intro.

Assert (lt (plus m ix_xs)(plus m (minus n m))).
Rewrite <- H20.
Auto.

(Apply Trans with ((Seqtl ys)++(Map_embed xs) (Build_finiteT H22));Auto with algebra).

Case (classic (i_Bs::(fin?)) =' (Build_finiteT H19));Intros.
(Apply in_part_comp_l with (Map_embed xs (Build_finiteT H19));Auto with algebra).
(Apply in_part_comp_l with (Map_embed xs i_Bs);Auto with algebra).

Assert (lt (plus m ix_xs)(plus m (minus n m))).
Rewrite <- H20.
Auto.

(Apply in_part_comp_r with ((span_ind (seq_set ysxs'))::(part_set?));Auto with algebra).
Apply in_part_included with (seq_set ysxs').
2:(Apply included_comp with (seq_set ysxs') ((span (seq_set ysxs'))::(part_set?));Auto with algebra).
(Apply in_part_included with (seq_set (omit (Map_embed xs) i_Bs));Auto with algebra).

Generalize (omit_removes' (Map_embed xs) H22).
Intro.
Inversion_clear X.
(Apply in_part_comp_l with (Map_embed xs (Build_finiteT H19));Auto with algebra).
Simpl.
Exists x0.
Auto.

(Apply included_comp with (seq_set (omit (Map_embed xs) i_Bs)) (seq_set ys++(omit (Map_embed xs) i_Bs));Auto with algebra).

(Apply seq_equal_seq_set;Auto with algebra).
Apply seq_equal_trans with w:= (omit ys++(Map_embed xs) i_AsBs).
Apply seq_equal_symm.
Unfold i_AsBs i_Bs.
Generalize omit_concat_second_part'.
Intro p.
Generalize (p???ys(Map_embed xs)).
Clear p;Intro p.
Generalize (p?ip);Clear p;Intro p.
Generalize (p (lt_n_S (plus m i) (plus m (minus n m)) (lt_reg_l i (minus n m) m ip))).
Intro q;Apply q.
Clear p q.
Simpl.
Rewrite H16.
Simpl.
Transitivity (plus (S m) (minus n (S m)));Auto with arith.
Apply plus_Snm_nSm.
Unfold ysxs'.
Unfold ys'xs.
Apply Map_eq_seq_equal.
(Apply omit_comp;Auto with algebra).

(Apply included_comp with (seq_set (omit (Map_embed xs) i_Bs)) (union (seq_set ys) (seq_set (omit (Map_embed xs) i_Bs)));Auto with algebra).
(Apply Sym;Auto with algebra).
(Apply seq_set_concat_union;Auto with algebra).

Intro.
(Apply in_part_comp_r with (span_set (seq_set ys++(omit (Map_embed xs) i_Bs)));Auto with algebra).

Assert x='(Seqtl ys (Build_finiteT H17)).
Generalize concat_first_part.
Intro.
(Apply Trans with (ys'xs (Build_finiteT in_range_prf));Auto with algebra); Unfold ys'xs.
(Apply H19;Auto with algebra).

Assert (in_part x (seq_set ys++(omit (Map_embed xs) i_Bs))).
(Apply in_part_comp_r with (union (seq_set ys) (seq_set (omit (Map_embed xs) i_Bs)));Auto with algebra).
Simpl.
Left.
Exists (Build_finiteT (lt_n_S??H17)).
(Apply Trans with (Seqtl ys (Build_finiteT H17));Auto with algebra).
(Apply Sym;Auto with algebra).
(Apply seq_set_concat_union;Auto with algebra).

(Apply in_part_comp_r with ((span_ind (seq_set ys++(omit (Map_embed xs) i_Bs)))::(part_set?));Auto with algebra).
Red in H20.
Exists (Immediately (Build_subtype H20)).
Simpl.
Auto with algebra.
(Apply Trans with ((span  (seq_set ys++(omit (Map_embed xs) i_Bs)))::(part_set?));Auto with algebra).

(Apply Trans with (span_set (seq_set (omit ((head ys);;ys'xs) i_AsBs)));Auto with algebra).
Generalize span_comp.
Intro p;Simpl in p.
Change (eq_part (span_set (seq_set ys++(omit (Map_embed xs) i_Bs))) (span_set (seq_set (omit ((head ys);;ys'xs) i_AsBs)))).
Apply p.
(Apply seq_equal_seq_set;Auto with algebra).
Generalize omit_concat_second_part'.
Intro.
Unfold i_AsBs i_Bs.
Generalize (H19???ys(Map_embed xs));Clear H19;Intro.
Generalize (H19?ip(lt_n_S (plus m i) (plus m (minus n m))
           (lt_reg_l i (minus n m) m ip)));Clear H19;Intro.
Apply seq_equal_symm.
Apply H19.
Transitivity (plus m (S (pred (minus n m)))).
Apply plus_Snm_nSm.
Simpl.
(Apply (f_equal2???plus);Auto with algebra).
Symmetry.
(Apply S_pred with i;Auto with algebra).
Qed.
