(** %\subsection*{ support :  counting\_elements.v }%*)
Set Implicit Arguments.
Require Export Diff.
Require Export Singleton.
Require Export has_n_elements.
Require Export Union.
Require Export const.
(** - Once we have has_n_elements, it would seem to be easy to define
 has_at_least_n_elements and has_at_most_n_elements. But one has to take a little
 care. We could not just say, e.g. [
 
Definition has_at_least_n_elements := ]
[    [n:nat;A:Setoid](EXT m:nat | (le n m) /\ (has_n_elements m A)).

 ] since the set may be infinite, and then there is no such m to be found.

 - But we may adapt the definition of has_n_elements slightly. It said that we can
 make a sequence [v] of length [n] with all elements distinct---[(distinct v)];
 covering the whole set---[(seq_set v)='(full v)]. Now we just drop this last
 requirement so we only need to point out a sequence of $n$ different elements:

 %\label{hasatleastnelements}% *)

Definition has_at_least_n_elements := [n:Nat;A:Setoid](EXT v:(seq n A) | (distinct v)).

(** - Note that, contrarily, we may not just drop the other requirement to obtain 

[Definition has_at_most_n_elements_wrong := 
    [n:nat;A:Setoid](EXT v:(seq n A) | (full A)='(seq_set v)).]

 since this doesn't work out well for empty sets: it has at most n elements for any n,
 but with this definition we'd need to exhibit an n-length sequence, which we can't do
 for $n>0$.*)

Definition has_at_most_n_elements := [n:Nat;A:Setoid](EXT m:nat | (le m n)/\(has_n_elements m A)).

Lemma has_at_most_n_elements_comp : (A:Setoid;n,m:Nat;B,C:(part_set A))
  (has_at_most_n_elements n B) -> B='C -> n='m -> (has_at_most_n_elements m C).
Intros.
Red.
Red in H.
Inversion_clear H.
Rename x into Bsize.
Inversion_clear H2.
Exists Bsize.
Split.
Generalize (eq_ind ?? [n](le Bsize n) H ? H1).
Auto.
(Apply has_n_elements_comp with Bsize B;Auto with algebra).
Qed.

Lemma has_at_least_n_elements_comp : (A:Setoid;n,m:Nat;B,C:(part_set A))
  (has_at_least_n_elements n B) -> B='C -> n='m -> (has_at_least_n_elements m C).
Intros.
Rewrite <- H1.
Red.
Red in H.
Inversion_clear H.
Rename x into Bseq.
Exists (Map_to_equal_subsets H0 Bseq).
Red;Intros;Intro;Red in H2;(Apply (H2 i j);Auto with algebra).
Simpl.
Red.
(Apply Trans with (subtype_elt (Bseq i));Auto with algebra).
(Apply Trans with (subtype_elt (Bseq j));Auto with algebra).
(Apply Trans with (subtype_elt (Map_to_equal_subsets H0 Bseq i));Auto with algebra).
(Apply Trans with (subtype_elt (Map_to_equal_subsets H0 Bseq j));Auto with algebra).
Qed.

Lemma has_n_elements_then_has_at_least_n_elements : (A:Setoid;n:Nat)
  (has_n_elements n A) -> (has_at_least_n_elements n A).
Intros.
Inversion_clear H.
Exists x.
Inversion_clear H0;Auto.
Qed.

Lemma has_n_elements_then_has_at_most_n_elements : (A:Setoid;n:Nat)
  (has_n_elements n A) -> (m:Nat) (le n m)->(has_at_most_n_elements m A).
Intros.
Exists n.
Split;Auto with arith.
Qed.

Lemma subset_has_at_least_n_elements : (A:Setoid;n:Nat;B:(part_set A))
  (has_at_least_n_elements n B) -> (has_at_least_n_elements n A).
Intros.
Red;Red in H.
Inversion_clear H.
Exists (Map_embed x).
Fold (distinct (Map_embed x)).
Fold (distinct x) in H0.
(Apply Map_embed_preserves_distinct;Auto with algebra).
Qed.

Lemma subset_bounds_set_size_from_below : (A:Setoid;B:(part_set A);n:Nat)
  (has_n_elements n B) -> (has_at_least_n_elements n A).
Intros.
(Apply subset_has_at_least_n_elements with B;Auto with algebra).
(Apply has_n_elements_then_has_at_least_n_elements;Auto with algebra).
Qed.


Lemma has_extra_element_strong: (A:Setoid;B,C:(part_set A);m,n:Nat)
  (has_at_least_n_elements n B) -> (has_n_elements m C) -> (lt m n) ->
    (EXT a:A | (in_part a B)/\~(in_part a C)).
Intros.
Inversion H.
LetTac B':=(seq_set (Map_embed x)).
Assert (has_n_elements n B').
Red.
Exists (seq_set_seq (Map_embed x)).
Split.
Unfold B'.
Simpl.
Red;Simpl.
Split;Intro;Auto.
Clear H3.
Unfold subtype_image_equal.
Simpl.
NewDestruct x0.
Simpl in subtype_prf.
Rename subtype_elt into a.
Inversion_clear subtype_prf.
Exists x0.
Simpl.
Auto.
Red.
Intros.
Simpl.
Unfold subtype_image_equal.
Simpl.
Intro;(Apply (H2 i j);Auto with algebra).
Assert (EXT a:A | (in_part a B')/\~(in_part a C)).
(Apply has_extra_element with m n;Auto with algebra).
Assert (included B' B).
Red.
Intros a Ha.
Simpl in Ha.
Inversion_clear Ha.
(Apply in_part_comp_l with (subtype_elt (x x0));Auto with algebra).
Inversion_clear H4.
Rename x0 into a.
Exists a.
Inversion_clear H6.
Split;Auto.
Qed.

Lemma not_at_least_then_at_most : (A:Setoid;n:Nat)
  ~(has_at_least_n_elements (S n) A) -> (has_at_most_n_elements n A).
Intros.
Unfold has_at_least_n_elements in H.
Unfold has_at_most_n_elements.
NewInduction n.
Exists O;Split;Auto.
Red.
Exists (empty_seq A).
Split.
Simpl.
Red.
Intro a;Split;Simpl;Auto.
Intros _.
(Apply False_ind;Auto with algebra).
Apply H.
Exists (const_seq (S O) a).
Intros;Intro.
Auto with algebra.
Red.
Intros.
Auto with algebra.
Case (classic (EXT v:(seq (S n) A) |
              (i,j:(fin (S n)))~i =' j->~(v i) =' (v j))).
Intro;Exists (S n).
Split;Auto.
Red.
Inversion_clear H0.
Rename x into aa.
Exists aa.
Split;Auto.
Simpl;Red;Simpl.
Intro a;Split;Auto;Intros _.
Apply NNPP;Intro;Apply H.
Exists a;;aa.
Red.
NewDestruct i;NewDestruct j.
NewDestruct index;NewDestruct index0.
Simpl.
Intuition.
Simpl.
Intros _.
Intro;Apply H0.
Exists (Build_finiteT (lt_S_n n0 (S n) in_range_prf0));Auto with algebra.
Simpl.
Intros _.
Intro;Apply H0.
Exists (Build_finiteT (lt_S_n n0 (S n) in_range_prf)).
(Apply Sym;Auto with algebra).
Simpl.
Intro.
(Apply (H1 (Build_finiteT (lt_S_n n0 (S n) in_range_prf))(Build_finiteT (lt_S_n n1 (S n) in_range_prf0)));Auto with algebra).

Intro.
Generalize (IHn H0);Intro p;Inversion_clear p.
Exists x.
Inversion_clear H1;Split;Auto.
Qed.

Lemma has_n_elements_by_at_least_at_most : (A:Setoid;n:Nat)
  (has_at_least_n_elements n A) -> (has_at_most_n_elements n A) ->
    (has_n_elements n A).
Intros.
Red in H H0.
Inversion_clear H;Inversion_clear H0.
Inversion_clear H.
Rename x0 into m.
Red;Red in H2.
Inversion_clear H2.
Inversion_clear H.
Rename x into aas.
Rename x0 into Aseq.
Exists aas.
Split;Auto.
(Apply Trans with (seq_set Aseq);Auto with algebra).

Simpl;Red;Simpl.
Intro a;Split;Simpl.

2:Simpl in H2;Red in H2;Simpl in H2.
2:Elim (H2 a);Auto.

Intro.
Inversion_clear H.
Rename x into i.
Cut (EXT j:(fin n) | (aas j)='(Aseq i)).
Intros.
Inversion_clear H.
Exists x.
(Apply Trans with (Aseq i);Auto with algebra).
Clear H4 a.

Generalize (exists_difference H0).
Intro;Inversion_clear H.
Rename x into d.
Cut (EXT j:(fin (plus m d)) | ((cast_seq aas H4) j) =' (Aseq i)).
Intro.
Inversion_clear H.
Rename x into j.
Exists (cast_fin j (sym_eq ??? H4)).
(Apply Trans with (cast_seq aas H4 j);Auto with algebra).

LetTac aas':=(cast_seq aas H4).
Assert (distinct aas').
Unfold aas'.
(Apply cast_seq_preserves_distinct;Auto with algebra).

Assert (included (seq_set aas') (seq_set Aseq)).
Simpl in H2;Red in H2;Simpl in H2.
Red.
Simpl;Intros.
Inversion_clear H5.
Elim (H2 x);Auto with algebra.

ClearBody aas'.
Clear H4 H2 H0 H1 aas n.
Move d after m.
Fold (distinct Aseq) in H3.

NewInduction m.
(Apply False_ind;Auto with algebra).

Case (classic (head aas')='(Aseq i)).
Intros.
Exists (Build_finiteT (lt_O_Sn (plus m d))).
(Apply Trans with (head aas');Auto with algebra).

Intros.
Elim (H5 (head aas')).
2:Unfold head;Simpl.
2:Fold (plus m d).
2:Exists (Build_finiteT (lt_O_Sn (plus m d))).
2:Apply Refl.

Intros j Hj.

Assert (distinct (omit Aseq j)).
(Apply omit_preserves_distinct;Auto with algebra).

Assert ~j='i in (fin?).
Assert ~(Aseq i)='(Aseq j).
Intro.
(Apply H0;Auto with algebra).
(Apply Trans with (Aseq j);Auto with algebra).
Intro;Apply H2.
(Apply (Map_compatible_prf Aseq);Auto with algebra).

Elim (omit_removes' Aseq H2).
Intros i' HAseqi'.

Assert (distinct (Seqtl aas')).
(Apply Seqtl_preserves_distinct;Auto with algebra).
Generalize (IHm (omit Aseq j) H1 i' (Seqtl aas') H4).
Intros.

Assert (included (seq_set (Seqtl aas')) (seq_set (omit Aseq j))).

2:Specialize (H6 H7).
2:Intro.
2:Inversion_clear H8.
2:NewDestruct x.
2:Exists (Build_finiteT (lt_n_S??in_range_prf)).
2:(Apply Trans with (Seqtl aas' (Build_finiteT in_range_prf));Auto with algebra).
2:(Apply Trans with (omit Aseq j i');Auto with algebra).

Clear H6.

Clear IHm HAseqi' i' H2 H0 i.
Cut (p:(fin (plus m d)))(EXT q:(fin m) | (Seqtl aas' p)='(omit Aseq j q)).
Intro.
Red.
Simpl.
Intros a Ha.
Inversion_clear Ha.
Generalize (H0 x);Intro p;Inversion_clear p.
Exists x0.
(Apply Trans with (Seqtl aas' x);Auto with algebra).

Intro.
Simpl.
NewDestruct p.
LetTac p':=(Build_finiteT (lt_n_S index (plus m d) in_range_prf)).

Assert ~p'='(Build_finiteT (lt_O_Sn (plus m d))) in(fin?).
Unfold p';Simpl.
Auto with arith.

Assert (k:(fin (plus (S m) d)))(EXT l:(fin (S m)) | (aas' k)='(Aseq l)).
Red in H5.
Simpl in H5.
Intro.
Generalize (H5 (aas' k));Intro.
Assert (EXT i:(finiteT (S (plus m d))) | (aas' k) =' (aas' i)).
Exists k.
Apply Refl.
Generalize (H2 H6).
Intro.
Inversion_clear H7.
Exists x.
Auto.

Generalize (H2 p');Intro.
Inversion_clear H6.
Rename x into q.

Cut (EXT q0:(finiteT m) | (Aseq q) =' (omit Aseq j q0)).
Intro.
Inversion_clear H6.
Exists x.
(Apply Trans with (Aseq q);Auto with algebra).

Cut ~j='q.
Intro.
Elim (omit_removes' Aseq H6).
Intros;Exists x;Auto.

Assert ~(aas' p')='(head aas').
Unfold head.
Fold (plus m d).
(Apply H;Auto with algebra).
Assert ~(Aseq q)='(head aas').
Intro;(Apply H6;Auto with algebra).
(Apply Trans with (Aseq q);Auto with algebra).
Assert ~(Aseq q)='(Aseq j).
Intro;(Apply H8;Auto with algebra).
(Apply Trans with (Aseq j);Auto with algebra).
Intro;(Apply H9;Auto with algebra).
Qed.

Lemma inclusion_bounds_elements_from_below : (A:Setoid;B,C:(part_set A);n:Nat)
  (has_n_elements n B) -> (included B C) -> (has_at_least_n_elements n C).
Intros;Red.
Red in H H0.
Inversion_clear H.
Inversion_clear H1.
Assert (i:(fin n))(in_part (Map_embed x i) C).
Intro.
Simpl.
(Apply H0;Auto with algebra).
Exists (cast_map_to_subset H1).
Red;Intros.
Red in H2;(Apply (H2 i j);Auto with algebra).
Qed.

Lemma has_n_elements_doesn't_have_more : (A:Setoid;n:Nat)
  (has_n_elements n A) -> (m:Nat) (lt n m) -> ~(has_at_least_n_elements m A).
Red;Intros.
Assert (has_at_most_n_elements m A).
Exists n.
Split;Auto with arith.
Generalize (has_n_elements_by_at_least_at_most H1 H2).
Intro.
Assert n='m.
Assert (has_n_elements n (full A)).
(Apply full_preserves_has_n_elements;Auto with algebra).
Assert (has_n_elements m (full A)).
(Apply full_preserves_has_n_elements;Auto with algebra).
(Apply (has_n_elements_inj H4 H5);Auto with algebra).
Rewrite H4 in H0.
Generalize lt_n_n;Intro p;Red in p.
(Apply p with m;Auto with algebra).
Qed.

Lemma union_has_at_most_n_plus_m_elements : (A:Setoid;B,C:(part_set A);n,m:Nat)
  (has_n_elements n B) -> (has_n_elements m C) ->
    (has_at_most_n_elements (plus n m) (union B C)).
Intros.
Red.
Generalize Dependent B.
NewInduction n.
Intros.
Exists m.
Split;Auto with arith.
(Apply has_n_elements_comp with m C;Auto with algebra).
(Apply Trans with (union (empty A) C);Auto with algebra).
(Apply union_comp;Auto with algebra).
(Apply Sym;Auto with algebra).

Intros.
Red in H.
Inversion_clear H.
Rename x into Bs.
Inversion_clear H1.
Red in H2.
Assert (has_n_elements n (seq_set (Map_embed (Seqtl Bs)))).
Red.
Exists (seq_set_seq (Map_embed (Seqtl Bs))).
Split.
Change (eq_part (full (seq_set (Map_embed (Seqtl Bs)))) (seq_set (seq_set_seq (Map_embed (Seqtl Bs))))).
Red.
Intro.
Simpl.
Split;Auto.
Intros _.
Unfold subtype_image_equal.
NewDestruct x.
Simpl in subtype_prf.
Inversion_clear subtype_prf.
Exists x.
Simpl.
Auto.
Red;Red;Intros.
Simpl in H3.
Red in H3.
NewDestruct i;NewDestruct j.
(Apply (H2 (Build_finiteT (lt_n_S ?? in_range_prf)) (Build_finiteT (lt_n_S?? in_range_prf0)));Auto with algebra).
Simpl.
Simpl in H1.
Auto with arith.
Generalize (IHn (seq_set (Map_embed (Seqtl Bs))) H1);Intro p.
Inversion_clear p.
Rename x into m'.
Inversion_clear H3.

Case (classic (in_part (B (head Bs)) C)).
Intro.
Exists m'.
Split.
Simpl;Auto with algebra.
(Apply has_n_elements_comp with m' (union (seq_set (Map_embed (Seqtl Bs))) C);Auto with algebra).
(Apply Trans with (union (inject_subsets (seq_set Bs)) C);Auto with algebra).
2:(Apply union_comp;Auto with algebra).
2:(Apply Trans with (inject_subsets (full B));Auto with algebra).
Apply Trans with (union (union (single (B (head Bs))) (seq_set (Map_embed (Seqtl Bs)))) C).
Change (eq_part (union (seq_set (Map_embed (Seqtl Bs))) C) (union
          (union (single (B (head Bs)))
            (seq_set (Map_embed (Seqtl Bs)))) C)).
Red.
Intro a;Split;Intro.
Simpl in H6.
Inversion_clear H6.
Simpl.
Left.
Right.
Auto.
Simpl.
Right.
Auto.
Simpl in H6.
Inversion_clear H6.
Inversion_clear H7.
Simpl.
Right.
(Apply in_part_comp_l with (B (head Bs));Auto with algebra).
Simpl.
Left;Auto.
Simpl.
Right;Auto.

Simpl;Red;Simpl.
Intro a;Split;Intros.
Inversion_clear H6.
Inversion_clear H7.
Right.
(Apply in_part_comp_l with (B (head Bs));Auto with algebra).
Left.
Inversion_clear H6.
NewDestruct  x.
Assert (in_part (Bs (Build_finiteT (lt_n_S??in_range_prf))) (seq_set Bs)).
Simpl.
Exists (Build_finiteT (lt_n_S index n in_range_prf)).
Red;Apply Refl.
Red in H6;Exists (Build_subtype H6).
Simpl.
Auto.
Right;Auto.

Inversion_clear H6.
2:Right;Auto.
Left.
Inversion_clear H7.
NewDestruct x.
Rename subtype_elt into a'.
Rename subtype_prf into Ha'.
Simpl in Ha'.
Inversion_clear Ha'.
Red in H7.
NewDestruct x.
NewDestruct index.
Left.
Simpl in H6.
(Apply Trans with (B a');Auto with algebra).
(Apply Trans with (subtype_elt (Bs (Build_finiteT in_range_prf)));Auto with algebra).
Right.
Exists (Build_finiteT (lt_S_n??in_range_prf)).
Simpl in H6.
(Apply Trans with (subtype_elt a');Auto with algebra).
(Apply Trans with (subtype_elt (Bs (Build_finiteT in_range_prf)));Auto with algebra).

Intro.
Exists (S m').
Split.
Simpl.
Auto with arith.

Inversion_clear H5.
Rename x into BCs.
Inversion_clear H6.
Assert (i:?)(in_part (Map_embed BCs i) (union B C)).
Intro.
Simpl.
LetTac bc:=(BCs i).
Change (in_part (subtype_elt bc) B)\/(in_part (subtype_elt bc) C).
Case bc.
Intros a Ha.
Simpl in Ha.
Inversion_clear Ha.
2:Simpl;Right;Auto.
Left.
Inversion_clear H6.
NewDestruct  x.
(Apply in_part_comp_l with (subtype_elt
              (Bs (Build_finiteT (lt_n_S index n in_range_prf))));Auto with algebra).

LetTac BCs':=((cast_map_to_subset H6)::(seq??)).
LetTac b0:=(B (head Bs)).
Assert (in_part b0 (union B C)).
Simpl.
Left.
Unfold b0.
Simpl.
Auto with algebra.
Red in H8.
Red.
LetTac bc0:=((Build_subtype H8)::(union B C)).
Exists bc0;;BCs'.
Split.
Simpl;Red;Simpl.
Intro bc;(Split;Auto);Intros _.
Unfold subtype_image_equal.
Case (classic bc='bc0 in (union B C)).
Intro.
Exists (Build_finiteT (lt_O_Sn m')).
Auto with algebra.
Intro.
Cut (EXT i:? | (subtype_elt bc) =' (subtype_elt (BCs i)) in A).
Intro.
Inversion_clear H10.
NewDestruct  x.
Exists (Build_finiteT (lt_n_S??in_range_prf)).
(Apply Trans with (subtype_elt (BCs (Build_finiteT in_range_prf)));Auto with algebra).
Simpl.
(Apply subtype_elt_comp;Auto with algebra).

Cut (union B C)='(seq_set (subtype_elt bc0);;(Map_embed BCs)).
Intro.
Simpl in H10.
Red in H10.
Elim (H10 (subtype_elt bc)).
Intros.
Clear H10 H12.
Assert (in_part (subtype_elt bc) (union B C));Auto with algebra.
Generalize (H11 H10);Clear H10 H11;Intro p.
Assert (in_part (subtype_elt bc) (seq_set (Map_embed BCs))).
Simpl in p.
Inversion_clear p.
NewDestruct x.
NewDestruct index.
(Apply False_ind;Auto with algebra).
(Apply in_part_comp_l with (subtype_elt
               (BCs (Build_finiteT (lt_S_n n0 m' in_range_prf))));Auto with algebra).
Simpl.
Exists (Build_finiteT (lt_S_n n0 m' in_range_prf)).
Apply Refl.
Simpl in H10.
Auto.

Clear H9 bc BCs' H7 H4 H1 H2 IHn H0 m.
Simpl;Red;Simpl.
Intro a;Split;Intro.
Inversion_clear H0.
Case (classic a='b0).
Intro;Exists (Build_finiteT (lt_O_Sn m'));Auto.
Intro.
Cut (in_part a (union (seq_set (Map_embed (Seqtl Bs))) C)).
Intro p.
Red in p.
Assert (in_part (Build_subtype p)::(union (seq_set (Map_embed (Seqtl Bs))) C) (seq_set BCs)).
(Apply in_part_comp_r with (full (union (seq_set (Map_embed (Seqtl Bs))) C));Auto with algebra).
Simpl in H2.
Inversion_clear H2.
NewDestruct x.
Exists (Build_finiteT (lt_n_S??in_range_prf)).
Red in H4;Simpl in H4.
(Apply Trans with (subtype_elt (BCs (Build_finiteT in_range_prf)));Auto with algebra).

Simpl.
Left.
Red in H1.
LetTac a':=((Build_subtype H1)::B).
Elim (H a').
Simpl;Intros.
Generalize (H2 I);Clear H2 H4;Intro.
Inversion_clear H2.
NewDestruct x.
NewDestruct index.
(Apply False_ind;Auto with algebra).
Apply H0.
Red in H4.
(Apply Trans with (subtype_elt a');Auto with algebra).
(Apply Trans with (subtype_elt (Bs (Build_finiteT in_range_prf)));Auto with algebra).
Unfold b0.
Simpl.
(Apply subtype_elt_comp;Auto with algebra).
Unfold head.
Exists (Build_finiteT (lt_S_n??in_range_prf)).
Red in H4.
(Apply Trans with (subtype_elt a');Auto with algebra).
(Apply Trans with (subtype_elt (Bs (Build_finiteT in_range_prf)));Auto with algebra).

Assert (in_part a (union (seq_set (Map_embed (Seqtl Bs))) C)).
Simpl;Right;Auto.
Red in H0.
Elim (H5 (Build_subtype H0)).
Simpl;Intros.
Generalize (H2 I);Clear H4 H2;Intro.
Inversion_clear H2.
NewDestruct x.
Exists (Build_finiteT (lt_n_S??in_range_prf)).
Red in H4;Simpl in H4.
(Apply Trans with (subtype_elt (BCs (Build_finiteT in_range_prf)));Auto with algebra).

Inversion_clear H0.
NewDestruct x.
NewDestruct index.
Left.
(Apply in_part_comp_l with b0;Auto with algebra).
Unfold b0.
Simpl.
Auto with algebra.
LetTac a'':= (BCs (Build_finiteT (lt_S_n n0 m' in_range_prf))).
Cut (in_part (subtype_elt a'') B)\/(in_part (subtype_elt a'') C).
Intros.
Inversion_clear H0.
Left.
(Apply in_part_comp_l with (subtype_elt a'');Auto with algebra).
Right.
(Apply in_part_comp_l with (subtype_elt a'');Auto with algebra).
Case a''.
Simpl.
Intros.
Inversion_clear subtype_prf.
Left.
Inversion_clear H0.
NewDestruct x.
Rename subtype_elt into a'.
(Apply in_part_comp_l with (subtype_elt
              (Bs (Build_finiteT (lt_n_S index n in_range_prf0))));Auto with algebra).
Right;Auto.

(Apply distinct_cons;Auto with algebra).
Intro.
Unfold bc0 BCs'.
Simpl.
Unfold subtype_image_equal.
Simpl.
Unfold b0.
Simpl.
LetTac b:=(BCs i).
Change ~(subtype_elt (head Bs)) =' (subtype_elt b).
Case b.
Intros a Ha;Simpl.
Simpl in Ha.
Inversion_clear Ha.
Inversion_clear H9.
NewDestruct x.
Intro;Red in H2;(Apply (H2 (Build_finiteT (lt_O_Sn n)) (Build_finiteT (lt_n_S??in_range_prf)));Auto with algebra).
Simpl.
Auto with arith.
Simpl.
Red.
(Apply Trans with (subtype_elt (head Bs));Auto with algebra).
(Apply Trans with a;Auto with algebra).
Intro;Apply H3.
Unfold b0.
(Apply in_part_comp_l with a;Auto with algebra).
Qed.

Lemma subset_also_has_n_elements_then_it_is_full : (n:Nat;A:Setoid;B:(part_set A))
  (has_n_elements n A) -> (has_n_elements n B) -> B='(full A).

(* By contradiction: suppose x in A and not x in B. Then B is also a subset of A\{x}. But the first has n elements and the latter n-1, contradicting the above result.*)

Intros.
Apply Sym.
Apply NNPP;Intro.
Assert (EXT x:A | ~(in_part x B)).
Assert ~(x:A)(in_part x B).
Intro;Red in H1;Apply H1.
Simpl;Red;Simpl.
Split;Auto.
Apply NNPP;Intro;Apply H2.
Intro a.
Apply NNPP;Intro;Apply H3.
Exists a;Auto.

Inversion_clear H2.
Rename x into a.
Assert (has_n_elements n (full A)).
(Apply full_preserves_has_n_elements;Auto with algebra).

NewDestruct n.
Red in H.
Inversion_clear H.
Inversion_clear H4.
Assert (in_part a (empty A)).
(Apply in_part_comp_r with (full A);Auto with algebra).
Simpl in H4.
Auto.
(* ie. the case n=0 cannot happen; n->(S n)*)

Assert (included B (diff (full A) (single a))).
Red;Simpl.
Split;Auto.
Intro;(Apply H3;Auto with algebra).
(Apply in_part_comp_l with x;Auto with algebra).

Cut (has_n_elements n (diff (full A) (single a))).
Intro.
Absurd (has_at_least_n_elements (S n) ((diff (full A) (single a)))).
(Apply has_n_elements_doesn't_have_more with n;Auto with algebra).
(Apply inclusion_bounds_elements_from_below with B;Auto with algebra).

Clear H4 H3 H H1 H0 B.
Generalize (n_element_subset_sequence H2).
Intro.
Inversion_clear H.
Inversion_clear H0.
Assert (EXT i:? | a='(x i)).
Simpl in H;Red in H;Simpl in H.
Generalize (H a);Intros.
Inversion_clear H0.
Auto.

Inversion_clear H0.
Rename x into As;Rename x0 into i.
(Apply has_n_elements_comp with n (seq_set (omit As i));Auto with algebra).
Assert (j:?)(in_part (omit As i j) (seq_set (omit As i))).
Intros.
Opaque omit.
Simpl.
Exists j.
Apply Refl.
Exists (cast_map_to_subset H0).
Split.
Simpl.
Red.
Simpl.
Split;Simpl;Auto.
Intros _.
Unfold subtype_image_equal.
NewDestruct x.
Simpl in subtype_prf.
Inversion_clear subtype_prf.
Exists x.
Simpl.
(Apply Trans with (omit As i x);Auto with algebra).
Red.
Intros.
Rename i0 into i'.
Assert ~(omit As i i')='(omit As i j).
Generalize (omit_preserves_distinct H1).
Intro p;Generalize (p i);Clear p;Intro p;Red in p.
(Apply p;Auto with algebra).
Intro;Red in H5;Apply H5.
(Apply Trans with (subtype_elt (cast_map_to_subset H0 i'));Auto with algebra).
(Apply Trans with (subtype_elt (cast_map_to_subset H0 j));Auto with algebra).

Simpl.
Red.
Simpl.
Split.
Intuition.
Inversion_clear H0.
Generalize distinct_omit_removes_all.
Intro p;Generalize (p ???H1 i x0).
Intro q;Red in q;(Apply q;Auto with algebra).
(Apply Trans with a;Auto with algebra).
(Apply Trans with x;Auto with algebra).

Intuition.
Elim (H x).
Simpl.
Intros p _;Generalize (p I);Clear p;Intro p.
Inversion_clear p.
Rename x0 into i'.
Assert ~i='i'.
Intro;Apply H5.
(Apply Trans with (As i');Auto with algebra).
(Apply Trans with (As i);Auto with algebra).

Elim (omit_removes' As H6).
Intro j;Intro.
Exists j;(Apply Trans with (As i');Auto with algebra).
Qed.
