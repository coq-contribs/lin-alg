(** %\subsection*{ support :  omit\_facts.v }%*)
Set Implicit Arguments.
Require Export seq_equality_facts.
Require Export sums.
Require Export mult_by_scalars.

Lemma omit_head_is_seqtl : (n:Nat;M:Setoid;s:(seq n M);H0:(lt O n))
  (omit s (Build_finiteT H0)) =' (Seqtl s).
NewDestruct n.
Simpl.
Red;Auto with algebra.
NewDestruct n.
Intros;(Apply Trans with (empty_seq M);Auto with algebra).
Auto with algebra.
Qed.

Hints Resolve  omit_head_is_seqtl : algebra.


Lemma omit_tlelt :
  (n:Nat;A:Setoid;v:(seq (S (S n)) A);m:Nat;HS:(lt (S m) (S (S n)));H:(lt m (S n)))
    (omit v (Build_finiteT HS)) =' (head v);;(omit (Seqtl v) (Build_finiteT H)).
Induction n.
Intros A v m.
Case m.
Intros.
(Apply Trans with (head v);;(empty_seq A);Auto with algebra).
Intros.
Inversion H.
Inversion H1.
Intros.
(Apply Trans with (head v);;(omit (Seqtl v) (Build_finiteT (lt_S_n ?? HS)));Auto with algebra).
Change  ((head v);;(omit (Seqtl v) (Build_finiteT (lt_S_n m (S (S n0)) HS))))
     =' ((head v);;(omit (Seqtl v) (Build_finiteT H0))) in (seq (S (S n0)) A).
(Apply cons_comp;Auto with algebra).
Qed.

Hints Resolve omit_tlelt : algebra.

(** - The above also holds for seqs of length (S n), but since the types
 become non-convertible then, we have to do a cast_seq or use seq_equal. *)

Lemma omit_tlelt' :
  (n:Nat;A:Setoid;v:(seq (S n) A);m:Nat;HS:(lt (S m) (S n));H:(lt m n);Heq:(S (pred n))=n)
    (omit v (Build_finiteT HS)) 
      =' (cast_seq (head v);;(omit (Seqtl v) (Build_finiteT H)) Heq).
NewDestruct n.
Intros;Inversion_clear Heq.
Intros.
(Apply Trans with (head v);;(omit (Seqtl v) (Build_finiteT H));Auto with algebra).
Qed.

Hints Resolve omit_tlelt' : algebra.

Lemma omit_tlelt'' :
  (n:Nat;A:Setoid;v:(seq (S n) A);m:Nat;HS:(lt (S m) (S n));H:(lt m n);Heq:(S (pred n))=n)
    (seq_equal (omit v (Build_finiteT HS)) (head v);;(omit (Seqtl v) (Build_finiteT H))).
Intros.
Apply seq_equal_trans with (pred (S n)) (cast_seq (head v);;(omit (Seqtl v) (Build_finiteT H)) Heq);Auto with algebra.
Apply Map_eq_seq_equal;Auto with algebra.
Qed.

Hints Resolve omit_tlelt'' : algebra.

Lemma omit_concat_first_part : (n,m:Nat;A:Setoid;v:(seq (S n) A);w:(seq m A);i:Nat;Hi:(lt i (S n));Hi':(lt i (plus (S n) m)))
  (omit v++w (Build_finiteT Hi')) =' (omit v (Build_finiteT Hi))++w.
NewInduction n.
Intros.
NewDestruct i.
2:Inversion_clear Hi.
2:Inversion_clear H.
(Apply Trans with (Seqtl v++w);Auto with algebra).
(Apply Trans with (Seqtl v)++w;Auto with algebra).
Intros.
NewDestruct i.
(Apply Trans with (Seqtl v++w);Auto with algebra).
(Apply Trans with (Seqtl v)++w;Auto with algebra).
(Apply Trans with (head v++w);;(omit (Seqtl v++w) (Build_finiteT (lt_S_n?(S (plus n m))Hi')));Auto with algebra).
(Apply Trans with ((head v);;(omit (Seqtl v) (Build_finiteT (lt_S_n??Hi))))++w;Auto with algebra).
(Apply Trans with (head v);;(omit (Seqtl v++w) (Build_finiteT (lt_S_n?(S (plus n m))Hi')));Auto with algebra).
Apply Trans with (head v);;((omit (Seqtl v) (Build_finiteT (lt_S_n n0 (S n) Hi)))++w).
2:Change (head v);;((omit (Seqtl v) (Build_finiteT (lt_S_n n0 (S n) Hi)))++w)
   ='((head v);;(omit (Seqtl v) (Build_finiteT (lt_S_n n0 (S n) Hi))))
       ++w in (seq (S (plus n m)) A).
2:Apply cons_concat_special.
Change (head v);;
     (omit (Seqtl v++w) (Build_finiteT (lt_S_n n0 (S (plus n m)) Hi')))
     ='(head v);;
         ((omit (Seqtl v) (Build_finiteT (lt_S_n n0 (S n) Hi)))++w)
     in (seq (S (plus n m)) A).
Apply cons_comp;Auto with algebra.
Apply Trans with (omit (Seqtl v)++w (Build_finiteT (lt_S_n n0 (S (plus n m)) Hi'))).
Change (omit (Seqtl v++w) (Build_finiteT (lt_S_n n0 (S (plus n m)) Hi')))
     ='(omit (Seqtl v)++w
         (Build_finiteT (lt_S_n n0 (S (plus n m)) Hi')))
     in (seq (pred (S (plus n m))) A).
Apply omit_comp;Auto with algebra.
Change (omit (Seqtl v)++w (Build_finiteT (lt_S_n n0 (S (plus n m)) Hi')))
     ='(omit (Seqtl v) (Build_finiteT (lt_S_n n0 (S n) Hi)))++w
     in (seq (pred (plus (S n) m)) A).
Apply (!IHn m A (Seqtl v) w).
Qed.

Hints Resolve omit_concat_first_part : algebra.

(** - The following also comes in two guises. It is again an equation between two
 sequences of equal but non-convertible length. The first formulation uses the
 external (not inherited from any setoid) equality seq_equal, the second does a
 cast_seq in the appropriate places *)

Lemma omit_concat_second_part' : (n,m:Nat;A:Setoid;v:(seq n A);w:(seq m A);i:Nat;Hi:(lt i m);Hi':(lt (plus n i) (plus n m));H:(plus n (pred m))=(pred (plus n m))) 
  (seq_equal (omit v++w (Build_finiteT Hi')) v++(omit w (Build_finiteT Hi))).
Intros.

NewInduction n.
Intro j.
Generalize (le_or_lt (pred (plus O m)) j).
Intro p;Inversion_clear p.
Right;Split;Auto.

Left.
Exists H0.
Exists (lt_comp H0 (sym_eq ???H)).
Simpl in Hi' H H0.
Simpl.
(Apply Ap_comp;Auto with algebra).
Intro j.
Generalize (le_or_lt (pred (plus (S n) m)) j).
Intro p;Inversion_clear p.
Right;Split;Auto.
Rewrite H.
Auto.
Left.
Exists H0.
Exists (lt_comp H0 (sym_eq ???H)).

(Apply Trans with (omit (hdtl v)++w (Build_finiteT Hi') (Build_finiteT H0));Auto with algebra).
(Apply Trans with ((hdtl v)++(omit w (Build_finiteT Hi)) (Build_finiteT (lt_comp H0  (sym_eq nat (plus (S n) (pred m)) (pred (plus (S n) m)) H))));Auto with algebra).
Unfold hdtl.
(Apply Trans with (omit (head v);;((Seqtl v)++w) (Build_finiteT Hi') (Build_finiteT H0));Auto with algebra).
Apply Trans with ((head v);;((Seqtl v)++(omit w (Build_finiteT Hi)))
          (Build_finiteT
            (lt_comp H0
              (sym_eq nat (plus (S n) (pred m)) (pred (plus (S n) m)) H)))).
2:(Apply Ap_comp;Auto with algebra).
2:(Apply toSeq;Auto with algebra).
2:Apply (cons_concat_special (head v) (Seqtl v) (omit w (Build_finiteT Hi))).
Assert (plus n m)=(S(pred(plus n m))).
Clear H0 j IHn w v A.
Transitivity (plus (S n) (pred m));Auto with arith.
Transitivity (pred (plus (S n) m));Auto with arith.
Simpl.
Apply S_pred with (plus n i).
Auto with arith.

Apply Trans with (cast_seq (head v);;(omit (Seqtl v)++w (Build_finiteT (lt_S_n??Hi'))) (sym_eq???H1) (Build_finiteT H0));Fold (plus n i) (plus n m).
(Apply Ap_comp;Auto with algebra).
Apply toSeq.
Apply Trans with (cast_seq
          ((head (head v);;((Seqtl v)++w))
              ;;(omit (Seqtl (head v);;((Seqtl v)++w))
                  (Build_finiteT (lt_S_n (plus n i) (plus n m) Hi'))))
          (sym_eq nat (plus n m) (S (pred (plus n m))) H1)).
(Apply (!omit_tlelt' ?? ((head v);;((Seqtl v)++w)) ? Hi' (lt_S_n??Hi') (sym_eq nat (plus n m) (S (pred (plus n m))) H1));Auto with algebra).
(Apply cast_seq_comp;Auto with algebra).
Apply cons_comp;Auto with algebra.
Apply omit_comp;Auto with algebra.
Apply (Seqtl_cons_inv (head v) (Seqtl v)++w).

(Apply seq_equal_equal_elements;Auto with algebra).
Apply seq_equal_trans with w:=(head v)
           ;;(omit (Seqtl v)++w
               (Build_finiteT (lt_S_n (plus n i) (plus n m) Hi'))).
Apply seq_equal_symm.
Apply cast_seq_preserves_seq_equal.
(Apply seq_equal_cons;Auto with algebra).
Generalize (IHn (Seqtl v) (lt_S_n (plus n i) (plus n m) Hi')).
Clear IHn;Intro.
Apply H2.
Clear H2.
Simpl in H.
Transitivity (pred (S (plus n (pred m))));Auto with arith.
Qed.

Lemma omit_concat_second_part : (n,m:Nat;A:Setoid;v:(seq n A);w:(seq m A);i:Nat;Hi:(lt i m);Hi':(lt (plus n i) (plus n m));H:(plus n (pred m))=(pred (plus n m)))
  (omit v++w (Build_finiteT Hi'))='(cast_seq v++(omit w (Build_finiteT Hi)) H).
Intros.
Apply seq_equal_map_equal.
Apply seq_equal_trans with w:=v++(omit w (Build_finiteT Hi)).
(Apply omit_concat_second_part';Auto with algebra).
Apply cast_seq_preserves_seq_equal.
Qed.

Lemma omit_seq_in_seq_set :
  (n:Nat;A:Setoid;v:(seq n A)) (i:(fin n);j:(fin (pred n)))
    (in_part (omit v i j) (seq_set v)).
Intros.
Simpl.
Elim (omit_removes v i j).
Intros.
Exists x;Auto with algebra.
Qed.

Lemma seqsum_is_elt_plus_omitseq : (n:Nat;M:abelian_monoid;s:(seq n M);i:(fin n))
  (sum s)='(s i)+'(sum (omit s i)).
NewDestruct n.
Intros.
(Apply False_ind;Auto with algebra).

Induction n.
Simpl.
Unfold head.
Intros.
Elim i.
Intros.
(Apply SGROUP_comp;Auto with algebra).

Intros M.
Generalize (Hrecn M);Clear Hrecn;Intros.
Case i.
Intro x; Case x.
Intro.
(Apply Trans with (head s)+'(sum(Seqtl s));Auto with algebra).
Intros n0 l.
Apply Trans with ((Seqtl s)(Build_finiteT (lt_S_n??l))) +' (sum (omit s (Build_finiteT l))).
2:(Apply SGROUP_comp;Auto with algebra).

(Apply Trans with ((Seqtl s) (Build_finiteT (lt_S_n ?? l)))+' (sum (head s);;(omit (Seqtl s) (Build_finiteT (lt_S_n ?? l))));Auto with algebra).
(Apply Trans with ((Seqtl s) (Build_finiteT (lt_S_n ?? l)))+'((head s)+'(sum (omit (Seqtl s)
                           (Build_finiteT (lt_S_n ?? l)))));Auto with algebra).
(Apply Trans with (head s) +' (((Seqtl s) (Build_finiteT (lt_S_n ?? l))) +' (sum
                           (omit (Seqtl s)
                             (Build_finiteT (lt_S_n?? l)))));Auto with algebra).
(Apply Trans with (head s)+'(sum (Seqtl s));Auto with algebra).
Qed.

Lemma seqsum_min_elt_is_omitseq : (n:Nat;AG:abelian_group;s:(seq n AG);i:(fin n))
  (sum s)+'(min (s i))='(sum (omit s i)).
Intros.
(Apply GROUP_reg_right with (s i);Auto with algebra).
(Apply Trans with (sum s)+'((min (s i))+'(s i));Auto with algebra).
(Apply Trans with (sum s)+'(zero AG);Auto with algebra).
(Apply Trans with (sum s);Auto with algebra).
(Apply Trans with (s i)+'(sum (omit s i));Auto with algebra).
Generalize seqsum_is_elt_plus_omitseq.
Intro p.
Apply (p n AG s i).
Qed.

Hints Resolve omit_head_is_seqtl omit_tlelt seqsum_is_elt_plus_omitseq seqsum_min_elt_is_omitseq: algebra.


Lemma omit_mult_by_scalars :
  (n:Nat;F:ring;V:(module F);a:(seq n F);v:(seq n V);i:(fin n))
    (omit (mult_by_scalars a v) i) =' (mult_by_scalars (omit a i) (omit v i)).
NewDestruct n.
Intros;(Apply False_ind;Auto with algebra).

Induction n.
Intros.
Unfold omit.
Unfold nat_rect.
Unfold mult_by_scalars.
Unfold pointwise.
Simpl.
Red.
Intro.
(Apply False_ind;Auto with algebra).
Rename n into n';Intros.
Case i.
Intro x;Case x.
Intro l.
(Apply Trans with (Seqtl (mult_by_scalars a v));Auto with algebra).
(Apply Trans with (mult_by_scalars (Seqtl a) (Seqtl v));Auto with algebra).
Intros n0 l.
(Apply Trans with (head (mult_by_scalars a v)::(seq??));;(omit (Seqtl (mult_by_scalars a v)) (Build_finiteT(lt_S_n ?? l))::(fin (pred (S (S n')))));Auto with algebra).
(Apply Trans with (mult_by_scalars (head a);;(omit (Seqtl a) (Build_finiteT(lt_S_n ?? l))) (head v);;(omit (Seqtl v) (Build_finiteT (lt_S_n ?? l))));Auto with algebra).
Unfold mult_by_scalars.
Apply Trans with ((uncurry (MODULE_comp 1!F 2!V)) (couple (head a) (head v)));;(pointwise (uncurry (MODULE_comp 1!F 2!V)) (omit (Seqtl a) (Build_finiteT (lt_S_n n0 (S n') l))) (omit (Seqtl v) (Build_finiteT (lt_S_n n0 (S n') l)))).
Change  ((head (pointwise (uncurry (MODULE_comp 1!F 2!V)) a v))
       ;;(omit (Seqtl (pointwise (uncurry (MODULE_comp 1!F 2!V)) a v))
           (Build_finiteT (lt_S_n n0 (S n') l))))
     =' ((uncurry (MODULE_comp 1!F 2!V) (couple (head a) (head v)))
            ;;(pointwise (uncurry (MODULE_comp 1!F 2!V))
                (omit (Seqtl a) (Build_finiteT (lt_S_n n0 (S n') l)))
                (omit (Seqtl v) (Build_finiteT (lt_S_n n0 (S n') l))))).
(Apply cons_comp;Auto with algebra).
Unfold mult_by_scalars in Hrecn.
(Apply Trans with ((omit (pointwise (uncurry (MODULE_comp 1!F 2!V)) (Seqtl a) (Seqtl v)))(Build_finiteT (lt_S_n n0 (S n') l)));Auto with algebra).
Change    ((uncurry (MODULE_comp 1!F 2!V) (couple (head a) (head v)))
       ;;(pointwise (uncurry (MODULE_comp 1!F 2!V))
           (omit (Seqtl a) (Build_finiteT (lt_S_n n0 (S n') l)))
           (omit (Seqtl v) (Build_finiteT (lt_S_n n0 (S n') l)))))
     =' (pointwise (uncurry (MODULE_comp 1!F 2!V))
          ((head a);;(omit (Seqtl a) (Build_finiteT (lt_S_n n0 (S n') l))))
          ((head v);;(omit (Seqtl v) (Build_finiteT (lt_S_n n0 (S n') l))))).
Auto with algebra.
Qed.

Hints Resolve omit_mult_by_scalars : algebra.

Lemma omit_Map_embed :
  (n:Nat;F:ring;V:(module F);s:(part_set V);v:(seq n s);i:(fin n))
    (omit (Map_embed v) i)='(Map_embed (omit v i)).
NewDestruct n.
Intros.
(Apply False_ind;Auto with algebra).

Induction n.
Intros.
Unfold Map_embed omit nat_rect.
Simpl.
Red.
Intros.
(Apply False_ind;Auto with algebra).

Intros.
Case i.
Intro x.
Case x.
Intro l.
(Apply Trans with (Seqtl (Map_embed v));Auto with algebra).
(Apply Trans with (Map_embed (Seqtl v));Auto with algebra).

Intros n1 l.
(Apply Trans with (head (Map_embed v));;(omit (Seqtl (Map_embed v)) (Build_finiteT (lt_S_n??l)));Auto with algebra).
(Apply Trans with (Map_embed (head v);;(omit (Seqtl v) (Build_finiteT (lt_S_n??l))));Auto with algebra).
(Apply Trans with (s (head v));;(Map_embed (omit (Seqtl v) (Build_finiteT (lt_S_n ?? l))));Auto with algebra).
Change    ((head (Map_embed v))
       ;;(omit (Seqtl (Map_embed v)) (Build_finiteT (lt_S_n n1 (S n) l))))
     =' ((s (head v))
            ;;(Map_embed (omit (Seqtl v) (Build_finiteT (lt_S_n n1 (S n) l))))).
(Apply cons_comp;Auto with algebra).
(Apply Trans with (omit (Map_embed (Seqtl v)) (Build_finiteT (lt_S_n ?? l)));Auto with algebra).
Change    ((s (head v))
       ;;(Map_embed (omit (Seqtl v) (Build_finiteT (lt_S_n n1 (S n) l)))))
     =' (Map_embed
          ((head v);;(omit (Seqtl v) (Build_finiteT (lt_S_n n1 (S n) l))))).
Auto with algebra.
Qed.
Hints Resolve omit_Map_embed : algebra.

