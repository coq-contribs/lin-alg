(** * subspace_dim.v *)
Set Implicit Arguments.
Require Export bases_finite_dim.

(** - This file proves theorem 1.11 - every subspace W of a finite-dimensional
vectorspace V has itself a finite dimension < dim(V) *)

Fixpoint span_ind_uninject [F:field;V:(vectorspace F);W:(subspace V);
  X:(part_set W);x:(span_ind_formal (inject_subsets X))] : (span_ind_formal X) :=

  Cases x of Zerovector =>
                  (Zerovector ?)
           | (Immediately c) =>
                  (Immediately 3!X (uninject_subsetsify c))
           | (Plusvector x1 x2) =>
                  (Plusvector (span_ind_uninject x1) (span_ind_uninject x2))
           | (Multvector f x1) =>
                  (Multvector f (span_ind_uninject x1))
  end.

(*
Axiom span_ind_uninject_prop : (F:field;V:(vectorspace F);W:(subspace V);X:(part_set W);x:(span_ind_formal (inject_subsets X))) 
  (span_ind_injection x)='(subtype_elt (span_ind_injection (span_ind_uninject x))).
*)

(** - The above axiom is actually provable. Below you find the proof script. (Garbled if
 you're reading via coqdoc) The reason I turned this into an axiom is that the [Qed.]
 command actually takes a full 40 minutes! (on my machine; a PIII/733MHz)
*)

Lemma span_ind_uninject_prop : (F:field;V:(vectorspace F);W:(subspace V);X:(part_set W);x:(span_ind_formal (inject_subsets X)))   (span_ind_injection x)='(subtype_elt (span_ind_injection (span_ind_uninject x))).
Intros.
Rename x into x1.
NewInduction x1.
Simpl.
Apply Refl.
Simpl.
Simpl in c.
NewDestruct c.
Simpl.
Apply Refl.
Apply Trans with (span_ind_injection x0)+'(span_ind_injection x2);[Apply Refl | Idtac].
Apply Trans with (subtype_elt (span_ind_injection (Plusvector (span_ind_uninject x0) (span_ind_uninject x2))));[Idtac | Apply Refl].
Apply Trans with (subtype_elt (span_ind_injection (span_ind_uninject x0))+'(span_ind_injection (span_ind_uninject x2))).
2:Apply subtype_elt_comp.
2:Simpl.
2:Red;Apply Refl.
Apply Trans with (subtype_elt (span_ind_injection (span_ind_uninject x0)))+'(subtype_elt (span_ind_injection (span_ind_uninject x2))).
2:Apply Refl.
Apply SGROUP_comp.
Apply IHx0.
Apply IHx2.
Apply Trans with c mX (span_ind_injection x1);[Apply Refl|Idtac].
Apply Trans with (subtype_elt c mX (span_ind_injection (span_ind_uninject x1)));[Idtac|Abstract Apply Refl].
Apply Trans with c mX (subtype_elt (span_ind_injection (span_ind_uninject x1)));Abstract Auto with algebra.
Time Qed.

Section prelim.
Variable F:field.
Variable V:(vectorspace F).

Lemma not_generates_then_leaves_over : (S:(part_set V))
  ~(generates S (full V)) -> (EXT v:V | ~(in_part v(span_set S))).
Intros.
Unfold generates in H.
Apply NNPP;Intro.
Red in H;Apply H.
Intro.
Simpl;Split;Auto;Intros _.
Apply NNPP;Intro.
Red in H0;Apply H0.
Exists x.
Simpl;Auto.
Qed.

(** - Once we know that some subset of $V$ has an element, we must be able to get it
 if we want to prove theorem 1.11 - hence this axiom. It is a kind of choice principle,
 hence the name I gave it. I know AC+EM+impredicativity = inconsistency, but type isn't
 impredicative so we should be OK *)
Axiom AC' : (S:(part_set V))(EXT v:V | (in_part v S))->(sigT V [v:V](in_part v S)).

Lemma ACcomplement :  (S:(part_set V))
  (EXT v:V | ~(in_part v S)) -> (sigT V [v:V]~(in_part v S)).
Intros.
Cut (EXT v:V | (in_part v (compl S)));Try Intro.
Generalize (AC' H0).
Intro.
NewDestruct X.
Exists x.
Simpl in i.
Auto.
Simpl.
Auto.
Qed.

(** - Also we need to be able to decide whether some set generates the vectorspace.
 This, by the way, is the only time I use the sort Set - just to be able to use the
 informative or (i.e., {A}+{B}) Since I didn't introduce AC on the Set level, we should
 still be OK; also we don't have full EM, just for this one predicate. *)

Axiom dec_gen : (S:(part_set V)){(generates S (full V))}+{~(generates S (full V))}.

(** - To extend a linearly independent sequence (whenever possible): *)
Definition try_extend : (k:Nat;v:(seq k V))
  (lin_indep (seq_set v))/\(distinct v) ->
    (sigT ? [i:Nat](sigT ? [w:(seq i V)](lin_indep (seq_set w))/\(distinct w))).
Intros.
Generalize (dec_gen (seq_set v)).
Intro.
Inversion_clear H0.
Exists k.
Exists v.
Auto.
Exists (S k).
Generalize Dependent (ACcomplement (not_generates_then_leaves_over H1)).
Intro.
NewDestruct X.
Exists x;;v.
Inversion_clear H;Split.
Elim (lin_dep_vs_span_lemma H0 5!x).
Intros.
Apply lin_indep_comp with (union (seq_set v) (single x));Auto with algebra.
Red;Intro p;Generalize Dependent (H p).
Auto.
Generalize Dependent set_included_in_its_span.
Unfold included.
Intros;Intro;Red in n;Apply n.
Apply in_part_comp_r with ((span (seq_set v))::(part_set V));Auto with algebra.
Apply distinct_cons.
Auto.
Intros.
Intro.
Red in n.
Apply n.
Apply in_part_comp_r with ((span (seq_set v))::(part_set V));Auto with algebra.
Apply set_included_in_its_span.
Exists i.
Auto.
Defined.

(** - It has the desired properties: *)

Lemma extend_prop : (k:Nat;v:(seq k V);H:(lin_indep (seq_set v))/\(distinct v))
  Cases (try_extend H) of (existT i _) =>
      (i='k <-> (span (seq_set v))='(full V) in (part_set V))
   /\ (i='(S k)<->~(span (seq_set v))='(full V) in (part_set V))
  end.
Intros.
Unfold try_extend.
LetTac dgv := (dec_gen (seq_set v)).
Case dgv.
Intro.
Red in g.
Split;Split.
Auto.
Simpl;Auto.
Intro;Intro.
Clear H1 g dgv H v V F.
Simpl in k.
Simpl in H0.
NewInduction k;Intuition.
Inversion_clear H0.
Intro.
Red in H0;Apply False_ind.
Auto.
Intro.
LetTac Acv:=(ACcomplement (not_generates_then_leaves_over n)).
Case Acv.
Intros.
Split;Split.
Intro;Apply False_ind.
Simpl in H0.
Clear n0 x Acv n dgv H v.
NewInduction k;Intuition.
Inversion_clear H0.

Intros;Apply False_ind;Intuition.
2:Auto with algebra.
Intros _.
Intro.
Red in n0;Apply n0.
Case (H0 x).
Simpl;Auto with algebra.
Qed.

Lemma extend_prop2 : (k:Nat;v:(seq k V);H:(lin_indep (seq_set v))/\(distinct v))
  Cases (try_extend H) of (existT i (existT w H')) =>
       (i='k <-> (seq_equal v w))
    /\ (i='(S k)-> (seq_equal v (Seqtl w)))
  end.
Intros.
Unfold try_extend.
LetTac dgv := (dec_gen (seq_set v)).
Case dgv.
Intro.
Split;Try Split;Auto with algebra.
Intros.
Simpl in H0.
Apply False_ind.
Clear g dgv H v;NewInduction k;Intuition;Inversion_clear H0.
Intro.
LetTac Acv:=(ACcomplement (not_generates_then_leaves_over n)).
Case Acv.
Intros.
Split;Try Split.
Intro;Apply False_ind.
Simpl in H0.
Clear n0 x Acv n dgv H v.
NewInduction k;Intuition;Inversion_clear H0.
Intros;Apply False_ind;Intuition.
2:Intros _.
2:Apply Map_eq_seq_equal;Auto with algebra.
Generalize Dependent (seq_equal_length_equal H0).
Intro p;Simpl in p.
Clear b H2 H1 H0 n0 x Acv n v.
NewInduction k;Intuition;Inversion_clear p.
Qed.

(** - To repeat this extending procedure $n$ times: *)
Fixpoint rep_ext [n:nat] : (k:Nat;v:(seq k V))
  (lin_indep (seq_set v))/\(distinct v) ->
    (sigT ? [i:Nat](sigT ? [w:(seq i V)](lin_indep (seq_set w))/\(distinct w)))
:=
  [k;v;H]
  Cases n of
     O => (existT ? [i:Nat]? k (existT ? [w:(seq k V)]? v H))
  | (S m) => Cases (rep_ext m H) of (existT i (existT w H')) =>
               (try_extend H')
             end
  end.

Lemma preserve_lin_indep: (n,k:Nat;v:(seq k V);H:(lin_indep (seq_set v))/\(distinct v))
  Cases (rep_ext n H) of (existT i (existT w H')) =>
    (lin_indep (seq_set w))/\(distinct w)
  end.
Intros.
Case (rep_ext n H).
Intros;NewDestruct s.
Auto.
Qed.

Lemma grow_nr_elts : (n,k:Nat;v:(seq k V);H:(lin_indep (seq_set v))/\(distinct v))
  (has_n_elements k (seq_set v))->
  Cases (rep_ext n H) of (existT i (existT w H')) =>
    (has_n_elements i (seq_set w))
  end.
NewInduction n.
Simpl.
Auto.
Intros.
Simpl.
Generalize Dependent (IHn ?? H H0).
Case (rep_ext n H).
Intros;NewDestruct s.
Generalize Dependent  (extend_prop a).
Generalize Dependent (extend_prop2 a).
Case (try_extend a).
Intros;NewDestruct s.
Inversion_clear H2.
Inversion_clear H3.
Case (classic (span 2!V (seq_set x0))='(full V) in (part_set V)).
Elim H2;Intros.
Generalize Dependent (H7 H8);Intro p;Simpl in p.
Clear H6 H5 H2 H3 a0 a H IHn.
Clear H0 v k H7 H8.
Inversion_clear H4.
Simpl in H;Generalize Dependent (H p);Intros.
Apply has_n_elements_comp with x (seq_set x0);Simpl;Auto with algebra.
Generalize Dependent (seq_equal_seq_set H2).
Simpl;Auto.
Clear H2 H4.
Inversion_clear H6.
Intro.
Generalize Dependent (H3 H4);Intro p;Simpl in p.
Clear H2 H3.
Generalize Dependent x2.
Rewrite p.
Intros.
Apply has_n_elements_comp with (S x) (seq_set (head x2);;x0).
3:Simpl;Auto.
2:Apply Trans with (seq_set (head x2);;(Seqtl x2));Auto with algebra.
Generalize Dependent (H5 (Refl (S x)::Nat)).
Clear H4 H5;Intro p'.
Clear p x1 H0 H v k IHn n.
Apply seq_set_n_element_subset.
Exists (head x2);;x0.
Split;Auto with algebra.
Apply distinct_comp with x2.
Inversion_clear a0;Auto.
Apply Trans with (head x2);;(Seqtl x2);Auto with algebra.
Qed.
End prelim.

Section MAIN.
Variable F:field.
Variable V:(findimvecsp F).

Variable W:(subspace V).

Local H : (lin_indep (seq_set (empty_seq W)))/\(distinct (empty_seq W)).
Split;Try Apply lin_indep_comp with (empty W);Auto with algebra.
Apply empty_lin_indep.
Intro.
Auto with algebra.
Qed.

Lemma grow_bound : (n:nat)Cases (rep_ext n H) of (existT i (existT w H')) => (le i n) end.
Intros;Move n after W.
NewInduction n.
Simpl.
Auto.
Generalize Dependent IHn.
LetTac re := (rep_ext n H).
Change Cases re of (existT i (existT w _)) => (le i n) end 
         -> Cases (Cases re of (existT i (existT w H')) => (try_extend H') end)
              of (existT i (existT w _)) => (le i (S n)) end.
Case re.
Intros x s.
NewDestruct s.
Intros.
Generalize Dependent  (extend_prop a).
Case (try_extend a).
Intros x1 s;NewDestruct s.
Case (classic (span 2!W (seq_set x0))='(full W) in (part_set W)).
Intros.
Inversion_clear H2.
Clear H4;Elim H3;Intros p q.
Generalize Dependent (q H1);Intro r;Simpl in r.
Rewrite r.
Auto with arith.
Intros.
Inversion_clear H2.
Clear H3;Elim H4;Intros p q.
Generalize Dependent (q H1);Intro r;Simpl in r.
Rewrite r.
Auto with arith.
Qed.


Local n:=(the_dim V).
(** - %\intoc{\bf Theorem 1.11}% *)
Lemma subspace_preserves_findimvecsp : (sigT nat [m] (le m n) /\ (has_dim m W)).

Generalize Dependent grow_bound;Intro H0.

Assert (has_n_elements O (seq_set (empty_seq W))).
Apply has_n_elements_comp with O (empty W);Auto with algebra.

Assert (n:nat)Cases (rep_ext n H) of  (existT i (existT w _)) =>
 (has_n_elements i (seq_set w))  end.
Clear n;Intro n.
Move n after W.
Apply grow_nr_elts.
Auto.

LetTac re_i := Cases (rep_ext n H) of (existT i _) => i end.

Exists re_i.
Split.
Unfold re_i.
Generalize Dependent (H0 n).
Case (rep_ext n H).
Intros x s.
NewDestruct s.
Auto.

Cut (Cases (rep_ext n H) of (existT i (existT w H)) => (is_basis (seq_set w)) end).
Intro.
Generalize Dependent (H2 n).
NewDestruct (rep_ext n H).
NewDestruct s.
Intro.
Apply has_dim_easy with (seq_set x0).
Auto.
Unfold re_i.
Auto.

Clear re_i.
Unfold is_basis.

Assert (n:nat)Cases (rep_ext n H) of (existT i (existT w H)) => 
  (lt i n)->(span (seq_set w))='(full W) in (part_set W) end.
Clear n;NewInduction n.
Intro.
Inversion_clear H3.

Simpl.
LetTac re := (rep_ext n0 H).
Change Cases Cases re of (existT i (existT w H'))=>(try_extend H') end of
  (existT i' (existT w' _)) => (lt i' (S n0))->(span_set (seq_set w'))='(full W) end.
Generalize Dependent IHn0.
Case re.
Intros x s;NewDestruct s.
Intros.
Generalize Dependent (extend_prop2 a).
Generalize Dependent (extend_prop a).
Case (try_extend a).
Intros x' s;NewDestruct s.
Intros.
Inversion_clear H4;Inversion_clear H3.
Inversion_clear H4;Inversion_clear H6(*;Inversion_clear H7*);Inversion_clear H8.
Case (classic (span (seq_set x0))='(full W) in (part_set W)).
Intro.
Generalize Dependent (H9 H8);Intro p;Generalize Dependent (H4 p);Intro q.
Apply Trans with (span_set (seq_set x0));Auto with algebra.
Generalize Dependent span_comp;Intro r;Simpl in r;Simpl.
Apply (r?W).
Generalize Dependent seq_equal_seq_set.
Simpl.
Auto with algebra.

Intro.
Assert ~(lt x n0).
Intro;Repeat Red in H8;Apply H8.
Apply IHn0;Auto with algebra arith.
Apply False_ind.
Generalize Dependent (H11 H8);Intro p;Simpl in p;Generalize Dependent H5.
Rewrite p;Intro.
Red in H12;Apply H12;Auto with arith.

Generalize Dependent (H0 n).
Generalize Dependent (H2 n).
Generalize Dependent (H3 n).

Case (rep_ext n H).
Intros x s;NewDestruct s.
Intros.
Case (le_lt_or_eq ?? H6).
Intro.
Split;Inversion_clear a;Auto.
Red;Auto.

Clear H4 H3 H2 H1 H0 H.
Intro.
Move H after x0.
Generalize Dependent x0.
Rewrite H.
Clear H6 H x;Intros.
Split;Inversion_clear a;Auto.

Assert (lin_indep (inject_subsets (seq_set x0))).
Red;Repeat Red in H;Intro;Apply H.
Elim (inject_subsets_lin_dep (seq_set x0));Intuition.
Assert (has_n_elements n (inject_subsets (seq_set x0))).
Apply inject_subsets_preserves_has_n_elements.
Auto.
Red.

Assert (is_basis (inject_subsets (seq_set x0))).
Generalize Dependent (dim_prf V).
Fold n.
Intros.
Inversion_clear H3.
Apply (finite_bases_always_equally_big H4);Auto with algebra.
Red in H3.
Inversion_clear H3.
Red in H4.

Assert (span_ind (inject_subsets (seq_set x0)))='(full V) in(part_set V).
Apply Trans with ((span 2!V (inject_subsets (seq_set x0)))::(part_set V));Auto with algebra.

Apply Trans with ((span_ind (seq_set x0))::(part_set W));Auto with algebra.
Simpl.
Red.
Split;Simpl;Auto;Intros _.
Simpl in H3;Red in H3.
Elim (H3 (subtype_elt x));Intros.
Simpl in H8.
Generalize (H8 I);Clear H8 H7 H6 H4 H2 H1 H0 H H5.
Intro.
Inversion_clear H.
Unfold subtype_image_equal.

Exists (span_ind_uninject x1).

Apply Trans with (span_ind_injection x1);Auto with algebra.
Apply span_ind_uninject_prop.
Qed.
End MAIN.
