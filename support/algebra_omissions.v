(** %\subsection*{ support :  algebra\_omissions.v }%*)
(** - In this file I prove some results that do not pertain to linear algebra at all.
 Instead, they could have been proven solely for the algebra distribution. This is
 also why I do not use the syntactic sugar as defined in equal_syntax.v and 
 more_syntax.v *)

Require Export Group_facts.
Set Implicit Arguments.

Lemma group_inverse_inj : (G:GROUP;g,g':G)
  (Equal (group_inverse ? g) (group_inverse ? g'))
    -> (Equal g g').
Intros.
Apply Trans with (group_inverse ? (group_inverse ? g));Auto with algebra.
Apply GROUP_law_inverse.
Apply Trans with (sgroup_law ? (group_inverse ? g') g');Auto with algebra.
Qed.

(* Because of later notation, this should also be known as: *)

Definition min_inj := group_inverse_inj.


(** - Elements of subsets are really pairs of those elements and proofs that they belong
 to that subset. I prove that two of these pairs are equal (in the subsetoid) iff their
 first projections are (in the parent setoid) *)

Lemma subtype_elt_comp : (A:Setoid;B:(part_set A);b,b':B) 
  (Equal b b')
    -> (Equal (subtype_elt b) (subtype_elt b')).
Simpl.
Unfold subtype_image_equal.
Auto with algebra.
Qed.

Lemma subtype_elt_inj : (A:Setoid;B:(part_set A);b,b':B) 
  (Equal (subtype_elt b) (subtype_elt b'))
    -> (Equal b b').
Simpl.
Unfold subtype_image_equal.
Auto with algebra.
Qed.

Hints Resolve subtype_elt_comp : algebra.

Lemma in_part_subtype_elt : (A:Setoid;B:(part_set A);b:B)
  (in_part (subtype_elt b) B).
Intros.
Red.
Apply subtype_prf.
Qed.

Hints Resolve in_part_subtype_elt : algebra.


(** - The setoid mechanism as defined in the algebra contribution makes for a 'layered'
 structure when dealing with subsets. Suppose $C\subset B\subset A$. This is translated
 as [A:Setoid; B:(part_set A); C:(part_set B)]. But obviously also $C\subset A$. Now
 [inject_subsets] injects a subset of B into the subsets of [A]

 %\label{injectsubsets}% *)

Definition inject_subsets: (A:Setoid;B:(part_set A)) (part_set B)->(part_set A).
Intros A B C.
Apply (Build_Predicate 2![a:A](EXT c:C | (Equal a (subtype_elt (subtype_elt c))))).
Red.
Intros.
NewDestruct H.
Generalize Dependent x0;Intro c;Intros.
Exists c.
Apply Trans with x;Auto with algebra.
Defined.

Lemma inject_subsets_comp : (A:Setoid;B:(part_set A);C,C':(part_set B)) 
  (Equal C C') 
    -> (Equal (inject_subsets C) (inject_subsets C')).
Intros.
Simpl in H;Simpl.
Red in H;Red.
Intro a;Split;Intros.
Simpl;Simpl in H0.
NewDestruct H0.
Elim (H (C x)).
Intros.
Assert (in_part (C x) C).
Simpl.
Auto with algebra.
Generalize (H1 H3);Clear H1 H2 H3;Intro.
Red in H1.
Exists (Build_subtype H1).
Simpl.
Auto.

Simpl;Simpl in H0.
NewDestruct H0.
Elim (H (C' x)).
Intros.
Assert (in_part (C' x) C').
Simpl.
Auto with algebra.
Generalize (H2 H3);Clear H1 H2 H3;Intro.
Red in H1.
Exists (Build_subtype H1).
Simpl.
Auto.
Qed.

Hints Resolve inject_subsets_comp: algebra.

Lemma inject_subsets_of_part_set_included : (A:Setoid;B:(part_set A);C:(part_set B))
  (included (inject_subsets C) B).
Intros.
Unfold included inject_subsets.
Simpl.
Intros.
Inversion_clear H.
Apply in_part_comp_l with (subtype_elt (subtype_elt x0));Auto with algebra.
Qed.

Hints Resolve inject_subsets_of_part_set_included : algebra.

Lemma inject_subsets_full_inv : (A:Setoid;B:(part_set A)) 
  (Equal (inject_subsets (full B)) B).
Intros.
Simpl.
Red.
Split;Intros.
Simpl in H.
Inversion_clear H.
NewDestruct x0.
Simpl in H0.
Generalize Dependent subtype_elt;Intro b;Intros.
Apply in_part_comp_l with (subtype_elt b);Auto with algebra.

Simpl.
Red in H.
LetTac b:=((Build_subtype H)::B).
Assert (in_part b (full B));Simpl;Auto.
Red in H0.
Exists (Build_subtype H0).
Simpl.
Auto with algebra.
Qed.

Hints Resolve inject_subsets_full_inv : algebra.

(** - Once we have [inject_subsets], we may need to view an element of [C] as an element
of the injected subset: so, if [x:C] then [(inject_subsetsify x):(inject_subsets C)]

 %\label{injectsubsetsify}% *)

Definition inject_subsetsify : (A:Setoid;B:(part_set A)) 
  (C:(part_set B)) C->(inject_subsets C).
Intros A B C c.
LetTac c':=(B (C c)).
Assert (EXT c:C | (Equal c' (subtype_elt (subtype_elt c)))).
Exists c.
Unfold c';Simpl.
Auto with algebra.
Exists c'.
Auto.
Defined.

Lemma inject_subsetsify_comp : (A:Setoid;B:(part_set A);C:(part_set B);c,c':C)
  (Equal c c')
    -> (Equal (inject_subsetsify c) (inject_subsetsify c')).
Intros.
Simpl.
Red.
Simpl.
Auto with algebra.
Qed.


(** - ...and vice versa: if [x:(inject_subsets C)] then [(uninject_subsets x):C]

 %\label{uninjectsubsetsify}% *)

Definition uninject_subsetsify : (A:Setoid;B:(part_set A)) 
  (C:(part_set B)) (inject_subsets C)->C.
Intros.
Simpl.
NewDestruct X.
Generalize Dependent subtype_elt.
Intros a Ha.
Simpl in Ha.
Assert (in_part a B).
Inversion_clear Ha.
Apply in_part_comp_l with (subtype_elt (subtype_elt x));Auto with algebra.
Red in H.
Exists (Build_subtype H).
Change (in_part ((Build_subtype H)::B) C).
Inversion_clear Ha.
Apply in_part_comp_l with (subtype_elt x);Auto with algebra.
Defined.

Lemma uninject_subsetsify_comp : (A:Setoid;B:(part_set A)) (C:(part_set B))
  (fun_compatible (!uninject_subsetsify A B C)).
Red.
Intros.
Unfold uninject_subsetsify.
NewDestruct x;NewDestruct y.
Simpl.
Red.
Simpl.
Auto with algebra.
Qed.

Lemma in_part_included : (A:Setoid;B,C:(part_set A);a:A) 
  (in_part a B)->(included B C)->(in_part a C).
Intros.
Red in H0.
Auto.
Qed.

Lemma exists_difference : (n,m:nat)(le n m)->(EXT q:nat | m = (plus n q)).
NewInduction m.
NewDestruct n.
Intro;Exists O;Auto.
Intro;Inversion_clear H.
Intro.
Inversion_clear H.
Exists O;Auto.
Generalize (IHm H0);Intro p;Inversion_clear p.
Exists (S x).
Transitivity (plus (S n) x).
Simpl.
Apply f_equal with f:=S.
Auto.
Simpl.
Apply plus_n_Sm.
Qed.
