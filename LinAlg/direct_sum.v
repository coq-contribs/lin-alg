(** * direct_sum.v *)
Set Implicit Arguments.
Require Export algebraic_span_facts.

Section MAIN.
Variable F:field.
Variable V:(vectorspace F).
(** - A vectorspace being a direct sum is only defined as a predicate; the sum_set
 however is defined as a construction:
%\tocdef{sum\_set}% *)
Definition sum_set [S1,S2:(part_set V)] : (part_set V).
Intros.
Simpl.
Apply Build_Predicate with [x:V](EXT s1:S1 | (EXT s2:S2 | x =' ((subtype_elt s1) +' (subtype_elt s2)))).
Red.
Intros.
Inversion_clear H.
Inversion_clear H1.
Exists x0.
Exists x1.
Apply Trans with x;Auto with algebra.
Defined.

Lemma subspace_sum_set : (W1,W2:(part_set V))
  (is_subspace W1) -> (is_subspace W2) -> (is_subspace (sum_set W1 W2)).
Unfold is_subspace;Intuition.
Simpl.
Red in H1 H.
Exists (Build_subtype H1).
Exists (Build_subtype H).
Simpl.
Auto with algebra.

Simpl in H3 H6.
Inversion_clear H3;Inversion_clear H6.
Inversion_clear H7;Inversion_clear H3.
NewDestruct x0;NewDestruct x1;NewDestruct x2;NewDestruct x3.
Generalize (H0??subtype_prf subtype_prf0).
Generalize (H2??subtype_prf1 subtype_prf2).
Intros.
Red in H3 H8.
Exists (Build_subtype H8).
Exists (Build_subtype H3).
Simpl.
Simpl in H6 H7.
Apply Trans with (subtype_elt+'subtype_elt1)+'(subtype_elt0+'subtype_elt2);Auto with algebra.

Simpl in H3.
Inversion_clear H3.
Inversion_clear H6.
NewDestruct x0;NewDestruct x1.
Generalize (H4 c?subtype_prf).
Generalize (H5 c?subtype_prf0).
Intros.
Simpl in H3;Simpl.
Red in H6 H7.
Exists (Build_subtype H7).
Exists (Build_subtype H6).
Simpl.
Apply Trans with c mX (subtype_elt+'subtype_elt0);Auto with algebra.
Qed.

(** %\tocdef{form\_direct\_sum}% *)
Definition form_direct_sum : (subspace V)->(subspace V)->Prop :=
  [W1,W2](inter W1 W2)='(single (zero V))/\ (sum_set W1 W2)='(full V).
End MAIN.

Section Example.
Require symmetric_matrices.
Require antisymmetric_matrices.

(** - Example 26 on page 20 is actually WRONG, or at least incomplete: if the field is
 $\mathbf Z/2\mathbf Z = \{0,1\}$, where $-1=1$, then symmetric and antisymmetric
 matrices coincide, and $M_{nn}$ cannot be split in just the symmetric and
 antisymmetric part. Hence the extra condition that $1+1\neq0$: *)
Lemma matrixspace_sym_antisym : (n:nat;F:field)(~one+'one='(zero F))->(form_direct_sum (symm_subspace n F) (antisym_subspace n F)).
Split.
Intro.
Split.
Simpl;Intuition.
Clear H3 H0 j' i'.
Cut (x i j)='(x j i).
Intro.
Cut (x i j)='(min (x j i)).
Intro.
Assert (x i j)+'(x i j)='(x j i)+'(min (x j i));Auto with algebra.
Assert (x i j)+'(x i j)='(zero F).
Apply Trans with (x j i)+'(min (x j i));Auto with algebra.
Assert (one rX (x i j))+'(one rX (x i j)) =' (zero F).
Apply Trans with (x i j)+'(x i j);Auto with algebra.
Assert (one +' one) rX (x i j) =' (one+'one)rX(zero F).
Apply Trans with(one rX (x i j))+'(one rX (x i j));Auto with algebra.
Apply Trans with (zero F);Auto with algebra.
Apply FIELD_reg_left with (one::F)+'(one::F);Auto with algebra.

Unfold antisym_subspace in H2.
Unfold alt_Build_subspace in H2.
Generalize Dependent H2.
Case (subspace_construction (antisymm_matr_subspace n F)).
Intros.
Simpl in e.
Red in e.
Elim (e x);Intros.
Generalize Dependent (H3 H2);Intro p;Simpl in p.
Red in p.
Auto.

Unfold symm_subspace in H1.
Unfold alt_Build_subspace in H1.
Generalize Dependent H1.
Case (subspace_construction (symm_matr_subspace n F)).
Intros.
Simpl in e.
Red in e.
Elim (e x);Intros.
Generalize Dependent (H0 H1);Intro p;Simpl in p.
Red in p.
Auto.

Intro p;Simpl in p.
Simpl.
Split.
Unfold symm_subspace.
Unfold alt_Build_subspace.
Case (subspace_construction (symm_matr_subspace n F)).
Intros.
Simpl in e;Red in e.
Elim (e x);Intros.
Apply H1.
Simpl.
Red.
Assert (i,j:(fin n))(x i j)='(zero F).
Intros;Apply p with i j;Auto with algebra.

Intros;Apply Trans with (zero F);Auto with algebra.

Unfold antisym_subspace.
Unfold alt_Build_subspace.
Case (subspace_construction (antisymm_matr_subspace n F)).
Intros.
Simpl in e;Red in e.
Elim (e x);Intros.
Apply H1.
Simpl.
Red.
Assert (i,j:(fin n))(x i j)='(zero F).
Intros;Apply p with i j;Auto with algebra.

Intros;Apply Trans with (zero F);Auto with algebra.
Apply Trans with (min (zero F));Auto with algebra.

Split;Intros.
Simpl.
Auto.

Clear H0.
Simpl.
LetTac x_s := (field_inverse ((one::F)+'(one::F))) mX (x+'(transpose x)).
Assert (in_part x_s (symm_subspace n F)).
Unfold symm_subspace.
Unfold alt_Build_subspace.
Case (subspace_construction (symm_matr_subspace n F)).
Intros.
Simpl in e;Red in e.
Elim (e x_s);Intros.
Apply H1.
Simpl.
Red.
Unfold x_s.
Intros.
Apply Trans with (field_inverse 1!F (ring_unit F)+'(ring_unit F))rX((x+'(transpose x)) i j);Auto with algebra.
Apply Trans with (field_inverse 1!F (ring_unit F)+'(ring_unit F))rX((x+'(transpose x)) j i);Auto with algebra.
Apply RING_comp;Auto with algebra.
Unfold transpose;Simpl.
Case x.
Simpl.
Auto with algebra.

LetTac x_a := (field_inverse ((one::F)+'(one::F))) mX (x+'(min ((transpose x)::(Mmn F n n)))).
Assert (in_part x_a (antisym_subspace n F)).
Unfold antisym_subspace.
Unfold alt_Build_subspace.
Case (subspace_construction (antisymm_matr_subspace n F)).
Intros.
Simpl in e;Red in e.
Elim (e x_a);Intros.
Apply H2.
Simpl.
Red.
Unfold x_a.
Intros.
Apply Trans with (field_inverse 1!F (ring_unit F)+'(ring_unit F))rX(x+'(min ((transpose x)::(Mmn F n n))) i j);Auto with algebra.
Apply Trans with (min (field_inverse 1!F (ring_unit F)+'(ring_unit F))rX(x+'(min ((transpose x)::(Mmn F n n))) j i));Auto with algebra.
Apply Trans with (field_inverse 1!F (ring_unit F)+'(ring_unit F))rX(min (x+'(min ((transpose x)::(Mmn F n n))) j i));Auto with algebra.
Apply RING_comp;Auto with algebra.
Unfold transpose;Simpl.
Case x.
Simpl.
Intros.
Apply Trans with (min (Ap2 j i))+'(min (min (Ap2 i j))).
Apply Trans with (min (min (Ap2 i j)))+' (min (Ap2 j i));Auto with algebra.
Apply Sym.
Apply Trans with (min (min (Ap2 i j)))+' (min (Ap2 j i));Auto with algebra.

Red in H0 H1.
Exists (Build_subtype H0).
Exists (Build_subtype H1).
Simpl.
Intros.
LetTac half:=(field_inverse (one::F) +' one).
Apply Trans with ((half rX (x i' j'))+'(half rX (transpose x i' j')))+'((half rX (x i' j'))+'(half rX (min (transpose x i' j'))));Auto with algebra.
Apply Trans with ((half rX (x i' j'))+'(half rX (x i' j')))+'((half rX (transpose x i' j'))+'(half rX (min (transpose x i' j'))));Auto with algebra.
Apply Trans with ((half rX (x i' j'))+'(half rX (x i' j')))+'(zero F).
Apply Trans with ((half rX (x i' j'))+'(half rX (x i' j')));Auto with algebra.
Apply Trans with ((half rX (x i j))+'(half rX (x i j)));Auto with algebra.
Apply Trans with one rX (x i j);Auto with algebra.
Apply Trans with ((one+'one)rX half) rX (x i j);Auto with algebra.
Apply RING_comp;Auto with algebra.
Apply Sym;Unfold half;Auto with algebra.
Apply Trans with (one +' one) rX (half rX (x i j));Auto with algebra.
Apply Trans with (one rX (half rX (x i j)))+'(one rX (half rX (x i j)));Auto with algebra.
Assert (x i j)='(x i' j').
Generalize Dependent (Ap2_comp_proof x);Intro p;Red in p;Auto with algebra.
Auto with algebra.
Apply SGROUP_comp;Auto with algebra.
Apply Trans with (half rX (transpose x i' j'))+'(min (half rX (transpose x i' j')));Auto with algebra.
Qed.
End Example.
