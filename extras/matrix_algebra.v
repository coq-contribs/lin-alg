(** %\subsection*{ extras :  matrix\_algebra.v }%*)
(** - This is not used, but nice anyway: $n\times n$-matrices over $F$ form
 an algebra (over $F$) *)

Require Export Matrices. 
Require Export Algebra.

Require Export vecspace_Mmn.
Require Export Cfield_facts.
Variable F:cfield.
Definition Mmn_alg [n:nat] : (algebra F).
Intros.
Apply Build_algebra with (Mmn F n n).
Apply Build_algebra_on.
Simpl.
Require Export Matrix_multiplication.

Local mult_arr : (n:nat)(Mmn F n n)-> (sgroup_hom (Mmn F n n) (Mmn F n n)).
Intros.
Apply Build_sgroup_hom with (Ap2_Map (matXmat F n n n) X).
Red.
Intros.
Simpl.
Intros.
(Apply Trans with (sum (pointwise (uncurry (RING_comp 1!F)) (row X i) ((col x j)+'(col y j))));Auto with algebra).
Apply Trans with ((sum (pointwise (uncurry (RING_comp 1!F)) (row X i) (col x j))) +' (sum (pointwise (uncurry (RING_comp 1!F)) (row X i) (col y j)))).
Require Export random_facts.
Apply Trans with (sum (pointwise (sgroup_law_map F) (pointwise (uncurry (RING_comp 1!F)) (row X i) (col x j)) (pointwise (uncurry (RING_comp 1!F)) (row X i) (col y j)))).
2:(Apply (!sum_of_sums n F
(pointwise (uncurry (RING_comp 1!F)) (row X i) (col x j))
(pointwise (uncurry (RING_comp 1!F)) (row X i) (col y j)));Auto with algebra).
(Apply sum_comp;Auto with algebra).
Simpl.
Red.
Intros.
Simpl.
(Apply Trans with ((X i x0)rX(x x0 j)) +' ((X i x0)rX(y x0 j));Auto with algebra).
Generalize row_comp;Intro Hr;Simpl in Hr.
Generalize col_comp;Intro Hc;Simpl in Hc.
Apply SGROUP_comp.
Apply sum_comp.
Simpl.
Red.
Simpl.
NewDestruct x;NewDestruct X.
Intro.
Simpl.
Apply RING_comp.
Red in Ap2_comp_proof0.
Auto with algebra.
Red in Ap2_comp_proof.
Auto with algebra.
Apply sum_comp.
Simpl.
Red.
Simpl.
NewDestruct y;NewDestruct X.
Intro.
Simpl.
Apply RING_comp.
Red in Ap2_comp_proof0.
Auto with algebra.
Red in Ap2_comp_proof.
Auto with algebra.
Defined.

Local mult_arr_mon : (n:nat)(Mmn F n n)->(monoid_hom (Mmn F n n) (Mmn F n n)).
Intros.
Apply Build_monoid_hom with (mult_arr n X).
Red.
Simpl.
Intros.
(Apply Trans with (sum (const_seq n (zero F)));Auto with algebra).
Apply sum_comp.
Simpl.
Red.
Simpl.
Auto with algebra.
Defined.

Local mult_arr_mod : (n:nat)(Mmn F n n)->(module_hom (Mmn F n n) (Mmn F n n)).
Intros.
Apply Build_module_hom with (mult_arr_mon n X).
Red.
Intros.
Simpl.
Intros.
Apply Trans with (a rX (sum (pointwise (uncurry (RING_comp 1!F)) (row X i) (col x j)))).
2:(Apply RING_comp;Auto with algebra).
2:Apply sum_comp.
2:Simpl.
2:Red.
2:Simpl.
2:Intro.
2:(Apply RING_comp;Auto with algebra).
2:NewDestruct X.
2:Simpl.
2:Red in Ap2_comp_proof.
2:Auto with algebra.
2:NewDestruct x.
2:Simpl.
2:Red in Ap2_comp_proof.
2:Auto with algebra.
Apply Trans with (sum (pointwise (uncurry (RING_comp 1!F)) (const_seq n a) (pointwise (uncurry (RING_comp 1!F)) (row X i) (col x j)))).
Apply sum_comp.
Simpl.
Red.
Intro.
Simpl.
Auto with algebra.
Apply Sym.
Require Export distribution_lemmas.
Apply RING_sum_mult_dist_l.
Defined.

Local mult_map_mod : (n:nat)(Map (Mmn F n n) (Hom_module (Mmn F n n) (Mmn F n n))).
Intros.
Apply Build_Map with (mult_arr_mod n).
Red.
Intros;Simpl.
Simpl in H.
Red;Simpl.
Intros.
Apply sum_comp.
Simpl.
Red.
Intro.
Simpl.
NewDestruct x0.
Simpl.
Red in Ap2_comp_proof.
(Apply RING_comp;Auto with algebra).
Defined.

Local mult_sgp_mod : (n:nat)(sgroup_hom (Mmn F n n) (Hom_module (Mmn F n n) (Mmn F n n))).
Intros.
Apply Build_sgroup_hom with (mult_map_mod n).
Red.
Intros;Simpl.
Red;Intros.
Simpl.
Intros.
(Apply Trans with (sum (pointwise (uncurry (RING_comp 1!F)) (row (x +' y) i') (col x0 j')));Auto with algebra).
Apply sum_comp.
Simpl.
Red.
Simpl.
Intro.
NewDestruct x;NewDestruct y;NewDestruct x0;Simpl.
Red in Ap2_comp_proof Ap2_comp_proof0 Ap2_comp_proof1.
(Apply RING_comp;Auto with algebra).
Apply Trans with (sum (pointwise (sgroup_law_map F)
  (pointwise (uncurry (RING_comp 1!F)) (row x i') (col x0 j'))
  (pointwise (uncurry (RING_comp 1!F)) (row y i') (col x0 j')))).
Apply sum_comp.
Simpl.
Red.
Simpl.
Intro.
(Apply Trans with ((x i' x1) rX (x0 x1 j')) +' ((y i' x1) rX (x0 x1 j'));Auto with algebra).
Generalize sum_of_sums.
Intros.
Apply (H1 n F (pointwise (uncurry (RING_comp 1!F)) (row x i') (col x0 j')) (pointwise (uncurry (RING_comp 1!F)) (row y i') (col x0 j'))).
Defined.

Local mult_mon_mod :  (n:nat)(monoid_hom (Mmn F n n) (Hom_module (Mmn F n n) (Mmn F n n))).
Intros.
Apply Build_monoid_hom with (mult_sgp_mod n).
Red.
Simpl.
Red.
Intro.
Simpl.
Intros.
Apply Trans with (sum (const_seq n (zero F))).
Apply sum_comp.
Simpl.
Red.
Simpl.
Auto with algebra.
Apply sum_of_zeros;Auto with algebra.
Defined.

Apply Build_module_hom with (mult_mon_mod n).
Red.
Intros;Simpl.
Red.
Intro;Simpl.
Intros.
Apply Trans with (sum (pointwise (uncurry (RING_comp 1!F)) (const_seq n a) (pointwise (uncurry (RING_comp 1!F)) (row x i') (col x0 j')))).
Apply sum_comp.
Simpl.
Red.
Simpl.
Intro.
(Apply Trans with (a rX (x i' x1))rX(x0 x1 j');Auto with algebra).
(Apply RING_comp;Auto with algebra).
(Apply RING_comp;Auto with algebra).
NewDestruct x;Red in Ap2_comp_proof;Simpl;Auto with algebra.
NewDestruct x0;Red in Ap2_comp_proof;Simpl;Auto with algebra.
Apply Sym.
Auto with algebra.
Defined.

Grammar constr constr0 :=
 algebramult [constr0($a) "aX" constr0($b)] -> [(algebra_mult $a $b)].
Syntax constr level 10 : algebramult [(algebra_mult $a $b)] -> [[<hv 0>$a:L [0 3] [<h 0> " aX " $b:L]]].

