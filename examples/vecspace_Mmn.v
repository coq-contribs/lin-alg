(** %\subsection*{ examples :  vecspace\_Mmn.v }%*)
(** - The vectorspace of $n\times m$ matrices over $F$ *)
Set Implicit Arguments.
Require Export Matrices.

Section Vectorspace.
Variable F:field.
Variable m,n:Nat.

Definition Mmn_set : SET.
Simpl.
Apply (!Build_Setoid (matrix F m n) [M,M':(matrix F m n)](i,i':(fin m);j,j':(fin n))i='i'->j='j'->(M i j) =' (M' i' j')).
Split;Try Split;Red;Unfold app_rel.
(*Refl*)
Intros.
Elim x.
Auto with algebra.
(*Trans*)
Intros.
(Apply Trans with (y i j);Auto with algebra).
(*Sym*)
Intros.
(Apply Sym;Auto with algebra).
Defined.

Local add_law: (law_of_composition Mmn_set).
Simpl.
Exact (Map2_Mapcart (!matrix_addition F m n)::(MAP2 Mmn_set Mmn_set Mmn_set)).
Defined.

Definition Mmn_sgp : SGROUP.
Apply (Build_sgroup 1!Mmn_set).
Apply (Build_sgroup_on 2!add_law).
Red.
Simpl.
NewDestruct x;NewDestruct y;NewDestruct z.
Simpl.
Intros.
(Apply Trans with (((Ap2 i' j') +' (Ap0 i' j')) +' (Ap1 i' j'));Auto with algebra).
Defined.

Definition Mmn_mon : MONOID.
Apply (Build_monoid 1!Mmn_sgp).
Apply (Build_monoid_on 2!((zero_matrix F m n)::(Mmn_sgp)));Red;Intros;Simpl;NewDestruct x.
Intros;Simpl.
(Apply Trans with (Ap2 i j);Auto with algebra).
Intros;Simpl.
(Apply Trans with (Ap2 i j);Auto with algebra).
Defined.

Section group.
Local minmatrix : Mmn_mon->Mmn_mon.
Intro M.
Apply (Build_Map2 4![i,j](min (M i j))).
Red.
Intros.
(Apply GROUP_comp;Auto with algebra).
NewDestruct M;Auto with algebra.
Defined.

Local minmatrixmap : (Map Mmn_mon Mmn_mon).
Apply (Build_Map 3!minmatrix).
Red.
Intros;Simpl.
NewDestruct x;NewDestruct y;Simpl.
Intros.
(Apply Trans with (min (Ap0 i j));Auto with algebra).
Defined.

Definition Mmn_gp : GROUP.
Apply (Build_group 1!Mmn_mon).
Apply (Build_group_on 2!minmatrixmap);Red;Intros;Simpl;Intros;Auto with algebra.
Defined.
End group.

Definition Mmn_abgp : ABELIAN_GROUP.
Apply (Build_abelian_group 1!Mmn_gp).
Apply (Build_abelian_group_on 1!Mmn_gp).
Apply (Build_abelian_monoid_on 1!Mmn_gp).
Apply (Build_abelian_sgroup_on 1!Mmn_gp).
Red.
Simpl.
Intros;NewDestruct x;NewDestruct y;Simpl.
(Apply Trans with (Ap0 i j) +' (Ap2 i j);Auto with algebra).
Defined.

Section module.
Local scmult_sgp_fun : F->(Endo_SET Mmn_abgp).
Intro c.
Simpl.
Apply (Build_Map 3!(matrix_scmult F m n c)).
Red.
Case matrix_scmult.
Unfold fun2_compatible.
Intros.
(Apply Ap2_comp_proof;Auto with algebra).
Defined.

Local scmult_sgp_map : (Map (Build_monoid (ring_monoid F)) (Endo_SET Mmn_abgp)).
(Apply (Build_Map 3!scmult_sgp_fun);Auto with algebra).
Red.
Intros; Unfold scmult_sgp_fun.
Simpl.
Red;Simpl.
Intros.
(Apply RING_comp;Auto with algebra).
Elim x0.
Intros p q;Red in q.
Simpl;Auto with algebra.
Defined.

Local scmult_sgp_hom : (sgroup_hom (Build_monoid (ring_monoid F)) (Endo_SET Mmn_abgp)).
Apply (Build_sgroup_hom 3!scmult_sgp_map).
Red.
Simpl.
Red.
Simpl.
Intros.
NewDestruct x0.
Red in Ap2_comp_proof.
(Apply Trans with (x rX (y rX (Ap2 i j)));Auto with algebra).
Simpl.
(Apply Trans with (x rX y) rX (Ap2 i j);Auto with algebra).
Defined.

Local scmult_mon_hom : (monoid_hom (Build_monoid (ring_monoid F)) (Endo_SET Mmn_abgp)).
Apply (Build_monoid_hom 3!scmult_sgp_hom).
Red.
Simpl.
Red.
Simpl.
Intros.
NewDestruct x.
Red in Ap2_comp_proof.
Simpl.
(Apply Trans with (Ap2 i j);Auto with algebra).
(Apply Trans with one rX (Ap2 i j);Auto with algebra).
Defined.

Definition Mmn : (VECSP F).
Apply (Build_module 1!F 2!Mmn_abgp).
Apply (Build_module_on 3!scmult_mon_hom);Red.
Simpl;Intros.
NewDestruct x.
Simpl.
(Apply Trans with ((a rX (Ap2 i j)) +' (b rX (Ap2 i j)));Auto with algebra).
Simpl;Intros.
(Apply Trans with ((a rX (x i j)) +' (a rX (y i j)));Auto with algebra).
NewDestruct x;NewDestruct y;(Apply SGROUP_comp;Auto with algebra).
Defined.
End module.
End Vectorspace.

Definition row_Map2 : (F:field;m,n:Nat)(MAP2 (Mmn F m n) (fin m) (Fn F n)).
Intros.
Apply (Build_Map2 4!(!row F m n)).
Red;Simpl.
Red;Simpl.
Intros.
NewDestruct x;NewDestruct x';Simpl.
Simpl in H.
(Apply Trans with (Ap0 y x0);Auto with algebra).
Defined.

Definition col_Map2 : (F:field;m,n:Nat)(MAP2 (Mmn F m n) (fin n) (Fn F m)).
Intros.
Apply (Build_Map2 4!(!col F m n)).
Red;Simpl.
Red;Simpl.
Intros.
NewDestruct x;NewDestruct x';Simpl.
Simpl in H.
(Apply Trans with (Ap0 x0 y);Auto with algebra).
Defined.
