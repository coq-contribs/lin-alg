(** %\subsection*{ examples :  infinite\_sequences.v }%*)
(** - The vectorspaces $F^\infty$, done in the new-fangled way using
 alt_build_vecspace; the final interactive definition requires only 3 lines (9 tactics) *)
Set Implicit Arguments.
Require Export alt_build_vecsp.

Section MAIN.
Variable F:field.
Definition infseq : Setoid.
Apply (Build_Setoid 2![s,s':nat->F](i:nat)(s i)='(s' i)).
Split;Try Split;Red;Unfold app_rel;Simpl;Auto with algebra.
Intros.
(Apply Trans with (y i);Auto with algebra).
Defined.

Definition addinfseqs : (Map2 infseq infseq infseq).
(Apply (Build_Map2 4![s,s':infseq](([i:nat](s i)+'(s' i))::infseq));Auto with algebra).
Red;Simpl.
Auto with algebra.
Defined.

Definition mltinfseqs : (Map2 F infseq infseq).
Apply (Build_Map2 4![c:F;s':infseq](([i:nat]c rX(s' i))::infseq)).
Red;Simpl.
Auto with algebra.
Defined.

Definition zeroseq : infseq := [n](zero F).

Definition minusseq : (Map infseq infseq).
Apply Build_Map with [s:infseq;n:nat](min (s n)).
Red.
Intros.
Simpl.
Simpl in H.
Intros.
Apply GROUP_comp.
Auto.
Defined.

Definition vecspace_infseq : (vectorspace F).
Apply (!alt_Build_vectorspace infseq F addinfseqs mltinfseqs zeroseq minusseq);Red;Simpl;Intros;Auto with algebra.
Apply Trans with (x i)+'(zero F);Auto with algebra.
Apply Trans with (zero F);Auto with algebra.
Defined.
End MAIN.