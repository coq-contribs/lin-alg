(** %\subsection*{ support :  cast\_seq\_lengths.v }%*)
Set Implicit Arguments.
Require Export finite.

(** - An important and annoying obstacle when dealing with seqs is that 
 v and w belong to the same setoid only if their types are convertible. 
 This means that v:(seq n A) and w:(seq k A) cannot be compared, even if 
 we have a proof that n=k. We cannot even %{\em state}% the equality because 
 the expression v='w is ill-typed! 
 - In this file we provide tools to convert between sequences (and their indices) 
 of the same length, if only we are given a proof of the fact. Note that these 
 casting-functions get in the way of many useful lemmas, unfortunately... *)

Section MAIN.
Lemma lt_comp : (m,n,n':Nat) (lt m n)->(n='n')->(lt m n').
Intros.
Rewrite <- H0.
Auto.
Qed.

(** %\label{castfin}% *)
Definition cast_fin : (n,n':Nat)(fin n)->n='n'->(fin n').
Intros.
NewDestruct X.
Exact (Build_finiteT (lt_comp in_range_prf H)).
Defined.

Lemma cast_fin_comp : (n,n':Nat;i,i':(fin n);H,H':n='n')
  i='i'->(cast_fin i H)='(cast_fin i' H').
Intros until H'.
Unfold cast_fin.
Case i;Case i'.
Simpl.
Auto.
Qed.

Hints Resolve cast_fin_comp : algebra.

Variable A:Setoid.

Definition cast_seq : (n,n':Nat)(seq n A)->n='n'->(seq n' A).
Intros.
NewDestruct X.
LetTac Ap':=[i:(fin n')](Ap (cast_fin i (sym_eq ??? H))).
Assert Mcp': (fun_compatible Ap').
Red;Red in Map_compatible_prf.
Unfold Ap'.
Intros.
(Apply Map_compatible_prf;Auto with algebra).
Exact (Build_Map Mcp').
Defined.

Lemma cast_seq_comp : (n,n':Nat;v,v':(seq n A);H,H':n='n')
  v='v'->(cast_seq v H)='(cast_seq v' H').
Unfold cast_seq.
Intros until H'.
Case v;Case v'.
Simpl.
Red.
Simpl.
Intros.
Red in H0.
Simpl in H0.
(Apply Trans with  (Ap0 (cast_fin x (sym_eq nat n n' H')));Auto with algebra).
Qed.

Hints Resolve  cast_seq_comp : algebra.

Variable n,n':Nat.
Variable v:(seq n A).

Lemma cast_seq_cast_fin : (i:(fin n);H,H':n='n')
  (v i)='(cast_seq v H (cast_fin i H')).
Intros.
Unfold cast_seq cast_fin.
NewDestruct v.
Simpl.
NewDestruct i.
(Apply Map_compatible_prf;Auto with algebra).
Qed.

Lemma cast_seq_cast_fin' : (i:(fin n');H:n =' n';H':n' =' n)
  (cast_seq v H i)='(v (cast_fin i H')).
Intros.
Unfold cast_seq cast_fin.
NewDestruct v.
Simpl.
NewDestruct i.
(Apply Map_compatible_prf;Auto with algebra).
Qed.

Hints Resolve  cast_seq_cast_fin cast_seq_cast_fin' : algebra.
End MAIN.
Hints Resolve cast_fin_comp : algebra.
Hints Resolve  cast_seq_comp : algebra.
Hints Resolve  cast_seq_cast_fin cast_seq_cast_fin' : algebra.