(** %\subsection*{ support :  mult\_by\_scalars.v }%*)
Set Implicit Arguments.

(** - mult_by_scalars is just an abbreviation for the special case of pointwise, where
 the operation is scalar multiplication. *)

(* That is to say: it takes two sequences of length N: one sequence v1...vN of *)
(* vectors and one sequence a1...aN of scalars. It returns the sequence of each vector *)
(* multiplied by its respective scalar; ie. a1*v1...aN*vN *)

Require Export pointwise.
Require Export modify_seq.
Require Export vecspaces_verybasic.

(** %\label{multbyscalars}% *)
Definition mult_by_scalars: (R:ring; V:(module R); N:Nat; a:(Map (fin N) R); v:(Map (fin N) V))(MAP (fin N) V)
:= [R,V,N,a,v](pointwise (uncurry (MODULE_comp 2!V)) a v).

Lemma mult_by_scalars_comp : 
  (R:ring; V:(module R);N:Nat; a,b:(MAP (fin N) R); v,w:(MAP (fin N) V)) 
    a='b -> v='w -> 
      (mult_by_scalars a v)='(mult_by_scalars b w).
Intros.
Unfold mult_by_scalars.
(Apply (!pointwise_comp_general (fin N) R V V);Auto with algebra).
Qed.

Lemma mult_by_scalars_fun2_compatible : (R:ring; V:(module R); N:Nat)
  (fun2_compatible (mult_by_scalars 2!V 3!N)::((MAP ??)->(MAP ??)->(MAP ??))).
Exact mult_by_scalars_comp.
Qed.

Hints Resolve mult_by_scalars_fun2_compatible mult_by_scalars_comp : algebra.

Lemma mult_by_scalars_Seqtl : 
  (R:ring; V:(module R); N:Nat; a:(Map (fin N) R); v:(Map (fin N) V))
    (mult_by_scalars (Seqtl a) (Seqtl v))='(Seqtl (mult_by_scalars a v)).
Intros.
Unfold mult_by_scalars.
(Apply Sym;Auto with algebra).
Qed.

Hints Resolve mult_by_scalars_Seqtl : algebra.

Lemma mult_by_scalars_concat : (R:ring; V:(module R); N,M:Nat; a:(Map (fin N) R); b:(Map (fin M) R); v:(Map (fin N) V); w:(Map (fin M) V)) 
  (mult_by_scalars a++b v++w)='(mult_by_scalars a v)++(mult_by_scalars b w).
Intros.
Unfold mult_by_scalars.
Auto with algebra.
Qed.

Hints Resolve mult_by_scalars_concat : algebra.

Lemma mult_by_scalars_modify_seq :
  (F:field;V:(vectorspace F);n:Nat;p:(seq n F);k:(seq n V);i:(fin n);q:F)
    (mult_by_scalars (modify_seq p i q) k)
    =' (modify_seq (mult_by_scalars p k) i q mX(k i)) in (seq??).
Induction n.
Intros;Inversion i;Inversion in_range_prf.
Intros.
Case i.
Intro;Case index.
Intros.
(Apply Trans with (mult_by_scalars q;;(Seqtl p) k);Auto with algebra).
Apply Trans with (mult_by_scalars q;;(Seqtl p) (head k);;(Seqtl k)).
Unfold mult_by_scalars.
(Apply toMap;Apply pointwise_comp;Auto with algebra).
Apply Trans with (q mX (head k));;(mult_by_scalars (Seqtl p) (Seqtl k)).
Unfold mult_by_scalars.
(Apply Trans with (uncurry (MODULE_comp 2!V) (couple q (head k)));;(pointwise (uncurry (MODULE_comp 1!F 2!V)) (Seqtl p) (Seqtl k));Auto with algebra).
Apply Trans with (q mX (head k));;(Seqtl (mult_by_scalars p k)).
(Apply cons_comp;Auto with algebra).
Unfold mult_by_scalars.
(Apply Trans with (q mX (k (Build_finiteT in_range_prf)));;(Seqtl (mult_by_scalars p k));Auto with algebra).
Apply cons_comp;Auto with algebra.


Intros m Hm.
LetTac Hm':=(lt_S_n??Hm).
(Apply Trans with (hdtl (mult_by_scalars (modify_seq p (Build_finiteT Hm) q) k));Auto with algebra).
(Apply Trans with (hdtl(modify_seq (mult_by_scalars p k) (Build_finiteT Hm)
          (q mX (k (Build_finiteT Hm)))));Auto with algebra).
Unfold hdtl.
(Apply Trans with (head (mult_by_scalars p k));;(Seqtl (modify_seq (mult_by_scalars p k) (Build_finiteT Hm) (q mX (k (Build_finiteT Hm)))));Auto with algebra).
Apply Trans with  (head (mult_by_scalars (modify_seq p (Build_finiteT Hm) q) k));;(mult_by_scalars (Seqtl  (modify_seq p (Build_finiteT Hm) q)) (Seqtl k)).
Auto with algebra.
Apply Trans with (head (mult_by_scalars (modify_seq p (Build_finiteT Hm) q) k));;(mult_by_scalars (modify_seq (Seqtl p) (Build_finiteT Hm') q) (Seqtl k)).
(Apply cons_comp;Auto with algebra).
(Apply cons_comp;Auto with algebra).
(Apply Trans with (mult_by_scalars (Seqtl (modify_seq p (Build_finiteT Hm) q)) (Seqtl k));Auto with algebra).
(Apply Trans with (modify_seq (Seqtl (mult_by_scalars p k)) (Build_finiteT Hm') (q mX (k (Build_finiteT Hm))));Auto with algebra).
(Apply Trans with (modify_seq (mult_by_scalars (Seqtl p) (Seqtl k)) (Build_finiteT Hm') (q mX (k (Build_finiteT Hm))));Auto with algebra).
Apply Trans with  (mult_by_scalars (modify_seq (Seqtl p) (Build_finiteT Hm') q) (Seqtl k)).
(Apply toMap;Apply mult_by_scalars_comp;Auto with algebra).
(Apply Trans with (modify_seq (mult_by_scalars (Seqtl p) (Seqtl k)) (Build_finiteT Hm') (q mX (Seqtl k (Build_finiteT Hm'))));Auto with algebra).
Qed.

Hints Resolve mult_by_scalars_modify_seq : algebra.