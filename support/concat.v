(** %\subsection*{ support :  concat.v }%*)
(** - concatenation of sequences, denoted by "++" (Haskell notation) plus some
 preliminary lemmas *)
Set Implicit Arguments.
Require Export conshdtl.

Section MAIN.
Variable A:Setoid.

(** %\label{concat}% *)
Definition concat : (n,m:Nat; f:(seq n A); g:(seq m A))(seq (plus n m) A).
Induction n.
Simpl.
Intros.
Exact g.
Intros.
Simpl.
Exact (f (Build_finiteT (lt_O_Sn n0)));; (X ? (Seqtl f) g).
(* ie. (concat (f0 :: (Seqtl f) g)) = f0 :: (concat (Seqtl f) g) *)
Defined.

Notation "a ++ b" := (concat a b) (at level 1, no associativity)
  V8only (at level 45, right associativity).

Lemma concat_comp : (n,m:Nat; f,f':(seq n A); g,g':(seq m A))
  f='f' -> g='g' -> f++g='f'++g'.
Induction n.
Intros.
Simpl.
Assumption.
(* the induction step *)
Intros.
LetTac fg:=f++g in Goal.
LetTac fg':=(f'++g') in Goal.
Simpl.
Red.
NewDestruct x.
NewDestruct index.
Unfold fg.
Unfold fg'.
Simpl.
Auto with algebra.
(**)
(Apply Trans with ((Seqtl f)++g (Build_finiteT (lt_S_n ?? in_range_prf)));Auto with algebra).
(Apply Trans with ((Seqtl f')++g' (Build_finiteT (lt_S_n ?? in_range_prf)));Auto with algebra).
(Apply Ap_comp;Auto with algebra).
(Apply (H ? (Seqtl f) (Seqtl f') g g');Auto with algebra).
Change (Seqtl f)=' (Seqtl f').
(Apply Seqtl_comp;Auto with algebra).
Qed.

Hints Resolve concat_comp : algebra.

Variable n,m:Nat.

Lemma cons_concat : (a,a':A; v,v':(seq n A); w,w':(seq m A)) 
  a='a' -> v='v' -> w='w'
    -> a;;(v++w) =' (a';;v')++w'.
Intros.
Apply Trans with (a;;v)++w.
Intro i.
NewDestruct i.
NewDestruct index.
Simpl.
Auto with algebra.
Rename in_range_prf into p.
(Apply Trans with (v++w (Build_finiteT (lt_S_n ?? p)));Auto with algebra).
(Apply Trans with ((Seqtl a;;v)++w (Build_finiteT (lt_S_n ?? p)));Auto with algebra).
Change (a;;v)++w='(a';;v')++w' in (seq (plus (S n) m) A).
Apply concat_comp;Auto with algebra.
Qed.

Hints Resolve cons_concat : algebra.

Lemma concat_cons : (a,a':A; v,v':(seq n A); w,w':(seq m A)) 
  a='a' -> v='v' -> w='w'
    -> (a';;v')++w'='a;;(v++w).
Intros;Apply Sym;Apply cons_concat;Auto with algebra.
Qed.

Hints Resolve concat_cons : algebra.

Lemma cons_concat_special : (a:A; v:(seq n A); v':(seq m A))
  a;;(v++v') =' (a;;v)++v'. 
Intros.
Intro i.
NewDestruct i.
NewDestruct index.
Simpl.
Auto with algebra.
Rename in_range_prf into p.
(Apply Trans with (v++v' (Build_finiteT (lt_S_n ?? p)));Auto with algebra).
(Apply Trans with ((Seqtl a;;v)++v' (Build_finiteT (lt_S_n ?? p)));Auto with algebra).
Qed.


Lemma concat_first_element: 
  (v:(seq (S n) A); w:(seq m A); Hnm:(lt O (S (plus n m)));Hn:(lt O (S n))) 
    (v++w (Build_finiteT Hnm))='(v (Build_finiteT Hn)).
Intros.
(Apply Trans with (head v);Auto with algebra).
Qed.

Lemma head_eats_concat : (v:(seq (S n) A); w:(seq m A)) 
  (head v++w)='(head v).
Intros.
Unfold head;Auto with algebra.
Qed.

Lemma Seqtl_concat : (v:(seq (S n) A); w:(seq m A))
  (Seqtl (v++w))=' (Seqtl v)++w.
Intros.
(Apply Trans with (Seqtl (hdtl v)++w);Auto with algebra).
(Apply Trans with (Seqtl (head v);;((Seqtl v)++w));Auto with algebra).
Unfold hdtl.
(Apply Seqtl_comp;Auto with algebra).
Change (Seqtl (head v);;((Seqtl v)++w))='(Seqtl v)++w in (seq (plus n m) A).
Generalize Dependent (Seqtl_cons_inv (head v) (Seqtl v)++w).
Auto.
Qed.

Lemma concat_Seqtl : (v:(seq (S n) A); w:(seq m A))
  (Seqtl v)++w =' (Seqtl (v++w)).
Intros.
Apply Sym.
Apply Seqtl_concat.
Qed.

End MAIN.

Notation "a ++ b" := (concat a b) (at level 1, no associativity)
  V8only (at level 45, right associativity).
Hints Resolve concat_comp : algebra.
Hints Resolve cons_concat concat_cons : algebra.
Hints Resolve concat_first_element head_eats_concat: algebra.
Hints Resolve Seqtl_concat concat_Seqtl : algebra.
Hints Resolve cons_concat_special : algebra.
