(** %\subsection*{ support :  omit.v }%*)
(** - (omit v i) = $\langle v_0...v_{i-1},v_{i+1}...v_{n-1}\rangle$ *)
Set Implicit Arguments.
Require Export empty.
Require Export conshdtl.

(** %\label{omit}% *)
Definition omit: (A:Setoid;n:Nat)(seq n A)->(fin n)->(seq (pred n) A).
NewDestruct n.
Auto.
Induction n.
Intros.
Apply (empty_seq A).
Intros.
Case X0.
Intro x;Case x.
Intro.
Exact (Seqtl X).
Intros.
Exact ((head X);;(Hrecn (Seqtl X) (Build_finiteT (lt_S_n ?? in_range_prf)))).
Defined.

Lemma omit_comp : (A:Setoid;n:Nat) (v,v':(seq n A);i,i':(fin n)) 
  v='v' -> i='i' -> (omit v i)='(omit v' i').
NewDestruct n.
Intros.
Auto with algebra.
Induction n.
Intros.
Unfold omit.
Unfold nat_rect.
Auto with algebra.
Intros v v' i.
Case i.
Intros x l i'.
Case i'.
Intros.
Apply Trans with (omit v' (Build_finiteT l)).
Unfold omit.
Unfold nat_rect.
Generalize l H0;Clear H0 l.
NewDestruct x.
Intros.
Change (Seqtl v) =' (Seqtl v'). 
(Apply Seqtl_comp;Auto with algebra).
Intros.
Simpl.
(Apply cons_comp;Auto with algebra).
Unfold omit in Hrecn.
Unfold nat_rect in Hrecn.
Apply Hrecn.
Change (Seqtl v) =' (Seqtl v').
(Apply Seqtl_comp;Auto with algebra).
Auto with algebra.
Unfold omit.
Unfold nat_rect.
Generalize l H0;Clear H0 l.
NewDestruct x.
NewDestruct index.
Intros;Auto with algebra.
Intros.
Simpl in H0.
Inversion H0.
Intros.
Generalize l H0;Clear H0 l.
NewDestruct index.
Intros.
Simpl in H0.
Inversion H0.
Intros.
Simpl.
(Apply cons_comp;Auto with algebra).
Unfold omit in Hrecn.
Unfold nat_rect in Hrecn.
(Apply Hrecn;Auto with algebra).
Qed.

Hints Resolve omit_comp : algebra.


(** - The following are actually definitions. omit_removes does the following: 
 suppose v:(seq n A) and i:(fin n). Define w:=(omit v i). Then given j, (w j)
 = (v j') for some j'. Omit_removes returns this j' and a proof of this fact
 (packed together in a sigma-type). *)

Lemma omit_removes : (n:Nat;A:Setoid;v:(seq n A);i:(fin n);j:(fin (pred n)))
  (sigT (fin n) [i'](v i')='((omit v i) j)).
NewDestruct n.
Intros.
(Apply False_rect;Auto with algebra).

Intros.
Generalize (j::(fin n)).
Clear j.
Intro j.

Induction n.
Apply False_rect.
(Apply fin_O_nonexistent;Auto with algebra).

Case i.
Intro x;Case x.
Intros.
LetTac l:=in_range_prf.
Case j.
Intros.
LetTac l0:=in_range_prf0.
Apply (existT ? [i':(fin (S (S n)))] ((Ap v i') =' ((omit v (Build_finiteT l)) (Build_finiteT l0))) (Build_finiteT (lt_n_S ?? l0))).
(Apply Trans with ((Seqtl v) (Build_finiteT l0));Auto with algebra).

Intros.
Rename in_range_prf into l.
Case j.
Intro x0; Case x0.
Intro l0.
Apply (existT (fin (S (S n))) [i':(fin (S (S n)))] ((Ap v i') =' (Ap (omit v (Build_finiteT l)) (Build_finiteT l0))) (Build_finiteT (lt_O_Sn (S n)))).
(Apply Trans with (head (omit v (Build_finiteT l)));Auto with algebra).

Intros.
Rename in_range_prf into l0.
Generalize (Hrecn (Seqtl v) (Build_finiteT (lt_S_n ?? l)) (Build_finiteT (lt_S_n ?? l0))).
Intro.
Inversion_clear X.
Generalize H.
Clear H.
Case x1.
Intros.
Apply (existT (fin (S (S n))) [i':(fin (S (S n)))] ((Ap v i') =' (Ap (omit v (Build_finiteT l)) (Build_finiteT l0))) (Build_finiteT (lt_n_S ?? in_range_prf))).
(Apply Trans with ((head v);;(omit (Seqtl v) (Build_finiteT (lt_S_n ?? l))) (Build_finiteT l0));Auto with algebra).
Defined.

(** - omit_removes' on the other hand does this: suppose again v:(seq n A) and i:(fin n)
 and define w:=(omit v i). Suppose that this time j:(fin n). If [~i='j] then (v j)='(w j')
 for some j'; again omit_removes' returns this j' and a proof. *)

Lemma omit_removes' : (n:Nat;A:Setoid;v:(seq n A);i,j:(fin n))
  ~i='j -> (sigT (fin (pred n)) [j'](v j)='((omit v i) j')).
NewDestruct n.
Intros.
(Apply False_rect;Auto with algebra).

Induction n.
Intros.
Absurd i='j.
Auto.
(Apply fin_S_O_unique;Auto with algebra).
Intros A v i.
Elim i.
Intro i';Case i'.
Intros Hi j.
Elim j.
Intro j';Case j'.
Intros.
Simpl in H.
Absurd O=O;Auto.
Intros n0 p0 H.
Exists (Build_finiteT (lt_S_n ?? p0)).
Simpl.
(Apply Ap_comp;Auto with algebra).
Simpl.
Auto.

Intros gat Hg vraag. 
Elim vraag.
Intro vr;Case vr.
Intros Hvr H.
Exists (Build_finiteT (lt_O_Sn n)).
Simpl.
Unfold head.
(Apply Ap_comp;Auto with algebra).
Simpl.
Auto.

Intros vr' Hvr H.
Assert ~(Build_finiteT (lt_S_n ?? Hg))='(Build_finiteT (lt_S_n ?? Hvr))in(fin?).
Simpl;Simpl in H;Auto.
LetTac aw:=(!Hrecn ? (Seqtl v) ?? H0).
Case aw.
Intro x;Elim x.
Intros.
Exists (Build_finiteT (lt_n_S??in_range_prf)).
Apply Trans with (Seqtl v (Build_finiteT (lt_S_n vr' (S n) Hvr))).
Apply Sym.
(Apply Seqtl_to_seq;Auto with algebra).
(Apply Trans with (omit (Seqtl v) (Build_finiteT (lt_S_n gat (S n) Hg)) (Build_finiteT in_range_prf));Auto with algebra).
Defined.
