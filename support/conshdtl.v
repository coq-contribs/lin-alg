(** %\subsection*{ support :  conshdtl.v }%*)
Set Implicit Arguments.
Require Export finite.
Require Export Parts.

(** - This file introduces the "cons" operator on sequences (called "conseq" here to
 avoid confusion with the normal notion for Lists). It is denoted as "a;;v" instead
 of "a::v" since the latter is already taken in coq.
 - Also it defines "Seqtl" (the "tail" operator) and "head". *)

Section MAIN.

(* conseq adjoins an element x of X to finite functions f:(fin N)->X *)
(* This is done by {0->x; m+1->f(m)} : (fin N+1)->X, ie. the new element *)
(* is inserted at the front. That's why it's called conseq: it's the seq *)
(* variant of the cons operator as seen in lists *)

(** %\label{conseq}% *)

Definition conseq : (A:Setoid; n:Nat; a:A; v:(seq n A))(seq (S n) A).
Intros.
Apply (Build_Map 3!([m:(fin (S n))]
      <[_:(fin (S n))](A::Type)>
        Cases m of
          (Build_finiteT x0 x1) => 
           (<[x2:Nat](lt x2 (S n))->(A::Type)>
              Cases x0 of
                O => [_:(lt O (S n))]a
              | (S m') => 
                 [HSm':(lt (S m') (S n))]
                  (Ap v (Build_finiteT (lt_S_n m' n HSm')))
              end x1)
        end)).
Red.
Simpl.
Intros x0 y.
Case x0.
Case y.
Simpl.
Intros x2 y1.
NewInduction x2.
Intros x2 y2.
NewInduction x2.
Intro;Apply Refl.
Intro H.
Inversion H.
Clear IHx2.
Induction index.
Intros h H.
Inversion H.
Intros. 
Clear H.
(Apply Ap_comp;Auto with algebra).
Defined.

Notation "a ;; b" := (conseq a b) (at level 4, right associativity)
  V8only (at level 60, right associativity).

Variable A:Setoid;n:Nat;a:A.

Lemma cons_comp :  (a':A; v,v':(seq n A)) 
  a =' a' -> v =' v'  -> a ;; v =' a' ;; v'.
Intros.
Simpl.
Red.
Intro i'.
Elim i'.
Intro i.
Simpl.
Case i.
Auto.
Intros.
(Apply Ap_comp;Auto with algebra).
Qed.

Hints Resolve cons_comp : algebra.

Lemma cons_first_element : (v:(seq n A);H:(lt O (S n))) 
  (a;;v (Build_finiteT H))=' a.
Auto with algebra.
Qed.

(** %\label{head}% *)
Definition head [A:Setoid;n:Nat;v:(seq (S n) A)] := (v (Build_finiteT (lt_O_Sn n))).

Lemma head_comp : (A:Setoid;n:Nat;v,v':(seq (S n) A)) 
  v =' v' -> (head v)='(head v').
Unfold head.
Auto with algebra.
Qed.

Hints Resolve head_comp cons_first_element : algebra.

(** - these two lemmas are mainly useful for the algebra Hints database 
 (hence the names) *)
Lemma head_unfolding1 : (v:(seq (S n) A)) 
  (v (Build_finiteT (lt_O_Sn n)))='a -> (head v)='a.
Auto with algebra.
Qed.

Lemma head_unfolding2 : (v:(seq (S n) A)) 
  a='(v (Build_finiteT (lt_O_Sn n))) -> a=' (head v).
Auto with algebra.
Qed.

Hints Resolve head_unfolding1 head_unfolding2 : algebra.
Hint head_unfolding1 : algebra := Extern 0 (head ?)='? Unfold head.
Hint head_unfolding2 : algebra := Extern 0 ?='(head ?) Unfold head.

Lemma head_cons_inv : (v:(seq n A)) (head a;;v)='a.
Auto with algebra.
Qed.

Hints Resolve head_cons_inv : algebra.

Lemma seq_S_O_contains_single_elt : (A:Setoid;v:(seq (S O) A);i:(fin (S O))) 
  (v i)='(head v).
Intros.
Unfold head.
(Apply Ap_comp;Auto with algebra).
Qed.

Hints Resolve seq_S_O_contains_single_elt : algebra.

Lemma seq_S_O_head_fixes_everything : (A:Setoid;v,v':(seq (S O) A)) 
  (head v)='(head v')->v='v'.
Intros.
Simpl.
Red.
Intro.
Apply Trans with (head v).
(Apply seq_S_O_contains_single_elt;Auto with algebra).
(Apply Trans with (head v');Auto with algebra).
Qed.

Hints Resolve seq_S_O_head_fixes_everything : algebra.

Lemma cons_later_elements : (v:(seq n A); i:Nat; Hi:(lt (S i) (S n)); Hi':(lt i n))
  (a;;v (Build_finiteT Hi)) =' (v (Build_finiteT Hi')).
Intros.
Simpl.
(Apply Ap_comp;Auto with algebra).
Qed.

Hints Resolve cons_later_elements : algebra.

(* Taking the "tl" of a sequence *)
(** %\label{Seqtl}% *)
Definition Seqtl : (n:Nat)(seq n A)->(seq (pred n) A). 
Clear n.
Intro n.
Case n.
Intro f.
Exact f.
Intros m f.
Apply (Build_Map 3!([i':(fin m)](Cases i' of (Build_finiteT i Hi) => (f (Build_finiteT (lt_n_S ?? (Hi::(lt i m)))))end))).
Red.
Intros x y.
Case x.
Case y.
Simpl.
Intros.
(Apply Ap_comp;Auto with algebra).
Defined.

Lemma Seqtl_comp: (v,v':(seq n A)) 
  v='v'->(Seqtl v)='(Seqtl v').
NewInduction n.
Intros.
Simpl.
Auto.
Intros.
Simpl.
Red.
Simpl.
Intro.
Elim x.
Intros.
(Apply Ap_comp;Auto with algebra).
Qed.

Hints Resolve Seqtl_comp : algebra.

(** - "hdtl" is a 'tool' for writing a sequence as the cons of its head and its tail
 %\label{hdtl}% *)

Definition hdtl [v:(seq (S n) A)]:=((head v);; (Seqtl v)::(seq (S n) A)).

Lemma conseq_hdtl : (v:(seq (S n) A);H:(lt O (S n)))
  v =' (v (Build_finiteT H));;(Seqtl v).
(* note we don't say v='(head v);;(Seqtl v): we want freedom in the choice of the proof H *)
Intros.
Simpl.
Red.
Simpl.
Intro x.
Case x.
Intro.
Case index.
Intros;Apply Ap_comp;Simpl;Auto with algebra arith.
Red;Auto with algebra.
Intros;Apply Ap_comp;Simpl;Auto with algebra arith.
Red;Auto with algebra.
Qed.

Hints Resolve conseq_hdtl : algebra.

Lemma hdtl_x_is_x : (v:(seq (S n) A)) v =' (hdtl v).
Unfold hdtl.
Intros.
Unfold head.
Apply conseq_hdtl.
Qed.

Hints Resolve hdtl_x_is_x : algebra.
Hint headconsseqtl1 : algebra := Extern 0 (head ?);;(Seqtl ?)='? Fold hdtl;Apply Sym;Apply hdtl_x_is_x.
Hint headconsseqtl2 : algebra := Extern 0 ?='(head ?);;(Seqtl ?) Fold hdtl;Apply hdtl_x_is_x.

Lemma cons_lemma_nice: (P:(Predicate (seq (S n) A))) 
  ((a:A;v:(seq n A))(Pred_fun P a;;v))
    -> ((w:(seq (S n) A))(Pred_fun P w)).
Intro.
Elim P.
Intros.
Unfold pred_compatible in Pred_compatible_prf.
(Apply Pred_compatible_prf with (hdtl w);Auto with algebra).
Unfold hdtl.
Apply H.
Qed.

Lemma cons_lemma_verynice: 
  (P:(Predicate (seq (S n) A));H:(lt O (S n));w:(seq (S n) A)) 
    (Pred_fun P (w (Build_finiteT H));;(Seqtl w))
      -> (Pred_fun P w).
Intros P H w. 
Elim P.
Intros.
Unfold pred_compatible in Pred_compatible_prf.
(Apply Pred_compatible_prf with (w (Build_finiteT H));;(Seqtl w);Auto with algebra).
Qed.

Lemma Seqtl_cons_inv : (v:(seq n A)) (Seqtl a;;v)='v.
Intros.
Simpl.
Red.
Simpl.
Intro i.
Elim i.
Intros.
(Apply Ap_comp;Auto with algebra).
Qed.

Hints Resolve Seqtl_cons_inv : algebra.

Lemma Seqtl_to_seq : (v:(seq (S n) A); i:Nat; Hi:(lt i n);HSi:(lt (S i) (S n)))
  ((Seqtl v) (Build_finiteT Hi))=' (v (Build_finiteT HSi)).
Intros.
Simpl.
(Apply Ap_comp;Auto with algebra).
Qed.

Hints Resolve Seqtl_to_seq : algebra.

Lemma split_hd_tl_equality : (v,w:(seq (S n) A))
  (head v)='(head w) -> (Seqtl v)='(Seqtl w) -> v='w.
Intros.
Intro.
NewDestruct x.
NewDestruct index.
(Apply Trans with (head v);Auto with algebra).
(Apply Trans with (head w);Auto with algebra).
(Apply Trans with (Seqtl v (Build_finiteT (lt_S_n ?? in_range_prf)));Auto with algebra).
(Apply Trans with (Seqtl w (Build_finiteT (lt_S_n ?? in_range_prf)));Auto with algebra).
Qed.

Hints Resolve split_hd_tl_equality : algebra.
End MAIN.

(* Hints and notation inside sections is forgotten... *)
Notation "a ;; b" := (conseq a b) (at level 4, right associativity)
  V8only (at level 60, right associativity).

Hints Resolve cons_comp : algebra.
Hints Resolve head_comp cons_first_element : algebra.
Hints Resolve head_unfolding1 head_unfolding2 : algebra.
Hint head_unfolding1 : algebra := Extern 0 (head ?)='? Unfold head.
Hint head_unfolding2 : algebra := Extern 0 ?='(head ?) Unfold head.
Hints Resolve head_cons_inv : algebra.
Hints Resolve cons_later_elements : algebra.
Hints Resolve Seqtl_comp : algebra.
Hints Resolve conseq_hdtl : algebra.
Hints Resolve hdtl_x_is_x : algebra.
Hint headconsseqtl1 : algebra := Extern 0 (head ?);;(Seqtl ?)='? Fold hdtl;Apply Sym;Apply hdtl_x_is_x.
Hint headconsseqtl2 : algebra := Extern 0 ?='(head ?);;(Seqtl ?) Fold hdtl;Apply hdtl_x_is_x.
Hints Resolve Seqtl_cons_inv : algebra.
Hints Resolve Seqtl_to_seq : algebra.
Hints Resolve split_hd_tl_equality : algebra.
Hints Resolve seq_S_O_contains_single_elt : algebra.
Hints Resolve seq_S_O_head_fixes_everything : algebra.
