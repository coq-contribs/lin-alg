(** %\subsection*{ support :  pointwise.v }%*)
Set Implicit Arguments.
Require Export concat.
Require Export Cartesian.

(** - The pointwise operation of a binary operator: suppose $f:A\to B, g:A\to C,
 \circ:B\times C\to D$, then (pointwise $\circ$ f g) = $a\mapsto f(a)\circ g(a): A\to D$.
 This is used almost solely to define linear combinations: we have a sequence $\vec a$
 of scalars and a sequence $\vec v$ of vectors, then (sum (pointwise (mX) a v)) = 
 $\sum_{i=0}^{n-1} a_i v_i$.

 %\label{pointwise}% *)

Definition pointwise : (A,B,C,D:Setoid; op:(Map (cart B C) D); f:(Map A B); g:(Map A C))(MAP A D).
Intros.
Apply (Build_Map 3!([a:A](op (couple (f a) (g a))))).
Red.
Intros.
(Apply Ap_comp;Auto with algebra).
Defined.

Lemma pointwise_comp_general :
  (A,B,C,D:Setoid;op,op':(Map (cart B C) D); f,f':(Map A B); g,g':(Map A C))
    op='op' in(MAP??) -> f='f' in(MAP??) -> g='g' in(MAP??)
      -> (pointwise op f g)='(pointwise op' f' g').
Intros.
Intro.
Unfold pointwise.
Simpl.
(Apply Ap_comp;Auto with algebra).
Qed.

Lemma pointwise_comp :
  (n:Nat;B,C,D:Setoid;op,op':(Map (cart B C) D); f,f':(seq n B); g,g':(seq n C))
    op='op' in(MAP??) -> f='f' -> g='g'
      -> (pointwise op f g)='(pointwise op' f' g').
Intros.
Apply (pointwise_comp_general H H0 H1).
Qed.

Hints Resolve pointwise_comp : algebra.

Lemma pointwise_hd: (A,B,C:Setoid; n:Nat; v:(seq (S n) A); w:(seq (S n) B); op:(Map (cart A B) C);H:(lt O (S n)))
  ((pointwise op v w) (Build_finiteT H))
  =' (op (couple (v (Build_finiteT H)) (w (Build_finiteT H)))).
Intros.
Unfold pointwise.
Simpl.
Apply Refl.
Qed.

Hints Resolve pointwise_hd:algebra.

Lemma pointwise_cons:
  (A,B,C:Setoid; a:A; b:B; n:Nat; v:(seq n A); w:(seq n B); op:(Map (cart A B) C))
    (pointwise op a;;v b;;w) =' (op (couple a b));;(pointwise op v w) in (seq??).
Intros.
(Apply split_hd_tl_equality;Auto with algebra).
Qed.

Hints Resolve pointwise_cons:algebra.

Lemma pointwise_hd_tl :
  (A,B,C:Setoid; n:Nat; v:(seq (S n) A); w:(seq (S n) B); op:(Map (cart A B) C))
    (pointwise op v w)
    =' (op (couple (head v) (head w)));;(pointwise op (Seqtl v) (Seqtl w))in(seq??).
Intros.
(Apply split_hd_tl_equality;Auto with algebra).
Unfold pointwise;Intro;Simpl.
NewDestruct x;(Apply Ap_comp;Auto with algebra).
Qed.

Hints Resolve pointwise_hd_tl : algebra.

Lemma pointwise_Seqtl:
  (A,B,C:Setoid; n:Nat; v:(seq n A); w:(seq n B); op:(Map (cart A B) C))
    (pointwise op (Seqtl v) (Seqtl w)) =' (Seqtl (pointwise op v w)) in (seq??).
NewInduction n.
Simpl.
Red.
Auto with algebra.
Intros.
(Apply Trans with (Seqtl (op (couple (head v) (head w)));;(pointwise op (Seqtl v) (Seqtl w)));Auto with algebra).
Qed.

Hints Resolve pointwise_Seqtl:algebra.

Lemma pointwise_concat: (A,B,C:Setoid; n,m:Nat; v:(seq n A); w:(seq m A); x:(seq n B); y:(seq m B); op:(MAP (cart A B) C))
     (pointwise op v++w x++y)='(pointwise op v x)++(pointwise op w y) in(seq??).
NewInduction n.
Intuition.
Intros.
(Apply (split_hd_tl_equality 3!(pointwise op v++w x++y) 4!(pointwise op v x)++(pointwise op w y));Auto with algebra).
(Apply Trans with (pointwise op (Seqtl v++w) (Seqtl x++y));Auto with algebra).
Apply Trans with  (pointwise op (Seqtl v)++w (Seqtl x)++y).
(Apply (!pointwise_comp ???? op op (Seqtl v++w) (Seqtl v)++w (Seqtl x++y) (Seqtl x)++y);Auto with algebra).
(Apply Trans with (Seqtl (pointwise op v x))++(pointwise op w y);Auto with algebra).
(Apply Trans with  (pointwise op (Seqtl v) (Seqtl x))++(pointwise op w y);Auto with algebra).
Apply (IHn ? (Seqtl v) w (Seqtl x) y).
Generalize concat_comp.
Intro p.
Apply (p???(pointwise op (Seqtl v) (Seqtl x))(Seqtl (pointwise op v x))(pointwise op w y)(pointwise op w y));Auto with algebra.
Apply Sym.
Apply (Seqtl_concat (pointwise op v x)(pointwise op w y)).
Qed.

Hints Resolve pointwise_concat:algebra.