(** %\subsection*{ support :  seq\_equality.v }%*)
Set Implicit Arguments.
Require Export cast_seq_lengths.

(** - We cannot compare v++w and w++v using =' since they have non-convertible
 lengths (n+k $v.$ k+n) and hence are judged to stem from different setoids. 
 We have two complementing ways of dealing with sequences of equal 
 but non-convertible lengths: one is using casting functions (see cast_seq_lengths.v),
 the other is defining a different equality predicate for sequences: seq_equal.
 Two sequences v:(seq n A) and w:(seq k A) are seq_equal if every i:nat 
 is either out of both sequences' bounds (ie. $i\geq n$ and $i\geq k$), or there 
 exist proofs that we can use to turn i into a (fin n) and (fin k), so 
 that "v(i)=w(i)"

 %\label{seqequal}% *)

Definition seq_equal [A:Setoid;n,m:Nat;v:(seq n A);w:(seq m A)] := 
(i:Nat)
  (EXT p:(lt i n) | (EXT q:(lt i m) |
     (v (Build_finiteT p))='(w (Build_finiteT q))))
\/ ((le n i)/\(le m i)).


(** - Of course seq_equal holds for ='-equal sequences *)
Lemma Map_eq_seq_equal : (A:Setoid;n:Nat;v,w:(seq n A)) v='w->(seq_equal v w).
Intros.
Red.
Intro.
Generalize (le_or_lt n i).
Intro p;Inversion_clear p.
Right;Split;Auto.
Left.
Repeat Exists H0.
Simpl in H;Red in H;Simpl in H;Apply H.
Qed.

(** - And the other way around, if v and w happen to have the same type *)

Lemma seq_equal_map_equal : (A:Setoid;n:Nat;v,w:(seq n A)) (seq_equal v w)->v='w.
Intros.
Simpl.
Red.
Intro.
Red in H.
NewDestruct x.
Rename index into i.
Generalize (H i);Clear H;Intro.
Inversion_clear H.
Inversion_clear H0.
Inversion_clear H.
Apply Trans with (v (Build_finiteT x)).
(Apply Ap_comp;Auto with algebra);Simpl;Auto.
(Apply Trans with (w (Build_finiteT x0));Auto with algebra).
(Apply Ap_comp;Auto with algebra);Simpl;Auto.
Inversion_clear H0;(Apply False_ind;Auto with algebra).
(Apply (le_not_lt n i);Auto with algebra).
Qed.

Hints Resolve seq_equal_map_equal : algebra.



(* Of course it's an equivalence relation: refl, symm, trans *)
Lemma seq_equal_refl : (A:Setoid;n:Nat;v:(seq n A)) (seq_equal v v).
Intros.
(Apply Map_eq_seq_equal;Auto with algebra).
Qed.

Hints Resolve seq_equal_refl : algebra.


Lemma seq_equal_symm : (A:Setoid;n,m:Nat;v:(seq n A);w:(seq m A)) (seq_equal v w)->(seq_equal w v).
Intros.
Red;Red in H;Intro;Generalize (H i);Clear H;Intro.
Inversion_clear H.
Left.
Inversion_clear H0.
Inversion_clear H.
Exists x0.
Exists x.
(Apply Sym;Auto with algebra).
Right.
Inversion_clear H0;Split;Trivial.
Qed.

Hints Immediate seq_equal_symm : algebra.


Lemma seq_equal_trans : (A:Setoid;n,m,l:Nat;v:(seq n A);w:(seq m A);u:(seq l A)) (seq_equal v w)->(seq_equal w u)->(seq_equal v u).
Intros.
Red in H H0.
Red;Intro.
Generalize (H i) (H0 i);Clear H H0;Intros.
Inversion_clear H;Inversion_clear H0.
Left.
Inversion_clear H1;Inversion_clear H.
Exists x.
Inversion_clear H0;Inversion_clear H1.
Exists x2.
(Apply Trans with  (w (Build_finiteT x1));Auto with algebra).
(Apply Trans with (w (Build_finiteT x0));Auto with algebra).
Inversion_clear H1;Inversion_clear H.
Inversion_clear H0.
(Apply False_ind;Auto with algebra).
Generalize (lt_not_le i m);Intro p;Red in p.
Auto.
Inversion_clear H1;Inversion_clear H.
(Apply False_ind;Auto with algebra).
Generalize (lt_not_le i m);Intro p;Red in p.
Auto.
Right.
Inversion_clear H;Inversion_clear H1;Split;Auto.
Qed.

Hints Resolve seq_equal_trans : algebra.




(* Finally, the interplay with casting functions: *)
Lemma cast_seq_preserves_seq_equal: (A:Setoid;n,m:Nat;v:(seq n A);H:n='m) (seq_equal v (cast_seq v H)).
Red;Intros.
Generalize (le_or_lt n i).
Intro p;Inversion_clear p.
Right.
Split;Try Trivial.
Rewrite <- H.
Trivial.
Left.
Exists H0.
Exists (lt_comp H0 H).
Apply Trans with (cast_seq v H (cast_fin (Build_finiteT H0) H)).
(Apply cast_seq_cast_fin;Auto with algebra).
Unfold cast_fin.
Auto with algebra.
Qed.

Hints Resolve cast_seq_preserves_seq_equal : algebra.
