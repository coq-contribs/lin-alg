(** %\subsection*{ support :  concat\_facts.v }%*)
Set Implicit Arguments.
Require Export concat.
Require Export empty.

Section MAIN.
Variable A:Setoid.
Variable n,m:Nat.
Variable v:(seq n A).
Variable w:(seq m A).

(** - More facts about concatenation *)

Lemma concat_first_part : (i:Nat; Hi:(lt i n); Hi':(lt i (plus n m))) 
  (v++w (Build_finiteT Hi'))='(v (Build_finiteT Hi)).
NewInduction n.
Intros.
Inversion Hi.
Intro.
Case i.
Unfold concat.
Unfold nat_rect.
Simpl.
Intros.
(Apply Ap_comp;Auto with algebra).
Intros.
Apply Trans with ((hdtl v)(Build_finiteT Hi)).
Apply Trans with ((concat (hdtl v) w) (Build_finiteT Hi')).
(Apply concat_comp;Auto with algebra).
2:(Apply Ap_comp;Auto with algebra).
Unfold hdtl.
(Apply Trans with ((head v);;((Seqtl v)++w) (Build_finiteT Hi'));Auto with algebra).
(Apply Trans with ((Seqtl v)(Build_finiteT (lt_S_n ?? Hi)));Auto with algebra).
(Apply Trans with ((Seqtl v)++w (Build_finiteT (lt_S_n ?? Hi')));Auto with algebra).
Qed.

Hints Resolve concat_first_part : algebra.

Lemma concat_second_part :(i:Nat; Hi:(lt i m); Hi':(lt (plus n i) (plus n m))) 
  (v++w (Build_finiteT Hi'))='(w (Build_finiteT Hi)).
NewInduction n.
Intros.
Unfold concat.
Unfold nat_rect.
(Apply Ap_comp;Auto with algebra).
Intros.
(Apply Trans with ((hdtl v)++w (Build_finiteT Hi'));Auto with algebra).
Unfold hdtl.
(Apply Trans with ((head v);;((Seqtl v)++w)(Build_finiteT Hi'));Auto with algebra).
Cut (lt (S (plus c i)) (S (plus c m))).
Intro.
(Apply Trans with ((Seqtl v)++w (Build_finiteT (lt_S_n ?? H)));Auto with algebra).
(Apply Trans with ((head v);;((Seqtl v)++w) (Build_finiteT H));Auto with algebra).
Replace (S (plus c i)) with (plus (S c) i).
Assumption.
Auto.
Qed.

Hints Resolve concat_second_part : algebra.

Lemma concat_prop_per_part : (P:(Predicate A))
    ((i:Nat;Hi:(lt i n)) (Pred_fun P (v (Build_finiteT Hi))))->
    ((j:nat;Hj:(lt j m)) (Pred_fun P (w (Build_finiteT Hj))))
->
    (k:nat;Hk:(lt k (plus n m))) (Pred_fun P (v++w (Build_finiteT Hk))).
NewInduction n.
Intros.
Unfold concat;Unfold nat_rect.
Apply H0.
Intros.
Generalize Hk;Clear Hk;Case k;[Intro Hk | Intros k0 Hk0].
Generalize (lt_O_Sn c);Intro Hk'.
(Apply (Pred_compatible_prf 2!P) with (v (Build_finiteT Hk'));Auto with algebra).
Simpl.
Apply Ap_comp;Auto with algebra.
Generalize (lt_S_n ?? Hk0);Intro Hk0'.
Fold (plus c m) in Hk0'.
Apply (Pred_compatible_prf 2!P) with ((Seqtl v)++w (Build_finiteT Hk0')).
(Apply IHc;Auto with algebra).
Clear Hk0' Hk0 k0 k.
Intros.
(Apply (Pred_compatible_prf 2!P) with (v (Build_finiteT (lt_n_S ?? Hi)));Auto with algebra).

Apply Trans with ((Seqtl v++w) (Build_finiteT Hk0')).
Apply Sym.
Generalize Seqtl_to_seq.
Intros.
Apply (H1 ??v++w?Hk0' Hk0).
Generalize Seqtl_concat.
Intro p.
(Apply Ap_comp;Auto with algebra).
Qed.

Lemma concat_prop_per_element : (P:(Predicate A))
  ((i:Nat;Hi:(lt i n);Hi':(lt i (plus n m)))
        (Pred_fun P (v++w (Build_finiteT Hi'))))
  -> ((j:Nat;Hj:(lt j m);Hj':(lt (plus n j) (plus n m)))
         (Pred_fun P (v++w (Build_finiteT Hj'))))
->
  (k:Nat;Hk:(lt k (plus n m))) (Pred_fun P (v++w (Build_finiteT Hk))).
Intros.
Apply concat_prop_per_part.
Intros.
Generalize (H i Hi); Intro.
Apply (Pred_compatible_prf 2!P) with (v++w (Build_finiteT (lt_plus_trans ?? m Hi))).
Apply H1.
Apply Sym.
Apply concat_first_part.
Intros.
Cut (lt (plus n j) (plus n m)).
Intro Hj'.
(Apply (Pred_compatible_prf 2!P) with (v++w (Build_finiteT Hj'));Auto with algebra).
Auto with arith.
Qed.

Lemma split_to_concat : (vw:(seq (plus n m) A))(sigT (seq n A) [a](sigT (seq m A) [b]vw='a++b)).
Clear v w.
NewInduction n.
Intros.
Exists (empty_seq A).
Simpl in vw.
Exists vw.
Simpl.
Red.
Auto with algebra.

Clear n;Intros.
Generalize (IHc (Seqtl vw)).
Intros.
Inversion_clear X.
Exists (head vw);;x.
Inversion_clear X0.
Exists x0.
(Apply Trans with (hdtl vw);Auto with algebra).
Change vw =' (hdtl vw) in (seq (S (plus c m)) A).
Apply hdtl_x_is_x.
Unfold hdtl.
(Apply Trans with (head vw);;(x++x0);Auto with algebra).
Change  ((head vw);;(Seqtl vw)) =' ((head vw);;((x++x0)::(seq (plus c m) A))).
(Apply cons_comp;Auto with algebra).
Apply cons_concat_special with a:=(head vw) v:=x v':=x0.
Qed.
End MAIN.

Hints Resolve concat_first_part : algebra.
Hints Resolve concat_second_part : algebra.
