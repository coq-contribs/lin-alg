(** %\subsection*{ extras :  restrict.v }%*)
Set Implicit Arguments.
Require Export const.
Require Export pointwise.
Require Export distinct.

(** - Restriction of a sequence to its prefixes... not used anywhere any more *)

Definition restricted_seq : (S:Setoid;N:Nat;f:(seq N S);M:Nat;leMN:(le M N))(seq M S).
Intros.
Simpl.
Apply (Build_Map 3![mM:(fin M)](f (Cases mM of (Build_finiteT m ltmM) =>
  (Build_finiteT (lt_le_trans ??? ltmM leMN)) end))).
Red.
Intros.
NewDestruct x.
NewDestruct y.
(Apply Ap_comp;Auto with algebra).
Defined.

Lemma restricted_comp : (S:Setoid;N:Nat;f,f':(seq N S);M:Nat;leMN,leMN':(le M N)) f='f'->(restricted_seq f leMN)='(restricted_seq f' leMN').
Intros.
Simpl.
Red.
Simpl.
NewDestruct x.
(Apply Ap_comp;Auto with algebra).
Qed.

Hints Resolve restricted_comp : algebra.

Lemma const_map_restricted : (n,N:Nat; H:(le n N); Y:Setoid; y:Y) (restricted_seq (const_seq N y) H)=' (const_seq n y).
Intros.
Simpl.
Red.
Intro i.
Unfold restricted_seq.
Unfold const_map.
Simpl.
Apply Refl.
Qed.

Hints Resolve const_map_restricted : algebra.

Lemma restricted_seq_preserves_distinct : (A:Setoid;n,m:Nat;v:(seq n A);H:(le m n)) (distinct v)->(distinct (restricted_seq v H)).
Unfold distinct.
Simpl.
Intros.
NewDestruct i;NewDestruct j.
Apply (H0(Build_finiteT (lt_le_trans index m n in_range_prf H))(Build_finiteT (lt_le_trans index0 m n in_range_prf0 H))).
Simpl;Simpl in H1.
Auto.
Qed.

Hints Resolve restricted_seq_preserves_distinct : algebra.

(* The restricted pointwise-generated sequence equals the pointwise-generated sequence of *)
(* restricted sequences *)

Lemma pointwise_restricted : (n,N:Nat; H:(le n N); B,C,D:Setoid; op:(Map (cart B C) D); f:(seq N B); g:(seq N C)) 
(restricted_seq (pointwise op f g) H) =' (pointwise op (restricted_seq f H) (restricted_seq g H)). 
Intros.
Unfold pointwise.
Unfold restricted_seq.
Simpl.
Red.
Intro i.
Simpl.
Apply Refl.
Qed.

Hints Resolve pointwise_restricted : algebra.