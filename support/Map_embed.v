(** %\subsection*{ support :  Map\_embed.v }%*)
Set Implicit Arguments.
Require Export concat.

(** - Any element of $A\subset E$ is of course also an element of $E$ itself.
 Map_embed takes setoid functions $X\to A$ to setoid functions $X\to E$ by embedding

 %\label{Mapembed}% *)
Definition Map_embed : (X,E:Setoid; A:(part_set E); f:(Map X A)) (MAP X E).
Intros.
Apply (Build_Map 3![n:X](A (f n))).
Red.
Intros x y.
Case f.
Intros.
Red in Map_compatible_prf.
Generalize Map_compatible_prf.
Intro H0.
Generalize (H0 x y).
Intros.
Simpl.
Apply H1.
Assumption.
Defined.

Lemma Map_embed_comp : (X,E:Setoid; A:(part_set E); f,g:(Map X A)) 
  f='g in(MAP??) -> (Map_embed f) =' (Map_embed g).
Intros.
Unfold Map_embed;Simpl;Red;Simpl.
Intuition.
Qed.

Hints Resolve Map_embed_comp : algebra.

Lemma Map_embed_cons : (E:Setoid; A:(part_set E); a:A; n:Nat; f:(seq n A)) 
  (Map_embed a;;f) =' (subtype_elt a);;(Map_embed f) in (seq??).
Intros.
Simpl.
Red.
Intro x;Case x;Intro i; Case i.
Simpl.
Auto with algebra.
Intros.
Simpl.
Apply Refl.
Qed.

Hints Resolve Map_embed_cons : algebra.

Lemma cons_Map_embed : (E:Setoid; A:(part_set E); a:A; n:Nat; f:(seq n A))  
  (subtype_elt a);;(Map_embed f) =' (Map_embed a;;f) in (seq??).
Auto with algebra.
Qed.

Hints Resolve cons_Map_embed : algebra.

Lemma Map_embed_Seqtl : (E:Setoid; A:(part_set E); n:Nat; f:(seq n A)) 
  (Map_embed (Seqtl f)) =' (Seqtl (Map_embed f)) in (seq??).
Induction n.
Simpl.
Red.
Auto with algebra.
Intros.
Simpl.
Red.
Simpl.
Intro i.
Case i.
Auto with algebra.
Qed.

Hints Resolve Map_embed_Seqtl : algebra.

Lemma Seqtl_Map_embed : (E:Setoid; A:(part_set E); n:Nat; f:(seq n A))
  (Seqtl (Map_embed f))='(Map_embed (Seqtl f))  in (seq??).
Auto with algebra.
Qed.

Hints Resolve Seqtl_Map_embed : algebra.

Lemma Map_embed_concat : 
  (E:Setoid; A:(part_set E); n,m:Nat; f:(seq n A); g:(seq m A))
    (Map_embed f++g)=' (Map_embed f)++(Map_embed g) in(seq??).
Induction n.
Intros.
Unfold concat.
Unfold nat_rect.
Apply Refl.
Intros.
(* Change =' to Map_eq *)
Change (Map_eq (Map_embed f++g)
     (Map_embed f)++(Map_embed g)).
Red.
Intros.
(Apply Trans with ((hdtl (Map_embed f++g)) x);Auto with algebra).
Case x;Intro i; Case i.
Intro l.
Unfold hdtl.
Unfold head.
Unfold concat.
Unfold nat_rect.
Simpl.
Apply Refl.
Intros.
Unfold hdtl.
Unfold head.
LetTac l:=in_range_prf.
(Apply Trans with ((Seqtl (Map_embed f++g)) (Build_finiteT (lt_S_n ?? l)));Auto with algebra).
Fold (plus n0 m).
Apply Sym.
Apply Trans with ((Seqtl (Map_embed f)++(Map_embed g))(Build_finiteT (lt_S_n ?? l))).
Fold (plus n0 m).
Apply Sym.
(Apply (!Seqtl_to_seq ??(Map_embed f)++(Map_embed g));Auto with algebra).
(Apply Ap_comp;Auto with algebra).
(Apply Trans with (Seqtl (Map_embed f))++(Map_embed g);Auto with algebra).
Apply Trans with (Map_embed (Seqtl f++g)).
2:(Apply (Map_embed_Seqtl (f++g));Auto with algebra).
Apply Trans with (Map_embed (Seqtl f)++g).
2:(Apply Map_embed_comp;Auto with algebra).
Apply Trans with (Map_embed (Seqtl f))++(Map_embed g).
(Apply (!concat_comp ??? (Seqtl (Map_embed f)) (Map_embed (Seqtl f)) (Map_embed g)(Map_embed g));Auto with algebra).
Apply Sym.
Change (Map_embed ((Seqtl f)++g)) =' ((Map_embed (Seqtl f))++(Map_embed g)) in(seq??).
(Apply H;Auto with algebra).
Qed.

Hints Resolve Map_embed_concat : algebra.

Lemma concat_Map_embed :
  (E:Setoid; A:(part_set E); n,m:Nat; f:(seq n A); g:(seq m A)) 
    (Map_embed f)++(Map_embed g)='(Map_embed f++g) in(seq??).
Auto with algebra.
Qed.

Hints Resolve concat_Map_embed.

Lemma Map_embed_prop : (A,D:Setoid;B:(part_set A);v:(MAP D B))
  (i:D)(in_part (Map_embed v i) B).
Simpl.
Intros.
NewDestruct (v i).
Simpl.
Red;Auto with algebra.
Qed.
