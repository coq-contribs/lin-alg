(** %\subsection*{ support :  sums.v }%*)
Set Implicit Arguments.
Require Export Map_embed.
Require Export algebra_omissions.
Require Export Sub_monoid.
Require Export more_syntax.

(** - A sequence of v1...vn of elements in a monoid V is a map (fin n)->V.
 We define the sum of a sequence of these elements.
 Of course we take the sum of an empty sequence to be zero 

 %\label{sum}% *)
Fixpoint sum [V:monoid;n:Nat] : (seq n V) -> V :=
   <[n:Nat](seq n V)->V>
  Cases n of 
    O => [x:(seq O V)] (zero V)
  | (S m) => [x:(seq (S m) V)] (head x)+'(sum (Seqtl x))
end.

Lemma sum_comp: (M:monoid;n:Nat;f,f':(seq n M))
  f='f' -> (sum f)='(sum f').
NewInduction n.
Intros.
Simpl.
Apply Refl.
Intros.
Unfold sum.
(Apply SGROUP_comp;Auto with algebra).
Apply IHn.
Change (Seqtl f)='(Seqtl f').
(Apply Seqtl_comp;Auto with algebra).
Qed.

Hints Resolve sum_comp : algebra.

Lemma sum_cons : (M:monoid;m:M; n:Nat;f:(seq n M))
  (sum m;;f)=' m +' (sum f).
Intros.
Induction n.
Simpl.
Apply Refl.
Unfold 1 sum.
Apply SGROUP_comp;Auto with algebra.
Apply sum_comp.
Generalize Dependent (Seqtl_cons_inv m f);Intro p.
Apply p.
Qed.

Hints Resolve sum_cons : algebra.

Lemma sum_concat: (n,m:Nat;G:monoid;a:(seq n G);b:(seq m G))
  (sum a++b)='(sum a)+'(sum b).
NewInduction n.
Intros.
(Apply Trans with (zero G) +'(sum b);Auto with algebra).
Intros.
(Apply Trans with (sum (hdtl a))+'(sum b);Auto with algebra).
(Apply Trans with (sum (hdtl a)++b);Auto with algebra).
Apply Trans with (sum (head a);;((Seqtl a)++b)).
Unfold hdtl.
(Apply sum_comp;Auto with algebra).
Unfold hdtl.
(Apply Trans with (head a)+'(sum (Seqtl a)++b);Auto with algebra).
(Apply Trans with ((head a)+'(sum (Seqtl a)))+' (sum b);Auto with algebra).
(Apply Trans with (head a)+'((sum (Seqtl a))+'(sum b));Auto with algebra).
Qed.

Hints Resolve sum_concat : algebra.

Lemma subtype_sum : (n:nat;A:monoid;B:(submonoid A);c:(seq n B))
  (subtype_elt (sum c))='(sum (Map_embed c)).
Intros.
Apply Sym.
NewInduction n.
Simpl.
Auto with algebra.
(Apply Trans with (head (Map_embed c))+'(sum (Seqtl (Map_embed c)));Auto with algebra).
Apply Trans with (subtype_elt (head c)+'(sum (Seqtl c))).
(Apply Trans with (subtype_elt (head c))+'(subtype_elt (sum (Seqtl c)));Auto with algebra).
(Apply Trans with ((head (Map_embed c)) +' (sum (Map_embed (Seqtl c))));Auto with algebra).
(Apply SGROUP_comp;Auto with algebra).
(Apply sum_comp;Auto with algebra).
(Apply Sym;Auto with algebra).
Generalize Map_embed_Seqtl.
Intro p.
Apply (p ??? (c::(seq??))).
Apply subtype_elt_comp.
(Apply Sym;Auto with algebra).
Qed.