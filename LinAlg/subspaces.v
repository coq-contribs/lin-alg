(** * subspaces.v *)
Section MAIN.
Set Implicit Arguments.
Require Export vecspaces_verybasic.
Require Export arb_intersections.
Require Export Sub_module.
Require Export Singleton.
Require Export algebra_omissions.

Variable F:field.
Variable V:(vectorspace F).
Section Subspace_def.

(** %\tocdef{subspace}% *)
Definition subspace :=
 [F:field; V:(vectorspace F)](submodule V).

(** - Some finger-flexing first *)
Variable W:(subspace V).
Definition inj_subspace : (Hom (W::(VECSP F)) V).
(Apply (!BUILD_HOM_MODULE F (W::(VECSP F)) V [x:W](subtype_elt x));Auto with algebra).
Defined.
(* This injects the subspace into its "parent" space *)

Lemma inj_subspace_injective: (injective inj_subspace).
Red.
Auto with algebra.
Qed.

Lemma mult_inherited : (c:F)(x:W) (inj_subspace (c mX x))=' (c mX (inj_subspace x)).
Intros.
Case inj_subspace.
Intros.
Simpl.
Apply module_hom_prf.
Qed.
End Subspace_def.

Section subspace_awkward_utils.
(** - Officially, "a subspace is a subset that is itself a vectorspace..." We cannot
 have both W:(part_set V) and W:(subspace V). Therefore we need to define subspace-ness
 on the predicate-level as well. *)
(** %\tocdef{is\_subspace}% *)
Definition is_subspace : (part_set V)->Prop := [W:(part_set V)]
(in_part (zero V) W)
   /\((x,y:V) (in_part x W)->(in_part y W)->(in_part (x +' y) W))
      /\((c:F; x:V)(in_part x W)->(in_part (c mX x) W)).

Lemma is_subspace_comp : (S,S':(part_set V))
  S='S' -> (is_subspace S)->(is_subspace S').
Intros.
Red.
Red in H0.
Inversion_clear H0.
Inversion_clear H2.
Split.
(Apply in_part_comp_r with S;Auto with algebra).
Split.
Intros.
(Apply in_part_comp_r with S;Auto with algebra).
(Apply H0;Auto with algebra).
(Apply in_part_comp_r with S';Auto with algebra).
(Apply in_part_comp_r with S';Auto with algebra).
Intros.
(Apply in_part_comp_r with S;Auto with algebra).
(Apply H3;Auto with algebra).
(Apply in_part_comp_r with S';Auto with algebra).
Qed.

(** - From the predicate, then, we may define (uniformly) a subspace having the
 part_set as a carrier *)
Definition subspace_construction : (Ws : (part_set V)) (is_subspace Ws) ->
  (sigT (subspace V) [W:(subspace V)](W =' Ws in (part_set V))).
Unfold is_subspace.
Intros Ws (H1, (H2, H3)).
Cut (sigT (submodule V) [Wmod:(submodule V)](Wmod='Ws in (part_set V))).
Intro.
Inversion_clear X.
Exists x.
Assumption.
Cut (sigT (subgroup V) [Wgp:(subgroup V)](Wgp='Ws in (part_set V))).
Intro.
Inversion_clear X.
Exists (Build_submodule [a:F; v:V; Hyp:(in_part v (x::(part_set V)))](in_part_comp_r (H3 a v (in_part_comp_r Hyp H)) (Sym H))).
Simpl.
Assumption.
Cut (sigT (submonoid V) [Wmon:(submonoid V)](Wmon='Ws in (part_set V))).
Intro.
Inversion X.
Cut (v:V)(min one) mX v =' (min v).
Intro.
Exists (Build_subgroup [v:V; Hyp:(in_part v (x::(part_set V)))](in_part_comp_r (in_part_comp_l (H3 (min one) v (in_part_comp_r Hyp H)) (Sym (H0 v))) (Sym H))).
Simpl.
Assumption.
Intro.
(Apply Trans with (min (one mX v));Auto with algebra).
Cut (sigT (subsgroup V) [Wsgp:(subsgroup V)](Wsgp='Ws in (part_set V))).
Intro.
Inversion_clear X.
Exists (Build_submonoid (in_part_comp_r H1 (Sym H))).
Simpl.
Assumption.
Exists (Build_subsgroup [x,y:V;Hx:(in_part x Ws);Hy:(in_part y Ws)](H2 x y Hx Hy)).
Simpl.
Exact [x:V](conj ? ? [Hx:(in_part x Ws)]Hx [Hx:(in_part x Ws)]Hx).
Defined.

Definition alt_Build_subspace : (W:(part_set V))(is_subspace W)->(subspace V)
:= [W,H]let (w,_)=(subspace_construction H) in w.

Lemma alt_Build_subspace_OK : (W:(part_set V); HW:(is_subspace W)) 
  W='(alt_Build_subspace HW).
Intros.
Unfold alt_Build_subspace.
Case  (subspace_construction HW).
Auto with algebra.
Qed.

Lemma is_subspace_OK : (W:(subspace V)) (is_subspace W).
Intro.
Split;Try Split;Auto with algebra.
Qed.

(** - %\intoc{\bf Theorem 1.3}% literally (more-or-less; now easy to prove): *)
Lemma subspace_alt_characterization : (Ws:(part_set V))
   (in_part (zero V) Ws)
   /\((x,y:V)(in_part x Ws)->(in_part y Ws)->(in_part (x +' y) Ws))
     /\((c:F; x:V)(in_part x Ws)->(in_part (c mX x) Ws))
   <->(EXT W:(subspace V) | W =' Ws in (part_set V)).
Split. 
Intros.
Elim (subspace_construction H).
Intros.
Exists x;Auto.
Intro;Inversion_clear H.
Generalize (is_subspace_OK x).
Intro H;Red in H;Split;Try Split;Intuition;(Apply in_part_comp_r with (x::(part_set V));Auto with algebra).
(Apply H;Auto with algebra);(Apply in_part_comp_r with Ws;Auto with algebra).
(Apply H3;Auto with algebra);(Apply in_part_comp_r with Ws;Auto with algebra).
Qed.


Definition Set_of_subspaces : (part_set (part_set V)).
Apply (Build_Predicate 2![W](is_subspace W)).
Red.
Intros.
Red;Red in H.
Inversion_clear H.
Inversion_clear H2.
Split;Try Split.
(Apply in_part_comp_r with x;Auto with algebra).
Intros;(Apply in_part_comp_r with x;Auto with algebra).
(Apply H;Auto with algebra).
(Apply in_part_comp_r with y;Auto with algebra).
(Apply in_part_comp_r with y;Auto with algebra).
Intros.
(Apply in_part_comp_r with x;Auto with algebra).
(Apply H3;Auto with algebra);(Apply in_part_comp_r with y;Auto with algebra).
Defined.


(** - %\intoc{\bf Theorem 1.4}% *)
Lemma Set_of_subspaces_closed_under_intersection : 
  (WS:(part_set Set_of_subspaces))
    (is_subspace (intersection (inject_subsets WS))).
Red.
Repeat Split.
Simpl.
Intros;Inversion_clear H.
NewDestruct x.
Rename subtype_elt into S.
Simpl in H0.
NewDestruct S.
Simpl in H0 subtype_prf subtype_prf0.
Apply in_part_comp_r with subtype_elt.
Red in subtype_prf0.
Inversion_clear subtype_prf0.
Auto.
Auto with algebra.

Simpl.
Intros.
Generalize Dependent (H p H1);Generalize Dependent (H0 p H1).
Inversion_clear H1.
NewDestruct x0.
NewDestruct subtype_elt.
Simpl in H2.
Intros;Simpl in subtype_prf0.
Red in subtype_prf0.
Inversion_clear subtype_prf0.
Inversion_clear H5.
Apply in_part_comp_r with subtype_elt;Auto with algebra.
Apply H6;Apply in_part_comp_r with p;Auto with algebra.
Intros.
Simpl.
Intros;Simpl in H.
Generalize Dependent (H p H0).
Inversion_clear H0.
NewDestruct x0.
NewDestruct subtype_elt.
Simpl in H1 subtype_prf0.
Red in subtype_prf0.
Inversion_clear subtype_prf0.
Inversion_clear H2.
Intro;Apply in_part_comp_r with subtype_elt;Auto with algebra.
Apply H4;Apply in_part_comp_r with p;Auto with algebra.
Qed.
End subspace_awkward_utils.

End MAIN.

Section Examples.
Variable F:field.
Variable V:(vectorspace F).

Lemma singleton_zero_is_subspace : (is_subspace (single (zero V))).
Intros.
Repeat Split.
Simpl.
Apply Refl.
Intros.
Simpl in H H0.
Apply in_part_comp_l with (zero V)+'(zero V);Simpl;Auto with algebra.
Intros.
Simpl in H.
Apply in_part_comp_l with c mX (zero V);Simpl;Auto with algebra.
Qed.

Definition triv_subspace : (subspace V).
Apply alt_Build_subspace with (single (zero V)).
Apply singleton_zero_is_subspace.
Defined.

Definition full_subspace : (subspace V).
Apply alt_Build_subspace with (full V).
Repeat Split.
Defined.
End Examples.
