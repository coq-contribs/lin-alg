(** %\subsection*{ support :  distinct\_facts.v }%*)
Set Implicit Arguments.
Require Export omit_facts.
Require Export seq_set_seq.
Require Export distinct.

Lemma distinct_cons : (A:Setoid;n:Nat;v:(seq n A))
  (distinct v) -> (a:A) ((i:(fin n)) ~a='(v i)) -> (distinct a;;v).
Intros.
Red.
Intro;Case i;Clear i;Intro i;Case i;Clear i.
Intros hi j;Case j;Clear j;Intro j;Case j;Clear j.
Intros.
Simpl in H1.
Absurd O=O;Auto.
Intros.
Simpl.
(Apply H0;Auto with algebra).
Intros i hi j;Case j;Clear j;Intro j;Case j;Clear j.
Intros.
Simpl.
Red;Intro;Red in H0.
(Apply (H0 (Build_finiteT (lt_S_n??hi)));Auto with algebra).
Intros j hj hij.
Red in H.
Simpl.
(Apply H;Auto with algebra).
Qed.

Hints Resolve distinct_cons : algebra.

Lemma Seqtl_preserves_distinct : (A:Setoid;n:Nat;v:(seq n A))
  (distinct v) -> (distinct (Seqtl v)).
Unfold distinct.
Induction n.
Simpl.
Auto with algebra.
Intros.
Generalize H1;Clear H1.
Case i;Case j.
Intro x;Case x.
Intros l x0;Case x0.
Intros l0 H1.
Simpl in H1.
Absurd O=O;Auto.
Intros n1 l0.
Intro q;Clear q.
Red;Red in H0.
Intro.
Cut (v (Build_finiteT (lt_n_S ?? l0)))=' (v (Build_finiteT (lt_n_S ?? l))).
Intro.
(Apply H0 with (Build_finiteT (lt_n_S (S n1) (pred (S n0)) l0)) (Build_finiteT (lt_n_S (0) (pred (S n0)) l));Auto with algebra).
Simpl.
Auto.
(Apply Trans with ((Seqtl v) (Build_finiteT l0));Auto with algebra).
Intros n1 l x0;Case x0.
Intros l0 H1.
Clear H1.
Red;Intro.
Cut (v (Build_finiteT (lt_n_S ?? l0)))=' (v (Build_finiteT (lt_n_S ?? l))).
Intro.
Red in H0.
(Apply H0  with (Build_finiteT (lt_n_S ?? l0)) (Build_finiteT (lt_n_S ?? l));Auto with algebra).
Simpl.
Auto.
(Apply Trans with ((Seqtl v) (Build_finiteT l0));Auto with algebra).
Intros n2 l0.
Simpl.
Intros.
(Apply H0;Auto with algebra).
Qed.

Hints Resolve Seqtl_preserves_distinct : algebra.

Lemma omit_preserves_distinct : (A:Setoid;n:Nat;v:(seq (S n) A))
  (distinct v) -> (i:(fin (S n)))(distinct (omit v i)).
Induction n.
Intros.
Red.
Inversion i0.
Inversion in_range_prf.

Intros.
Case i.
Intro x;Case x.
Intro l.
(Apply distinct_comp with (Seqtl v);Auto with algebra).

Intros n1 l.
(Apply distinct_comp with (head v);;(omit (Seqtl v) (Build_finiteT (lt_S_n??l)));Auto with algebra).
Unfold distinct in H H0.
Unfold distinct. 
Intros i0 j.
Case i0.
Case j.
Clear x.
Intro x;Case x.
Intros p x';Case x'.
Intros p' H'.
Simpl in H'.
Absurd O=O;Auto.
Intros n2 p' q;Clear q.
Red;Red in H0;Intro.
Generalize (omit_removes (Seqtl v) (Build_finiteT (lt_S_n??l)) (Build_finiteT (lt_S_n??p'))).
Intro k;Inversion_clear k.
NewDestruct x0.
(Apply H0 with (Build_finiteT (lt_O_Sn (S n0))) (Build_finiteT (lt_n_S??in_range_prf));Auto with algebra).
Simpl.
Auto.
(Apply Trans with (head v);Auto with algebra).
(Apply Trans with (Seqtl v (Build_finiteT in_range_prf));Auto with algebra).
(Apply Trans with ((head v);;(omit (Seqtl v) (Build_finiteT (lt_S_n n1 (S n0) l))) (Build_finiteT p'));Auto with algebra).

Intros n2 l1 x1.
Case x1.
Intros l2 H2.
Clear H2.
Cut ~((omit (Seqtl v) (Build_finiteT (lt_S_n n1 (S n0) l))) (Build_finiteT (lt_S_n ?? l1)))='(head v).
Unfold head.
Auto with algebra.
Red.
Intro.
Generalize (omit_removes (Seqtl v) (Build_finiteT (lt_S_n n1 (S n0) l)) (Build_finiteT (lt_S_n n2 n0 l1))).
Intro.
Inversion_clear X.
NewDestruct x0.
Cut ((Seqtl v) (Build_finiteT in_range_prf))='(head v).
Intros.
Cut (v (Build_finiteT (lt_n_S??in_range_prf)))='(head v).
Unfold head.
Intros.
Cut ~(Build_finiteT (lt_n_S index (S n0) in_range_prf))='(Build_finiteT (lt_O_Sn (S n0)))in(fin?).
Intro.
Red in H0.
Apply H0 with (Build_finiteT (lt_n_S index (S n0) in_range_prf)) (Build_finiteT (lt_O_Sn (S n0)));Auto.
Simpl.
Auto.
Auto with algebra.
(Apply Trans with ((omit (Seqtl v) (Build_finiteT (lt_S_n n1 (S n0) l))) (Build_finiteT (lt_S_n n2 n0 l1)));Auto with algebra).

Intros n3 l0 H2.
Simpl in H2.
Cut ~((omit (Seqtl v) (Build_finiteT (lt_S_n n1 (S n0) l))) (Build_finiteT (lt_S_n??l0)))='((omit (Seqtl v) (Build_finiteT (lt_S_n n1 (S n0) l))) (Build_finiteT (lt_S_n??l1))).
Unfold not;Auto with algebra.
(Apply H;Auto with algebra).
Intros.
Change   ~(Seqtl v i1) =' (Seqtl v j0). 
(Apply Seqtl_preserves_distinct;Auto with algebra).
Qed.

Hints Resolve omit_preserves_distinct : algebra.

Lemma distinct_omit_removes_all : (A:Setoid;n:Nat;v:(seq (S n) A))
  (distinct v) -> (i:(fin (S n));j:(fin n)) ~((omit v i) j)='(v i).
Induction n;Intros.
Inversion_clear j;Inversion_clear in_range_prf.
Red in H0.
Elim i.
Intro x;Case x;Intros.
Cut ~((Seqtl v) j) =' (v (Build_finiteT in_range_prf)).
Case j.
Intros.
Cut ~(v (Build_finiteT (lt_n_S??in_range_prf0)))='(v (Build_finiteT in_range_prf)).
Intros.
Cut ~(Build_finiteT (lt_n_S index (S n0) in_range_prf0)) =' (Build_finiteT in_range_prf)in(fin?).
Intro.
Red in H2;Red.
Auto with algebra.
Simpl.
Auto.
Auto with algebra.
Case j.
Intros x0 l.
Cut ~(v (Build_finiteT (lt_n_S??l)))='(v (Build_finiteT in_range_prf)).
Unfold not;Auto with algebra.
Cut ~(Build_finiteT (lt_n_S x0 (S n0) l)) =' (Build_finiteT in_range_prf)in(fin?).
Intro.
(Apply H0;Auto with algebra).
Red.
Simpl.
Intro.
Inversion H1.
Red;Intro.
Cut ((head v);;(omit (Seqtl v) (Build_finiteT (lt_S_n??in_range_prf))) j)='(v (Build_finiteT in_range_prf)).
Case j.
Intro x0.
Case x0.
Intro l.
Intro.
Cut (head v)='(v (Build_finiteT in_range_prf)).
Intro.
Unfold head in H3.
Red in H0.
(Apply H0 with (Build_finiteT (lt_O_Sn (S n0))) (Build_finiteT in_range_prf);Auto with algebra).
Simpl.
Auto.
(Apply Trans with ((head v);;(omit (Seqtl v) (Build_finiteT (lt_S_n n1 (S n0) in_range_prf))) (Build_finiteT l));Auto with algebra).
Intros n2 l H2.
Cut ((omit (Seqtl v) (Build_finiteT (lt_S_n n1 (S n0) in_range_prf))) (Build_finiteT (lt_S_n??l)))='(v (Build_finiteT in_range_prf)).
Intro.
Cut ((omit (Seqtl v) (Build_finiteT (lt_S_n n1 (S n0) in_range_prf))) (Build_finiteT (lt_S_n??l)))='((Seqtl v) (Build_finiteT (lt_S_n??in_range_prf))).
Intro.
Red in H.
Cut (distinct (Seqtl v)).
Intro.
(Apply H with (Seqtl v) (Build_finiteT (lt_S_n n1 (S n0) in_range_prf)) (Build_finiteT (lt_S_n n2 n0 l));Auto with algebra).
(Apply Seqtl_preserves_distinct;Auto with algebra).
(Apply Trans with (v (Build_finiteT in_range_prf));Auto with algebra).
(Apply Trans with ((head v) ;;(omit (Seqtl v) (Build_finiteT (lt_S_n n1 (S n0) in_range_prf))) (Build_finiteT l));Auto with algebra).
(Apply Trans with (omit v (Build_finiteT in_range_prf) j);Auto with algebra).
Qed.

Lemma Map_embed_preserves_distinct : (A:Setoid;n:Nat;B:(part_set A);v:(seq n B))
  (distinct v)->(distinct (Map_embed v)).
Unfold distinct.
Unfold not.
Intros.
(Apply H with i j;Auto with algebra).
Qed.

Hints Resolve Map_embed_preserves_distinct : algebra.

Lemma Map_embed_reflects_distinct : (A:Setoid;n:Nat;B:(part_set A);v:(seq n B))
  (distinct (Map_embed v))->(distinct v).
Unfold distinct.
Unfold not.
Intros.
(Apply H with i j;Auto with algebra).
Qed.

Lemma seq_set_seq_preserves_distinct : (A:Setoid;n:Nat;v:(seq n A))
  (distinct v)->(distinct (seq_set_seq v)).
Unfold distinct.
Intros.
Simpl.
Red;Intro.
Red in H;(Apply (H??H0);Auto with algebra).
Qed.

Hints Resolve seq_set_seq_preserves_distinct : algebra.

Lemma seq_set_seq_respects_distinct : (A:Setoid;n:Nat;v:(seq n A))
  (distinct (seq_set_seq v))->(distinct v).
Unfold distinct.
Intros.
Simpl.
Red;Intro.
Red in H;(Apply (H??H0);Auto with algebra).
Qed.

Lemma cast_seq_preserves_distinct : (A:Setoid;n,m:Nat;v:(seq n A);H:n='m)
  (distinct v)->(distinct (cast_seq v H)).
Unfold cast_seq distinct.
Intros until H.
Elim v.
Simpl.
Intros.
Red;Intro;Red in H0;(Apply H0 with (cast_fin i (sym_eq nat n m H)) (cast_fin j (sym_eq nat n m H));Auto with algebra).
Unfold cast_fin.
Generalize H1;Elim i;Elim j.
Simpl.
Auto.
Qed.

Hints Resolve cast_seq_preserves_distinct : algebra.

Lemma cast_seq_respects_distinct : (A:Setoid;n,m:Nat;v:(seq n A);H:n='m)
  (distinct (cast_seq v H))->(distinct v).
Unfold distinct cast_seq.
Intros until H.
NewDestruct v.
Simpl.
Intros.
Red;Intro;Red in H0.
Apply H0 with (cast_fin i H) (cast_fin j H).
Unfold cast_fin.
Generalize H1;Elim i;Elim j.
Simpl.
Auto.
(Apply Trans with (Ap i);Auto with algebra).
(Apply Map_compatible_prf;Auto with algebra).
Unfold cast_fin.
Elim i.
Simpl.
Auto.
(Apply Trans with (Ap j);Auto with algebra).
(Apply Map_compatible_prf;Auto with algebra).
Unfold cast_fin.
Elim j.
Simpl.
Auto.
Qed.