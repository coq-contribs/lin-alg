(** %\subsection*{ support :  finite.v }%*)
Set Implicit Arguments.
Require Export Arith.
Require Export equal_syntax.


(** - The setoid of natural numbers - not really necessary but it's nice to have a
 uniform approach *)

Definition Nat : Setoid.
Apply (Build_Setoid 2![i,j:nat]i=j).
Split;Try Split;Red;Unfold app_rel;Simpl;Auto.
Intros;Transitivity y;Auto.
Defined.



(** - In this formalisation, we often need the sets $\{0...n-1\}$ 
 We use these for finite sequences: $(a_1...a_n)$ is represented 
 as a setoid function $a:\{0...n-1\}\to A$; also these elements are used as 
 indices into these sequences. Since we use a function type to 
 represent a sequence, we can just type [(a i)] for $a_i$. 
 - finiteT will serve as the Type on which we base our finite 
 setoids [(fin N)] = $\{0...N-1\} = \{ n \in N | n<N \}$. *)

Record finiteT [N:Nat] : Type := 
  {index : nat;
   in_range_prf : (lt index N)}.



(** - The setoid itself is called [(fin N)]. [n:(finiteT N)] is really a pair <n,H>;
 <n,H> and <n',H'> will be deemed equal if n and n' are; the proofs H of n<N and 
 H' of n'(=n)<N may differ. 

 - %\bf% Useful knowledge: if [H:(lt i n)] then [(Build_finiteT H):(fin n)]

%\label{fin}% *)


Definition fin : Nat->Setoid.
Intro N.
Apply (!Build_Setoid (finiteT N) [n,m:(finiteT N)](index n)=(index m)).
Red.
Split.
Red.
Intro.
Red.
Reflexivity.
Red.
Split.
Red.
Intros.
Red in H.
Red in H0.
Red.
Transitivity (index y).
Assumption.
Assumption.
Red.
Intros.
Red in H.
Red.
Symmetry.
Assumption.
Defined.

Lemma fin_equation : (n,i,j:nat;Hi:(lt i n);Hj:(lt j n)) 
  i=j -> (Build_finiteT Hi)='(Build_finiteT Hj) in (fin n).
Intros.
Simpl.
Auto.
Qed.

(* This formalisation is heavily dependent on Loic Pottier's algebra contribution *)
(* and therefore relies heavily on the algebra Hints database as well. *)
(* We feel free to extend it: *)

Hints Resolve fin_equation : algebra.

Lemma fin_decidable : (n:Nat;i,i':(fin n)) i =' i' \/ ~i=' i'.
Intros.
Simpl.
Cut (k,l:nat)k=l\/~k=l.
Intro.
Auto.
Clear i' i n.
Double Induction k l.
Left;Auto.
Intros;Right.
Unfold not.
Intro.
Inversion H0.
Intros;Right.
Unfold not.
Intro.
Inversion H0.
Intros.
Elim (H0 n).
Auto.
Auto.
Qed.


Lemma fin_O_nonexistent : (fin (0))->False.
NewDestruct 1.
Inversion_clear in_range_prf0.
Qed.

Hints Resolve fin_O_nonexistent : algebra.

Lemma fin_S_O_unique : (i,j:(fin (1)))i='j.
Intro.
Case i.
Intro x.
Case x.
Intros l j.
Case j.
Intro x0.
Case x0.
Simpl.
Auto.
Intros.
Inversion in_range_prf0.
Inversion H0.
Intros.
Inversion in_range_prf0.
Inversion H0.
Qed.

Hints Resolve fin_S_O_unique : algebra.

(** - A sequence is just a setoid function from (fin n) to A: 
%\label{seq}% *)
Definition seq [n:Nat;A:Setoid]:=(MAP (fin n) A).

(* Somehow this is necessary: *)
Lemma toSeq : (A:Setoid;n:Nat;v,v':(Map (fin n) A)) 
  v =' v' in (seq??) -> v =' v' in (MAP??).
Auto.
Qed.

Lemma toMap : (A:Setoid;n:Nat;v,v':(Map (fin n) A)) 
  v='v' in (MAP??) -> v='v' in (seq??).
Auto.
Qed.

Hints Resolve toSeq toMap : algebra.
