(** %\subsection*{ extras :  finite\_misc.v }%*)
Set Implicit Arguments.
Require Export empty.
Require Export conshdtl.

(** - Like before_after, a file with stuff I thought I could use some day but didn't: *)

(* The relation with lists *)

Section list_seq.
(* We define a list with entries in a setoid *)
Inductive Type SList [A:Setoid] := Snil : (SList A) | Scons : A->(SList A)->(SList A).

Fixpoint Length [A:Setoid;L:(SList A)] : nat :=
Cases L of Snil => O | (Scons _ L') => (S (Length L')) end.

Fixpoint SList2fun [A:Setoid;L:(SList A)] : (seq (Length L) A) :=
<[L:(SList A)]((seq (Length L) A)::Type)>
Cases L of Snil => (empty_seq A) |
         ( Scons a L' ) => a;;(SList2fun L')
end.

Definition SList2seq : (A:Setoid;L:(SList A))(seq (Length L) A).
Intros.
Red.
Apply (Build_Map 3!(SList2fun L)).
Red.
Intros k k'.
Elim k.
Induction index.
Elim k'.
Induction index0.
Intros.
(Apply Ap_comp;Auto with algebra).
Intros.
Inversion H0.
Elim k'.
Induction index0.
Simpl.
Intros.
Inversion H0.
Intros.
(Apply Ap_comp;Auto with algebra).
Defined.

Fixpoint Seq2SList [A:Setoid;n:nat] : (seq n A)->(SList A) := <[n:nat]((seq n A)->(SList A))>
 Cases n of O => [b:(seq O A)](Snil A) 
          | (S m) => [b:(seq (S m) A)](Scons (b (Build_finiteT (le_lt_n_Sm ?? (le_O_n m)))) (Seq2SList (Seqtl b))) end.
End list_seq.

Section other.
(* The next reverses a sequence: 0...n-1 -> n-1...0 *)
Definition reverse_seq : (n:nat)(seq n (fin n)).
Induction n.
(* First the case n=0, ie. the empty map *)
Apply (Build_Map 3![nonexistent_thingy:(fin O)]nonexistent_thingy).
Red.
Auto with algebra.
(* The nonempty case. *)
Intros.
(* If we have the reversing map X on 0...n0-1 (=(fin n)), the reversing map on 0...n0 *)
(* can be made thus: we map 0 to n0, and we map m+1 to X(m) *)
Apply (Build_Map 3![finelt:(fin (S n0))]
      <[_:(fin (S n0))](fin (S n0))>
        Cases finelt of
          (Build_finiteT x x0) => 
           (<[x1:nat](lt x1 (S n0))->(fin (S n0))>
              Cases x of
                O => [_:(lt (0) (S n0))](Build_finiteT (lt_n_Sn n0))
              | (S m) => 
                 [HSm:(lt (S m) (S n0))]
                  (Build_finiteT
                    (lt_S
                      (index (X (Build_finiteT (lt_S_n m n0 HSm)))) n0
                      (in_range_prf (X (Build_finiteT (lt_S_n m n0 HSm))))))
              end x0)
        end).
Red.
(* To prove the fun_compatibility of the newly devised function: *)
Intro x.
Case x.
Intro x0.
Case x0.
Intros l y.
Case y.
Intro x1.
Case x1. 
(* first the cases where x=0 or y=0 *)
Simpl.
Tauto.
Simpl.
Intros.
Inversion H.
Simpl.
Intros n1 l y.
Case y.
Intro x1.
Case x1.
Intros.
Inversion H.
(* Now the interesting case. Here we make use of the fun_compatibility of X *)
Intros.
Inversion H.
Elim X.
Intros.
Simpl.
Red in Map_compatible_prf.
Simpl in Map_compatible_prf.
(Apply Map_compatible_prf;Auto with algebra).
Defined.

(* Reverting finite sequences *)
Definition reverse := [n:nat;X:Setoid;f:(seq n X)]((comp_map_map f (reverse_seq n))::(seq n X)).

(* Now we can easily cons elements at the right part of a seq: *)

Definition consr : (X:Setoid; n:nat; x:X; f:(seq n X))(seq (S n) X).
Intros.
Exact (reverse x;;(reverse f)).
Defined.
End other.