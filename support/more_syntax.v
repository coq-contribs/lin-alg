(** %\subsection*{ support :  more\_syntax.v }%*)
Require Export Module_cat.

(**
In this file we introduce more syntax to make the development
more readable. Since we will be working in a commutative (abelian)
setting most of the time, we introduce the notation [+'] for the
"sgroup_law" and [zero] (instead of "one" or "unit") for the 
monoid-unit. In fact, since in rings we also have a multiplicative
unit (called [ring_unit]), we can reserve the notation [one] for
that. Note also that the syntax defined in this files leaves implicit
the structures on which the notions are derived; that is to say, e.g.,
[+'] is defined in sgroups, but the notation [a +' b] does not mention
the sgroup where [a] and [b] are taken from. (Just like 'normal'
mathematics)

I found out that due to coercions, the underlying multiplicative 
monoid of a ring R will just be printed as 'R', which sometimes 
leads to confusion: then we may get subgoals that seem to require
us to prove things like (a+b)v = a(bv); but since the "addition"
actually takes place in the multiplicative semigroup, it is in
fact a multiplication. Unfortunately the coercions causing this 
behaviour are in the Algebra contribution, which I prefer not to
change. Moreover, this behaviour is really an exception; in most
cases not printing the coercions is in fact the desired behaviour.
*)

(** %\label{moresyntax}% *)

Notation "a +' b" := (sgroup_law ? a b) (at level 4, left associativity).

Notation "'zero' a" := (monoid_unit a) (at level 10).

Notation "'one'" := (ring_unit ?).

Notation "a 'mX' b" := (module_mult a b) (at level 3, right associativity)
  V8only (at level 42, right associativity).

Notation "a 'rX' b" := (ring_mult a b) (at level 3, right associativity)
  V8only (at level 42, right associativity).

Notation "'min' a" := (group_inverse ? a) (at level 10).
