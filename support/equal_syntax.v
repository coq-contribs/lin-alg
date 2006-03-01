(** %\subsection*{ support :  equal\_syntax.v }%*)
(** This file introduces the notation [='] for the [Equal] relation.
We separate this from the rest of the algebra syntax since many
definitions only require setoids and nothing more.
%\label{equalsyntax}% *)
Require Export Sets.

Notation "a =' b 'in' c" := (Equal (s:=c) a b) (at level 70, b at next level).

Notation "a =' b" := (a =' b in _) (at level 70, only parsing).