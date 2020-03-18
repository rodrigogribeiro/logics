Require Export
        List.

Export ListNotations.

From Equations Require Import Equations.

(** type syntax *)

Inductive ty : Set :=
| Base  : ty
| Arrow : ty -> ty -> ty.

Notation "t1 '==>' t2" := (Arrow t1 t2)
                          (at level 70, right associativity).
(** contexts are just lists *)

Definition con := list ty.

(** list membership *)

Inductive member (t : ty) : con -> Type :=
| Here  : forall ts, member t (t :: ts)
| There : forall ts t', member t ts -> member t (t' :: ts).

Arguments Here {t}{ts}.
Arguments There {t}{ts}{t'}.

Derive Signature for member.

(** term syntax *)

Inductive term G : ty -> Type :=
| Var : forall t, member t G -> term G t
| Abs : forall t t', term (t' :: G) t -> term G (t' ==> t)
| App : forall t t', term G (t' ==> t) -> term G t' -> term G t. 


Arguments Var {G}{t}.
Arguments Abs {G}{t}{t'}.
Arguments App {G}{t}{t'}.

