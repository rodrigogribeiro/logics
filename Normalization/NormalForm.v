Require Import
        Syntax.Syntax
        Syntax.OPE.

From Equations Require Import Equations.


(** normal forms *)

Inductive nf : con -> ty -> Type :=
| NE : forall G, ne G Base -> nf G Base
| NAbs : forall G t t', nf (t' :: G) t -> nf G (t' ==> t)
with ne : con -> ty -> Type :=
| NVar : forall G t, member t G -> ne G t
| NApp : forall G t t', ne G (t' ==> t) -> nf G t' -> ne G t.

Arguments NE {G}.
Arguments NAbs {G}{t}{t'}.
Arguments NVar {G}{t}.
Arguments NApp {G}{t}{t'}.

Equations embed_nf {G G' t}(p : OPE G G')(n : nf G' t) : nf G t :={
  embed_nf p (NE n)   := NE (embed_ne p n) ;
  embed_nf p (NAbs e) := NAbs (embed_nf (Keep p) e) }
where
  embed_ne {G G' t}(p : OPE G G')(n : ne G' t) : ne G t :={
  embed_ne p (NVar v)     := NVar (embed_member p v) ;
  embed_ne p (NApp e e')  := NApp (embed_ne p e) (embed_nf p e') }.

