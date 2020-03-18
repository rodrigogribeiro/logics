Require Export 
        Syntax.Syntax.

From Equations Require Import Equations.

(** definition of order preserving embeddings *)

Inductive OPE : con -> con -> Type :=
| Done
  : OPE [] []
| Drop
  : forall G G' t,
    OPE G G' -> OPE (t :: G) G'
| Keep
  : forall G G' t,
    OPE G G' -> OPE (t :: G) (t :: G').

Arguments Drop {G}{G'}{t}.
Arguments Keep {G}{G'}{t}.

(** embeddings in membership proofs *)

Equations embed_member {G G' t}(p : OPE G G')(v : member t G') : member t G :=
  embed_member Done     v         := v;
  embed_member (Drop p) v         := There (embed_member p v);
  embed_member (Keep p) Here      := Here;
  embed_member (Keep p) (There v) := There (embed_member p v).

Equations embed_term {G G' t}(p : OPE G G')(e : term G' t) : term G t :=
  embed_term p (Var v)    := Var (embed_member p v) ;
  embed_term p (Abs e)    := Abs (embed_term (Keep p) e) ;
  embed_term p (App e e') := App (embed_term p e) (embed_term p e').

Equations embed_id (G : con) : OPE G G :=
  embed_id []       := Done ;
  embed_id (t :: G') := Keep (embed_id G').

Arguments embed_id {G}.

Equations wk t G : OPE (t :: G) G :=
  wk t G := Drop embed_id.

Arguments wk {t}{G}.

Derive Signature for OPE.

Equations(noind) compose_OPE {G G1 G'}(p : OPE G1 G')(p1 : OPE G G1) : OPE G G' :=
  compose_OPE p Done             := p ;
  compose_OPE p (Drop p')        := Drop (compose_OPE p p') ;
  compose_OPE (Drop p) (Keep p') := Drop (compose_OPE p p') ;
  compose_OPE (Keep p) (Keep p') := Keep (compose_OPE p p').
