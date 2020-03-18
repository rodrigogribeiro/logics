Require Import
        Syntax.Syntax
        Syntax.OPE.

From Equations Require Import Equations.

(** definition of substitutions *)

Inductive sub (G : con) : con -> Type :=
| Nil  : sub G []
| Snoc : forall G' t, sub G G' -> term G t -> sub G (t :: G').

Arguments Nil {G}.
Arguments Snoc {G}{G'}{t}.

(** embeddings of substitutions *)

Equations embed_sub {G G1 G'}(s : sub G G')(p : OPE G1 G) : sub G1 G' :=
  embed_sub Nil p        := Nil ;
  embed_sub (Snoc s t) p := Snoc (embed_sub s p) (embed_term p t).

Equations drop_sub {G G' t}(s : sub G G') : sub (t :: G) G' :=
  drop_sub s := embed_sub s wk.

Equations keep_sub {G G' t}(s : sub G G') : sub (t :: G) (t :: G') :=
  keep_sub s := Snoc (drop_sub s) (Var Here).

Equations inject_OPE {G G'} (p : OPE G G') : sub G G' :=
  inject_OPE Done     := Nil ;
  inject_OPE (Drop p) := drop_sub (inject_OPE p) ; 
  inject_OPE (Keep p) := keep_sub (inject_OPE p).

(** substitution application *)

Equations apply_var {G G' t}(s : sub G G')(v : member t G') : term G t :=
  apply_var (Snoc s t) Here      := t ;
  apply_var (Snoc s t) (There v) := apply_var s v.

Equations apply_sub {G G' t}(s : sub G G')(e : term G' t) : term G t :=
  apply_sub s (Var v)    := apply_var s v ;
  apply_sub s (Abs e)    := Abs (apply_sub (keep_sub s) e) ;
  apply_sub s (App e e') := App (apply_sub s e) (apply_sub s e').

Equations id_sub G : sub G G :=
  id_sub []       := Nil ;
  id_sub (t :: G') := keep_sub (id_sub G').

Arguments id_sub {G}.


