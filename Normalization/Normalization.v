Require Import
        Syntax.Syntax
        Syntax.Sub
        Syntax.OPE
        Normalization.NormalForm.


(** definition of normalization by evaluation *)

Equations norm_ty (t : ty)(G : con) : Type :=
  norm_ty Base       G := nf G Base ; 
  norm_ty (t ==> t') G := forall G', OPE G' G -> norm_ty t G' -> norm_ty t' G'.

Equations embed_ty t {G G'}(p : OPE G' G)(e : norm_ty t G) : norm_ty t G' :=
  embed_ty Base        p tn := embed_nf p tn ;
  embed_ty (t1 ==> t2) p tn := fun G' d => tn G' (compose_OPE p d).

Arguments embed_ty {t}{G}{G'}.

Inductive norm_con : con -> con -> Type :=
| NNil
  : forall G', norm_con [] G'
| NSnoc
  : forall t G G', norm_con G G' -> norm_ty t G' -> norm_con (t :: G) G'.

Arguments NNil {G'}.
Arguments NSnoc {t}{G}{G'}.

Equations embed_con {G G1 G'}(p : OPE G' G1)(n : norm_con G G1) : norm_con G G' :=
  embed_con p NNil          := NNil ;
  embed_con p (NSnoc n' t') := NSnoc (embed_con p n') (embed_ty p t'). 

Derive Signature for norm_con.

Equations norm_member {t G}(p : member t G) {G'}(nc : norm_con G G') : norm_ty t G' :=
  norm_member Here      (NSnoc _ tn) := tn ;
  norm_member (There v) (NSnoc n _)  := norm_member v n.

Equations norm_term {G t}(e : term G t){G'}(nc : norm_con G G') : norm_ty t G' :=
  norm_term (Var v)    nc := norm_member v nc ;
  norm_term (Abs e)    nc := fun G' p an => norm_term e (NSnoc (embed_con p nc) an) ;
  norm_term (App e e') nc := norm_term e nc _ embed_id (norm_term e' nc).

Equations quote_term t G (tn : norm_ty t G) : nf G t := {
  quote_term Base        G tn := tn ;
  quote_term (t1 ==> t2) G tn
     := NAbs (quote_term _ _ (tn _ wk (unquote_term _ _ (NVar Here)))) }
where
  unquote_term t G (n : ne G t) : norm_ty t G :=
  unquote_term Base        G n := NE n ;
  unquote_term (t1 ==> t2) G n :=
    fun G' p an => unquote_term _ _ (NApp (embed_ne p n) (quote_term _ _ an)).

Arguments quote_term {t}{G}.
Arguments unquote_term {t}{G}.

Equations quote_con G : norm_con G G :=
  quote_con []       := NNil ;
  quote_con (t :: G') := NSnoc (embed_con wk (quote_con _)) (unquote_term (NVar Here)). 

Arguments quote_con {G}.

Definition nbe_nf {t G}(e : term G t) : nf G t :=
  quote_term (norm_term e quote_con).

