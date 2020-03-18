Require Import
        Syntax.Syntax
        Syntax.OPE
        Syntax.Sub
        Normalization.Normalization
        Normalization.NormalForm.

(** definition of the Kripke model *)

Section KRIPKE.

  Reserved Notation "w '||-'" (at level 40, no associativity).
  Reserved Infix "<<"  (at level 40, no associativity).

  Parameter world : Type.

  Parameter lt_world : world -> world -> Type.
  Notation  "w1 '<<' w2" := (lt_world w1 w2).

  Parameter lt_world_refl : forall w, w << w.
  Parameter lt_world_trans : forall w1 w2 w3,
      w1 << w2 ->
      w2 << w3 ->
      w1 << w3.

  Parameter forces : world -> Type.
  Notation "w '||-'" := (forces w).

  Parameter forces_lt_mono
    : forall w w', w << w' -> w ||- -> w' ||-.


  Equations forces_ty (w : world)(t : ty) : Type :=
    forces_ty w Base        := forces w ;
    forces_ty w (t1 ==> t2) := forall w', w << w' -> forces_ty w' t1 -> forces_ty w' t2.

  Equations forces_con (w : world)(G : con) : Type :=
    forces_con w []       := unit ;
    forces_con w (t :: G)  := forces_con w G * forces_ty w t.

  Definition forcing G t :=
    forall (w : world), forces_con w G -> forces_ty w t.

  Equations ty_mono {w w'} t (p : w << w')
    : forces_ty w t -> forces_ty w' t :=
    ty_mono Base        p d := forces_lt_mono _ _ p d ;
    ty_mono (t1 ==> t2) p d := fun _ q r => d _ (lt_world_trans _ _ _ p q) r.

  Equations con_mono G {w w'}
    : w << w' -> forces_con w G -> forces_con w' G :=
    con_mono []       p q := q ;
    con_mono (t :: G') p q := (con_mono G' p (fst q), ty_mono t p (snd q)).

  Equations member_mono {G t}(v : member t G) : forcing G t :=
    member_mono Here      w (_, q) := q ;
    member_mono (There v) w (p, q) := member_mono v w p.

  Equations term_mono {G t}(e : term G t) : forcing G t :=
    term_mono (Var v)         w p   := member_mono v w p;
    term_mono (Abs e)         w p   := fun _ q r => term_mono e _ (con_mono _ q p, r) ;
    term_mono (App e e')      w p
       := term_mono e w p _ (lt_world_refl w) (term_mono e' w p).
End KRIPKE.
