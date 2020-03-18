Require Import
        Syntax.Syntax
        Syntax.OPE
        Syntax.Sub
        Normalization.Normalization
        Normalization.NormalForm.

(** definition of the Kripke model *)

Reserved Notation "w '||-'" (at level 40, no associativity).
Reserved Infix "<<"  (at level 40, no associativity).

Class kripke (world : Type) : Type
  := {
      lt_world : world -> world -> Type 
      where "w1 '<<' w2" := (lt_world w1 w2) ;

      lt_world_refl : forall w, w << w ;
      lt_world_trans : forall w1 w2 w3, w1 << w2 ->
                                   w2 << w3 ->
                                   w1 << w3 ;
      forces : world -> Type
      where "w '||-'" := (forces w) ;

       forces_lt_mono : forall w w',
           w << w' -> w ||- -> w' ||- 
     }.

Declare Scope kripke_scope.
Bind Scope kripke_scope with kripke.
Delimit Scope kripke_scope with kripke. 

Notation "w << w1" := (lt_world w w1)(at level 40, no associativity).
Notation "w ||-"   := (forces w)(at level 40, no associativity).

Equations forces_ty {W}`{kripke W}(w : W)(t : ty) : Type :=
  forces_ty w Base        := forces w ;
  forces_ty w (t1 ==> t2) := forall w', w << w' -> forces_ty w' t1 -> forces_ty w' t2.

Equations forces_con {W}`{kripke W}(w : W)(G : con) : Type :=
  forces_con w []       := unit ;
  forces_con w (t :: G)  := forces_con w G * forces_ty w t.

Definition forcing {W}`{kripke W} G t :=
  forall (w : W), forces_con w G -> forces_ty w t.

