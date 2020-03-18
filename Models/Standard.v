Require Import
        Syntax.Syntax.

From Equations Require Import Equations.

(** type interpretation in the standard model *)

Equations sem_ty (t : ty) : Type :=
  sem_ty Base       := False ;
  sem_ty (t ==> t') := sem_ty t -> sem_ty t'.

(** semantics of contexts *)

Equations sem_con (G : con) : Type :=
  sem_con []       := unit ;
  sem_con (t :: G') := prodT (sem_ty t) (sem_con G').
 
(** semantics of membership proofs *)

Equations sem_member {G t}(v : member t G) : (sem_con G -> sem_ty t) :=
  sem_member Here      E := fst E ;
  sem_member (There v) E := sem_member v (snd E).

(** semantics of terms *)

Equations sem_term {G t}(e : term G t) : sem_con G -> sem_ty t :=
  sem_term (Var v) => sem_member v ; 
  sem_term (Abs e) => fun E => fun v => sem_term e (v, E) ;
  sem_term (App e e') => fun E => sem_term e E (sem_term e' E). 

(** consistency *)

Definition consistency : term [] Base -> False :=
  fun (e : term [] Base) => sem_term e tt.

