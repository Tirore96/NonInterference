
(** Process type **)
Parameter Proc : Type -> Type -> Type.

(** Core combinators *)
Parameter map   : forall {I I' O O'}, (I -> I') -> (O -> O') -> Proc I' O -> Proc I O'.
Parameter sta   : forall {I O V}, (I -> V -> V) -> (O -> V -> V) -> V -> Proc (V*I) O -> Proc I (V*O).
Parameter swi   : forall {I O},  bool -> Proc I (bool * O)%type -> Proc (bool * I) (option O).
Parameter par   : forall {I O1 O2}, Proc I O1 -> Proc I O2 -> Proc I (O1 * O2).
Parameter loop  : forall {I}, Proc I I -> Proc I I.
Parameter maybe : forall {I O}, Proc I O -> Proc (option I) O.

(** Derived combinators  *)
Definition mapO {I O O'} (f : O -> O') : Proc I O  -> Proc I O' :=
  map (@id I) f.
Definition swiI {I O : Type} (b : bool) (p : Proc I O) : Proc (bool * I) (option O) :=
  swi b (mapO (fun x => (false,x)) p).

(** Example : Round-Robin Scheduled Processes **)

Inductive Empty : Type := .

Definition unit_to_true_none {T} (u : unit)
  : bool * option T :=
  (true, None).

Definition product_option_to_option_sum {O1 O2} (s : option O1 * option O2)
  : option (O1 + O2) :=
  match s with
  | (Some o1, _) => Some (inl o1)
  | (_, Some o2) => Some (inr o2)
  | (None, None) => None
  end.

Definition round_robin_deaf {O1 O2} (p1 : Proc Empty O1) (p2 : Proc Empty O2)
  : Proc unit ( option (O1 + O2) ) :=
    map unit_to_true_none product_option_to_option_sum (
      par
        (swiI true  (maybe p1))
        (swiI false (maybe p2))
      ).










(* ==========================================================================================*)

(* =HERE=THERE=BE=DRAGONS====================================================================*)

(* ==========================================================================================*)

(* ==========================================================================================*)

(* ==========================================================================================*)

(* ==========================================================================================*)

(* ==========================================================================================*)

(* ==========================================================================================*)

(* ==========================================================================================*)

(* From stdpp Require Import base.*)

(*** Message transformation *)
Definition mapI {I I' O} (f : I -> I') : Proc I' O -> Proc I O := map f (@id O).
Definition mapO {I O O'} (f : O -> O') : Proc I O  -> Proc I O' := map (@id I) f.

(*** Message filtering *)
Definition filter {I O} (f : I -> bool) (g : O -> bool) (p : Proc I O) :
  Proc I (option O) :=
  map
    (fun i => if f i then Some i else None)
    (fun o => if g o then Some o else None) (maybe p).

(* Not derivable from [filter]? *)
Definition filterI {I O : Type} (f : I -> bool) (p : Proc I O) : Proc I O :=
  mapI (fun i => if f i then Some i else None) (maybe p).
Definition filterO {I O : Type} (f : O -> bool) (p : Proc I O) : Proc I (option O) :=
  filter (fun _ => true) f p.

Definition source {I I' O : Type} (p : Proc I O) : Proc I' O :=
  mapI (fun _ => None) (maybe p).

(*** Message tagging: TBD *)

(*** Process state: TBD *)


Definition staI {I O V} (f : I -> V -> V) (v:V) (p:Proc (V*I) O) : Proc I (V*O) :=
  sta f (fun o v => v) v p.
Definition staO {I O V} (f : O -> V -> V) (v:V) (p:Proc (V*I) O) : Proc I (V*O) :=
  sta (fun i v => v) f v p.



(*** Process switching *)

Definition swiI {I O : Type} (b : bool) (p : Proc I O) : Proc (bool * I) (option O) :=
  swi b (mapO (fun x => (false,x)) p).
Definition swiO {I O : Type} (b : bool) (p : Proc I (bool * O)) : Proc I (option O) :=
  mapI (fun x => (false,x)) (swi b p).

Definition par_swiI {I1 I2 O1 O2} (b:bool) (p1 : Proc I1 O1) (p2 : Proc I2 O2)
  : Proc (bool * (I1 * I2)) (option O1 * option O2) :=
    par
    (swiI b (mapI fst p1))
    (swiI (negb b) (mapI snd p2)).

Definition option_unit_to_bool (u : option unit) : bool := 
  match u with
  | None => false
  | Some _ => true
  end.

Definition on_left {L L' R} (f : L -> L') (a : L * R) : L' * R :=
  match a with
  | (l, r) => ( f l, r)
  end.

Definition round_robin {I1 I2 O1 O2} (b:bool) (p1 : Proc I1 O1) (p2 : Proc I2 O2)
  : Proc (bool * (I1 * I2)) (option O1 * option O2) :=

(*** Process composition: TBD *)

(** Personal derived combinators *)

Definition f1 {I1 I2} (i : I1 + I2) : option I1 := 
  match i with
  | inl i1 => Some i1
  | inr _ => None
  end.

Definition f2 {I1 I2} (i : I1 + I2) : option I2 := 
  match i with
  | inl _ => None
  | inr i2 => Some i2
  end.

Definition either {I1 I2 O1 O2} (p1 : Proc I1 O1) (p2 : Proc I2 O2) : Proc (I1 + I2) (O1*O2) :=
  par (mapI f1 $ maybe p1) (mapI f2 $ maybe p2).

Definition to_left {I1 I2 O1 O2} (p1 : Proc I1 O1) (p2 : Proc I2 O2) : Proc I1 (O1*O2) :=
  mapI inl $ either p1 p2.

Definition to_right {I1 I2 O1 O2} (p1 : Proc I1 O1) (p2 : Proc I2 O2) : Proc I2 (O1*O2) :=
  mapI inr $ either p1 p2.

(** Definitions *)

Parameter I1 : Type.
Parameter I2 : Type.

Parameter I1_inhib : Inhabited I1.
Existing Instance I1_inhib.
Parameter I2_inhib : Inhabited I2.
Existing Instance I2_inhib.

Parameter O1 : Type.
Parameter O2 : Type.

Parameter O1_inhabited : Inhabited O1.
Existing Instance O1_inhabited.
Parameter O2_inhabited : Inhabited O2.
Existing Instance O2_inhabited.

Parameter p1 : Proc I1 O1.
Parameter p2 : Proc I2 O2.

Definition option_elim {A} `{Inhabited A} (o : option A) : A :=
  match o with Some a => a | None => inhabitant end.

(* TODO: Make par_swi - Needs [uni] *)
Definition par_swiI {I1 I2 O1 O2} `{Inhabited O1} `{Inhabited O2}
  (b:bool) (p1 : Proc I1 O1) (p2 : Proc I2 O2) : Proc (bool * (I1 * I2)) (O1 + O2) :=
  mapO (if b then inl ∘ option_elim ∘ fst else inr ∘ option_elim ∘ snd) $
    par
    (swiI b $ mapI fst p1)
    (swiI (negb b) $ mapI snd p2).

(*
                 p1 -----o---> p1'
 ----------------------------------------------------
 par_swiI True p1 p2 --inl o--> par_swiI True p1' p2

                 p2 -----o---> p2'
 -----------------------------------------------------
 par_swiI False p1 p2 --inr o--> par_swiI False p1 p2'

          p1 ~~i1~~> p1'   p2 ~~i2~~> p2'
 ---------------------------------------------------------
 par_swiI b p1 p2 ~~(b',i1,i2)~~> par_swiI (b⊕ b') p1' p2'

 *)

(* Process definition. Interference when high input comes in and interferes with scheduling. *)
Definition processes : Proc (bool * (I1 * I2)) (O1 + O2) :=
  par_swiI true p1 p2.

(* Mitigator definition(s). Prevents interference as scheduling is round robin. *)
Definition naive_scheduler {I O} (p : Proc (bool * I) O) : Proc I O :=
  mapI (λ i, (true,i)) $ p.

Definition naive_mitigator : Proc (I1 * I2) (O1 + O2) :=
  naive_scheduler processes.

Definition scheduler {I O} n (p : Proc (bool * I) O) : Proc I O :=
  mapO snd $
    staI (λ _ v, (v.1+1, Nat.eqb (Nat.modulo v.1 n) 0)) (0,inhabitant) $
    mapI (λ (nbi : ((nat * bool) * I)), (nbi.1.2,nbi.2)) $
    p.

Definition mitigator : Proc (I1 * I2) (O1 + O2) :=
  scheduler 10 $ processes.
