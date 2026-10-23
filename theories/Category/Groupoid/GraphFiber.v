(** Strict fibers of a functor, as a displayed groupoid over its codomain.
    The fiber witness is an equality of objects, with no chosen lifts. *)
Set Warnings "-notation-overridden".
From Bonak.Category.Groupoid Require Export Map.
From Bonak.Category.Groupoid Require Import Section.
From Bonak.Lib Require Import HSet SigT Notation.
Set Primitive Projections.
Set Printing Projections.
Set Universe Polymorphism.

Local Lemma castArrowInv {G: Groupoid} {x x' y y': G.(CObj)}
  (p: x = x') (q: y = y') (f: G.(CHom) x y):
  castArrow q p (ginv f) = ginv (castArrow p q f).
Proof. now destruct p, q. Defined.

Definition graphFiber {C B: HSetGroupoid} (p: Functor C B): Family B.
Proof.
  unshelve refine (@Build_Family B
    (fun b => hsigT (A := C) (fun c => hEq b (p.(fobj) c)))
    (fun b b' a a' => C.(CHom) a.1 a'.1)
    (fun b b' a a' f => castArrow (eq_sym a.2) (eq_sym a'.2) (p.(fhom) f))
    (fun b a => C.(cid) a.1) (fun b b' b'' a a' a'' f g => f ⨟ g)
    (fun b b' a a' f => ginv f)
    (fun b b' a a' f => C.(cidl) f) (fun b b' a a' f => C.(cidr) f)
    (fun b b' b'' b''' a a' a'' a''' f g h => C.(cassoc) f g h)
    (fun b b' a a' f => ginvL f) (fun b b' a a' f => ginvR f) _ _ _).
  - intros b a. cbn beta. rewrite p.(fid). now apply (castArrowId (G := B)).
  - intros b b' b'' a a' a'' f g. cbn beta. rewrite p.(fcomp).
    now apply (castArrowComp (G := B)).
  - intros b b' a a' f. cbn beta. rewrite (functorInv p).
    now apply (castArrowInv (G := B)).
Defined.

Definition graphPoint {C B: HSetGroupoid} (p: Functor C B) (c: C):
  (graphFiber p).(dobj) (p.(fobj) c) := (c; eq_refl).

Definition graphSection {G H: HSetGroupoid} (F: Functor G H):
  Section (graphFiber F) F :=
  @Build_Map G H (unitFamily G) (graphFiber F) F
    (fun x _ => graphPoint F x) (fun x y a b f => f)
    (fun x a => eq_refl) (fun x y z a b c f g => eq_refl)
    (fun x y a b f => eq_refl).

Definition graphUnit {C B: HSetGroupoid} (p: Functor C B): Functor C (total (graphFiber p)) :=
  Build_Functor C (total (graphFiber p))
    (fun c => (p.(fobj) c; graphPoint p c)) (fun x y f => f)
    (fun _ => eq_refl) (fun _ _ _ _ _ => eq_refl).

Definition graphTotal {C B: HSetGroupoid} (p: Functor C B): Functor (total (graphFiber p)) C :=
  Build_Functor (total (graphFiber p)) C (fun a => a.2.1) (fun x y f => f)
    (fun _ => eq_refl) (fun _ _ _ _ _ => eq_refl).

Definition graphUnitProj {C B: HSetGroupoid} (p: Functor C B):
  graphUnit p ⨟ᶠ proj (graphFiber p) ≐ p.
Proof. unshelve econstructor; now intros. Defined.

Definition graphObjectEta {C B: HSetGroupoid} (p: Functor C B)
  (a: total (graphFiber p)): (graphUnit p).(fobj) ((graphTotal p).(fobj) a) = a.
Proof.
  destruct a as [b [c e]]. cbn.
  destruct (eq_sym e).
  now rewrite (@UIP B _ _ e eq_refl).
Defined.
