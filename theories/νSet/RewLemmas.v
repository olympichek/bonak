(** A few rewriting lemmas not in the standard library *)

Import Logic.EqNotations.

Set Warnings "-notation-overridden".
From Bonak Require Import HSet Notation.

Lemma rew_permute_ll_hset: forall (A: Type) (P Q: A -> HSet) (x y: A)
  (H: forall z: A, P z = Q z) (H': x = y) (a: P x),
  rew [Dom] H y in rew [P] H' in a = rew [Q] H' in rew [Dom] H x in a.
Proof.
  now destruct H'.
Defined.

Lemma rew_swap: forall A (P: A -> Type) a b (H: a = b) (x: P a) (y: P b),
  x = rew <- H in y <-> rew H in x = y.
Proof.
  intros. split; now destruct H.
Defined.

Lemma rew_app_rl A (P: A -> Type) (x y: A) (H H': x = y) (a: P x) :
  H = H' -> rew <- [P] H in rew [P] H' in a = a.
Proof.
  intros * ->. now destruct H'.
Defined.

Lemma rew_map_eq_l {A B: Type} (f: A -> B) {x y: A} (H: x = y)
  {z: B} (p: f x = z):
  rew [fun a: A => f a = z] H in p =
  rew [fun b: B => b = z] (f_equal f H) in p.
Proof.
  exact (rew_map (fun b => b = z) f H p).
Defined.

Lemma map_subst_app {A B} {x y} {𝛉: A} (H: x = y :> B) (P: A -> B -> Type)
  (f: forall 𝛉, P 𝛉 x):
  rew [P 𝛉] H in f 𝛉 = (rew [fun x => forall 𝛉, P 𝛉 x] H in f) 𝛉.
Proof.
  now destruct H.
Defined.

(** Transport in an equality type whose left-hand side is itself a transport of
    a fixed [C1] along the index, and whose right-hand side is fixed.  This is
    the cancellation used by [mkCoh2Painting]: the outer
    [rew [Endpoint] coh2Frame] motive has exactly this shape (with the index
    being a *path* [fe : a = b] and the inner transport in some fibre [B]), so
    rewriting with it turns the outer transport into
    [f_equal (fun fe => rew [B] fe in C1) coh2Frame] — the very factor produced
    by [mkCohLayer], which then cancels. *)
Lemma rew_eq_dep_l {A: Type} {B: A -> Type} {a b: A} {C1: B a} {C2: B b}
  {p1 p2: a = b} (e: p1 = p2) (q: rew [B] p1 in C1 = C2):
  rew [fun fe: a = b => rew [B] fe in C1 = C2] e in q =
  eq_sym (f_equal (fun fe: a = b => rew [B] fe in C1) e) • q.
Proof.
  now destruct e, q.
Defined.
