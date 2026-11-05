(** Sequential limits, their equivalences and dependent decomposition. *)

Set Warnings "-notation-overridden".
From Stdlib Require Import Logic.FunctionalExtensionality.
From Bonak.Lib Require Import SigT Equiv RewLemmas Notation.

Set Primitive Projections.
Set Printing Projections.
Set Universe Polymorphism.

(** A sequential limit consists of one point at each stage and paths
    relating adjacent stages along the restriction maps. *)

Definition SequentialLimit (X: nat -> Type) (r: forall n, X (S n) -> X n): Type :=
  {x: forall n, X n &T forall n, r n (x (S n)) = x n}.

(** Equality of sequential-limit points follows from compatible
    pointwise paths. *)

Lemma sequentialLimitEq {X: nat -> Type} {r: forall n, X (S n) -> X n}
  (c d: SequentialLimit X r) (p: forall n, c.1 n = d.1 n)
  (H: forall n, f_equal (r n) (p (S n)) • d.2 n = c.2 n • p n):
  c = d.
Proof.
  pose (E := functional_extensionality_dep_good c.1 d.1 p).
  assert (HP: forall n, f_equal (fun a: forall n, X n => a n) E = p n).
  { intro n. now apply f_equal__functional_extensionality_dep_good. }
  assert (HS: forall n,
    f_equal (fun a: forall n, X n => r n (a (S n))) E
      = f_equal (r n) (p (S n))).
  { intro n. rewrite <- (f_equal_compose
      (fun a: forall n, X n => a (S n)) (r n) E).
    now rewrite HP. }
  refine (= E; _).
  apply functional_extensionality_dep_good; intro n.
  rewrite <- (@map_subst_app nat (forall n, X n) c.1 d.1 n E
    (fun n (a: forall n, X n) => r n (a (S n)) = a n) c.2).
  rewrite (rew_between
    (fun a: forall n, X n => r n (a (S n)))
    (fun a: forall n, X n => a n)), HS, HP.
  symmetry. now apply eq_trans_shift_l, H.
Defined.

(** A commuting square at every bond transports the coherence paths;
    no truncation assumption on the stages is needed. *)

Definition sequentialLimitEquiv {X Y: nat -> Type}
  (r: forall n, X (S n) -> X n) (s: forall n, Y (S n) -> Y n)
  (e: forall n, Equiv (X n) (Y n))
  (comm: forall n x, e n (r n x) = s n (e (S n) x)):
  Equiv (SequentialLimit X r) (SequentialLimit Y s).
Proof.
  unfold SequentialLimit. refine (sigTEquiv (piEquiv e) _).
  intro x. apply piEquiv; intro n.
  refine (compEquiv (symEquiv (eqvInjEquiv (e n))) _).
  now exact (rewEquiv (fun y: Y n => y = e n (x n)) (comm n (x (S n)))).
Defined.

(** The limit of a dependent family over a fixed base point, with
    compatibility expressed using its base paths. *)

Definition SequentialLimitFiber {X: nat -> Type} (P: forall n, X n -> Type)
  (r: forall n, X (S n) -> X n)
  (s: forall n x, P (S n) x -> P n (r n x)) (cx: SequentialLimit X r): Type :=
  {p: forall n, P n (cx.1 n) &T forall n,
    rew [P n] (cx.2 n) in s n (cx.1 (S n)) (p (S n)) = p n}.

(** Splitting a sequential limit of dependent pairs into a base limit
    and the corresponding fibre limit. *)

Definition sequentialLimitSigmaEquiv {X: nat -> Type} {P: forall n, X n -> Type}
  (r: forall n, X (S n) -> X n)
  (s: forall n x, P (S n) x -> P n (r n x)):
  Equiv (SequentialLimit (fun n => {x: X n &T P n x})
      (fun n z => (r n z.1; s n z.1 z.2)))
    {cx: SequentialLimit X r &T SequentialLimitFiber P r s cx}.
Proof.
  unfold SequentialLimit, SequentialLimitFiber.
  refine (compEquiv (symEquiv (sigTEquivFst
    (B := fun z: forall n, {x: X n &T P n x} =>
      forall n, (r n (z (S n)).1; s n (z (S n)).1 (z (S n)).2) = z n)
    (@sigTPiEquiv nat X P))) _).
  refine (compEquiv (sigTEquivSnd
    (fun z: {x: forall n, X n &T forall n, P n (x n)} => piEquiv
      (fun n => sigTPathEquiv
        (r n (z.1 (S n)); s n (z.1 (S n)) (z.2 (S n)))
        (z.1 n; z.2 n)))) _).
  refine (compEquiv (sigTEquivSnd
    (fun z: {x: forall n, X n &T forall n, P n (x n)} => symEquiv
      (@sigTPiEquiv nat
        (fun n => r n (z.1 (S n)) = z.1 n)
        (fun n p => rew [P n] p in s n (z.1 (S n)) (z.2 (S n)) = z.2 n)))) _).
  now exact (qinvEquiv
    (fun z => ((z.1.1; z.2.1); (z.1.2; z.2.2)))
    (fun z => ((z.1.1; z.2.1); (z.1.2; z.2.2)))
    (fun _ => eq_refl) (fun _ => eq_refl)).
Defined.
