(** Selecting composable segments at given depths along a chain of projections. *)
Set Warnings "-notation-overridden".
From Bonak.Lib Require Import SigT Notation LeSProp.
From Bonak.Presheaf Require Import GeneratingFaces.
Set Universe Polymorphism.
Set Primitive Projections.
Set Printing Projections.

(** Projecting a stage changes the two indices from [(S P, K)] to
    [(P, S K)]. Chain length counts these projections. *)
Record ChainSystem := {
  stage: nat -> nat -> Type;
  drop {P K}: stage (S P) K -> stage P (S K);
  chain {P K}: stage P K -> forall {p k}, stage p k -> Type;
  nil {P K} (x: stage P K): chain x x;
  step {P K} (x: stage (S P) K): chain x (drop x);
  join {P K} {x: stage P K} {p k} {y: stage p k} {l m} {z: stage l m}:
    chain x y -> chain y z -> chain x z;
  len {P K} {x: stage P K} {p k} {y: stage p k}: chain x y -> nat;
  lenNil P K (x: stage P K): len (nil x) = 0;
  lenStep P K (x: stage (S P) K): len (step x) = 1;
  lenJoin P K (x: stage P K) p k (y: stage p k) l m (z: stage l m)
    (a: chain x y) (b: chain y z): len (join a b) = len a + len b;
}.

Section ChainDepth.
Context (Syst: ChainSystem).
Local Abbreviation D := Syst.(stage).
Local Definition Segment {P K} (x: D P K) :=
  {p: nat &T {k: nat &T {y: D p k &T Syst.(chain) x y}}}.
Local Definition prepend {P K} (x: D (S P) K) (s: Segment (Syst.(drop) x)): Segment x :=
  (s.1; (s.2.1; (s.2.2.1; Syst.(join) (Syst.(step) x) s.2.2.2))).

Local Lemma lenPrepend {P K} (x: D (S P) K) (s: Segment (Syst.(drop) x)):
  Syst.(len) (prepend x s).2.2.2 = S (Syst.(len) s.2.2.2).
Proof. unfold prepend; cbn. now rewrite lenJoin, lenStep. Defined.

Fixpoint chainAtDepth P: forall K (x: D P K) (i: FaceDepth P),
  {s: Segment x &T Syst.(len) s.2.2.2 = depth i}.
Proof.
  destruct P as [|P]; intros K x [[|i] hi].
  - now exact ((0; (K; (x; Syst.(nil) x))); Syst.(lenNil) 0 K x).
  - now destruct (leR_O_contra hi).
  - now exact ((S P; (K; (x; Syst.(nil) x))); Syst.(lenNil) (S P) K x).
  - pose (s := chainAtDepth P (S K) (Syst.(drop) x) {| depth := i; depthBound := ⇓ hi |}).
    now exact (prepend x s.1; lenPrepend x s.1 • f_equal S s.2).
Defined.

(** The first segment ends at [i]. Composing it with the second
    reaches [j], including when either segment is empty. *)
Fixpoint pairAtDepth P: forall K (x: D P K) (i j: FaceDepth P), depth i <= depth j ->
  {s: {a: Segment x &T Segment a.2.2.1} &T
    ((Syst.(len) s.1.2.2.2 = depth i) *
     (Syst.(len) (Syst.(join) s.1.2.2.2 s.2.2.2.2) = depth j))%type}.
Proof.
  destruct P as [|P]; intros K x [[|i] hi] [[|j] hj] hij;
    try (destruct (leR_O_contra hi)); try (destruct (leR_O_contra hj));
    try (destruct (leR_O_contra hij)).
  - exists ((0; (K; (x; Syst.(nil) x))); (0; (K; (x; Syst.(nil) x)))).
    cbn. now rewrite lenJoin, lenNil; split.
  - exists ((S P; (K; (x; Syst.(nil) x))); (S P; (K; (x; Syst.(nil) x)))).
    cbn. now rewrite lenJoin, lenNil; split.
  - pose (s := chainAtDepth (S P) K x {| depth := S j; depthBound := hj |}).
    exists ((S P; (K; (x; Syst.(nil) x))); s.1). cbn.
    rewrite lenJoin, lenNil. now split; [reflexivity | exact s.2].
  - pose (s := pairAtDepth P (S K) (Syst.(drop) x) {| depth := i; depthBound := ⇓ hi |}
      {| depth := j; depthBound := ⇓ hj |} (⇓ hij)).
    exists (prepend x s.1.1; s.1.2). split.
    + now exact (lenPrepend x s.1.1 • f_equal S (fst s.2)).
    + change (Syst.(len) (Syst.(join) (prepend x s.1.1).2.2.2 s.1.2.2.2.2) = S j).
      rewrite lenJoin, lenPrepend. apply (f_equal S).
      rewrite <- lenJoin. now exact (snd s.2).
Defined.
End ChainDepth.

