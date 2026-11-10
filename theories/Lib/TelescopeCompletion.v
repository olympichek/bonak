(** Completing a finite telescope prefix with a chosen family of later data. *)

Set Warnings "-notation-overridden".
From Bonak.Lib Require Import SigT Notation LeSProp Equiv Limit SequentialLimit
  TelescopeLimit RewLemmas.

Set Primitive Projections.
Set Printing Projections.

Definition shiftTelescope (T: Telescope): Telescope := {|
  stage n := T.(stage) (S n);
  datum n := @datum T (S n);
  extend n := @extend T (S n);
  bond n := @bond T (S n);
  head n := @head T (S n);
  bondExtend n := T.(bondExtend) (S n);
  headExtend n := T.(headExtend) (S n);
  extendHead n := T.(extendHead) (S n);
  bondExtendHead n := T.(bondExtendHead) (S n);
|}.

Definition prependSequential {T: Telescope}
  (L: SequentialLimit (shiftTelescope T).(stage)
    (fun n => @bond (shiftTelescope T) n)):
  SequentialLimit T.(stage) (fun n => @bond T n).
Proof.
  exists (fun n => match n with 0 => bond (L.1 0) | S k => L.1 k end).
  intros [|n]; [now reflexivity|now exact (L.2 n)].
Defined.

(** Shifting both the telescope and the remaining height avoids arithmetic
    casts. Every object below the supplied prefix is obtained by bonding. *)
Fixpoint completePrefixChain (n: nat) (T: Telescope)
  (later: forall l (s: T.(stage) l), @datum T l s)
  (s: T.(stage) n): SequentialLimit T.(stage) (fun l => @bond T l) :=
  match n as n return forall (s: T.(stage) n),
      SequentialLimit T.(stage) (fun l => @bond T l) with
  | 0 => fun s => limitToSequential (ana s later)
  | S n => fun s => prependSequential
      (completePrefixChain n (shiftTelescope T) (fun l => later (S l)) s)
  end s.

Lemma completePrefixAt n T later (s: T.(stage) n):
  (completePrefixChain n T later s).1 n = s.
Proof.
  revert T later s; induction n as [|n IH]; intros T later s.
  - now reflexivity.
  - now exact (IH (shiftTelescope T) (fun l => later (S l)) s).
Defined.

(** Starting the chosen continuation one step later gives the same chain,
    including its bonding paths. Naturality of [bondExtend] supplies the
    compatibility square without truncation assumptions on the stages. *)
Section ContinuePrefix.
Context (T: Telescope)
  (later: forall l (s: T.(stage) l), @datum T l s)
  (s: T.(stage) 0).

Fixpoint advanceApprox (l: nat):
  @mkApprox (shiftTelescope T) (extend s (later 0 s))
    (fun l => later (S l)) l = mkApprox s later (S l) :=
  match l with
  | 0 => eq_refl
  | S l => f_equal (fun x => @extend T (S l) x (later (S l) x))
      (advanceApprox l)
  end.

Lemma advanceApproxBond l:
  f_equal (@bond T (S l)) (advanceApprox (S l))
    • T.(bondExtend) (S l) (mkApprox s later (S l))
        (later (S l) (mkApprox s later (S l)))
  = T.(bondExtend) (S l)
      (@mkApprox (shiftTelescope T) (extend s (later 0 s))
        (fun l => later (S l)) l)
      (later (S l) (@mkApprox (shiftTelescope T) (extend s (later 0 s))
        (fun l => later (S l)) l)) • advanceApprox l.
Proof.
  cbn [advanceApprox].
  refine (f_equal (fun p => p • T.(bondExtend) (S l)
    (mkApprox s later (S l)) (later (S l) (mkApprox s later (S l))))
    (f_equal_compose (fun x => @extend T (S l) x (later (S l) x))
      (@bond T (S l)) (advanceApprox l)) • _).
  refine (homotopyNat
    (fun x => @bond T (S l) (@extend T (S l) x (later (S l) x)))
    (fun x => x) (fun x => T.(bondExtend) (S l) x (later (S l) x))
    (advanceApprox l) • _).
  now rewrite f_equal_id.
Defined.

Lemma completePrefixExtendZero:
  completePrefixChain 1 T later (extend s (later 0 s))
    = completePrefixChain 0 T later s.
Proof.
  refine (sequentialLimitEq
    (completePrefixChain 1 T later (extend s (later 0 s)))
    (completePrefixChain 0 T later s)
    (fun l => match l as k return
      (completePrefixChain 1 T later (extend s (later 0 s))).1 k
        = (completePrefixChain 0 T later s).1 k with
     | 0 => T.(bondExtend) 0 s (later 0 s)
     | S l => advanceApprox l
     end) _).
  intros [|l].
  - now reflexivity.
  - now exact (advanceApproxBond l).
Defined.
End ContinuePrefix.

Lemma completePrefixExtend n T later (s: T.(stage) n):
  completePrefixChain (S n) T later (extend s (later n s))
    = completePrefixChain n T later s.
Proof.
  revert T later s; induction n as [|n IH]; intros T later s.
  - now apply completePrefixExtendZero.
  - now exact (f_equal (@prependSequential T)
      (IH (shiftTelescope T) (fun l => later (S l)) s)).
Defined.

(** Restricting a stored prefix preserves its adjacent bonding paths. *)
Fixpoint takeStage (n: nat): forall (T: Telescope) (s: T.(stage) n)
  (m: nat), leR m n -> T.(stage) m.
Proof.
  destruct n as [|n]; intros T s [|m] h.
  - now exact s.
  - now destruct (leR_O_contra h).
  - now exact (@bond T 0 (takeStage n (shiftTelescope T) s 0 leR_O)).
  - now exact (takeStage n (shiftTelescope T) s m (⇓ h)).
Defined.

Lemma takeStageAt n (T: Telescope) (s: T.(stage) n):
  takeStage n T s n leR_refl = s.
Proof.
  revert T s; induction n as [|n IH]; intros T s.
  - now reflexivity.
  - now exact (IH (shiftTelescope T) s).
Defined.

Lemma takeStageBond n (T: Telescope) (s: T.(stage) n)
  m (h: leR (S m) n):
  @bond T m (takeStage n T s (S m) h) = takeStage n T s m (↓ h).
Proof.
  revert T s m h; induction n as [|n IH]; intros T s [|m] h.
  - now destruct (leR_O_contra h).
  - now destruct (leR_O_contra h).
  - now reflexivity.
  - now exact (IH (shiftTelescope T) s m (⇓ h)).
Defined.

Lemma takeStageNaturality n (T: Telescope) (x y: T.(stage) n) (e: x = y)
  m (h: leR (S m) n):
  f_equal (@bond T m) (f_equal (fun s => takeStage n T s (S m) h) e)
    • takeStageBond n T y m h
  = takeStageBond n T x m h
    • f_equal (fun s => takeStage n T s m (↓ h)) e.
Proof.
  destruct e.
  now exact (eq_trans_refl_l _ • eq_sym (eq_trans_refl_r _)).
Defined.

Definition shiftChain {T: Telescope}
  (X: SequentialLimit T.(stage) (fun m => @bond T m)):
  SequentialLimit (shiftTelescope T).(stage) (fun m => @bond (shiftTelescope T) m) :=
  ((fun m => X.1 (S m)); fun m => X.2 (S m)).

Fixpoint takeStageOfChain (n: nat): forall (T: Telescope)
  (X: SequentialLimit T.(stage) (fun m => @bond T m)) m (h: leR m n),
  takeStage n T (X.1 n) m h = X.1 m.
Proof.
  destruct n as [|n]; intros T X [|m] h.
  - now reflexivity.
  - now destruct (leR_O_contra h).
  - now exact (f_equal (@bond T 0)
      (takeStageOfChain n (shiftTelescope T) (shiftChain X) 0 leR_O) • X.2 0).
  - now exact (takeStageOfChain n (shiftTelescope T) (shiftChain X) m (⇓ h)).
Defined.

(** This square retains the actual bonding path supplied by the chain. *)
Lemma takeStageOfChainBond n (T: Telescope)
  (X: SequentialLimit T.(stage) (fun m => @bond T m)) m (h: leR (S m) n):
  f_equal (@bond T m) (takeStageOfChain n T X (S m) h) • X.2 m
  = takeStageBond n T (X.1 n) m h • takeStageOfChain n T X m (↓ h).
Proof.
  revert T X m h; induction n as [|n IH]; intros T X [|m] h.
  - now destruct (leR_O_contra h).
  - now destruct (leR_O_contra h).
  - change (f_equal (@bond T 0)
      (takeStageOfChain n (shiftTelescope T) (shiftChain X) 0 leR_O) • X.2 0
    = eq_refl • (f_equal (@bond T 0)
      (takeStageOfChain n (shiftTelescope T) (shiftChain X) 0 leR_O) • X.2 0)).
    now apply eq_sym, eq_trans_refl_l.
  - now exact (IH (shiftTelescope T) (shiftChain X) m (⇓ h)).
Defined.

Lemma takeStageOfChainAt n (T: Telescope)
  (X: SequentialLimit T.(stage) (fun m => @bond T m)):
  takeStageOfChain n T X n leR_refl = takeStageAt n T (X.1 n).
Proof.
  revert T X; induction n as [|n IH]; intros T X.
  - now reflexivity.
  - now exact (IH (shiftTelescope T) (shiftChain X)).
Defined.

(** A shared later stage determines compatible paths at all earlier stages. *)
Definition takeStageChainPath n (T: Telescope)
  (X Y: SequentialLimit T.(stage) (fun m => @bond T m))
  (e: X.1 n = Y.1 n) m (h: leR m n): X.1 m = Y.1 m :=
  eq_sym (takeStageOfChain n T X m h)
    • (f_equal (fun z => takeStage n T z m h) e • takeStageOfChain n T Y m h).

Lemma takeStageChainPathAt n (T: Telescope)
  (X Y: SequentialLimit T.(stage) (fun m => @bond T m)) (e: X.1 n = Y.1 n):
  takeStageChainPath n T X Y e n leR_refl = e.
Proof.
  unfold takeStageChainPath. rewrite 2 takeStageOfChainAt.
  pose proof (homotopyNat (fun z => takeStage n T z n leR_refl)
    (fun z => z) (takeStageAt n T) e) as h.
  rewrite f_equal_id in h. rewrite h. now apply eq_trans_sym_cancel_l.
Defined.

Local Lemma takeStagePathAlgebra {T: Type} {a b c d e f g h: T}
  (u: a = b) (v: c = d) (p: a = c)
  (l: a = e) (r: c = f) (x: e = g) (y: f = h) (q: e = f)
  (s: b = g) (t: d = h)
  (hs: u • s = l • x) (ht: v • t = r • y) (hp: p • r = l • q):
  (eq_sym u • (p • v)) • t = s • (eq_sym x • (q • y)).
Proof.
  destruct u, v, x, y, l, p, r.
  cbn in hs, ht, hp |- *.
  repeat rewrite eq_trans_refl_l in hs, ht, hp |- *.
  now rewrite hs, ht, <- hp.
Defined.

Lemma takeStageChainPathBond n (T: Telescope)
  (X Y: SequentialLimit T.(stage) (fun m => @bond T m))
  (e: X.1 n = Y.1 n) m (h: leR (S m) n):
  f_equal (@bond T m) (takeStageChainPath n T X Y e (S m) h) • Y.2 m
  = X.2 m • takeStageChainPath n T X Y e m (↓ h).
Proof.
  unfold takeStageChainPath.
  rewrite 2 eq_trans_map_distr, fEqualSym.
  now exact (takeStagePathAlgebra
    (f_equal (@bond T m) (takeStageOfChain n T X (S m) h))
    (f_equal (@bond T m) (takeStageOfChain n T Y (S m) h))
    (f_equal (@bond T m) (f_equal (fun z => takeStage n T z (S m) h) e))
    (takeStageBond n T (X.1 n) m h) (takeStageBond n T (Y.1 n) m h)
    (takeStageOfChain n T X m (↓ h)) (takeStageOfChain n T Y m (↓ h))
    (f_equal (fun z => takeStage n T z m (↓ h)) e)
    (X.2 m) (Y.2 m) (takeStageOfChainBond n T X m h)
    (takeStageOfChainBond n T Y m h) (takeStageNaturality n T _ _ e m h)).
Defined.
