(** Extending a bounded coherent face map by one retained rank. *)
Set Warnings "-notation-overridden".
Set Universe Polymorphism.
From Bonak.Lib Require Import HSet Notation LeSProp NatLemmas RewLemmas Funext.
From Bonak.Presheaf Require Import FaceStructure.
Set Primitive Projections.
Set Printing Projections.
Import Logic.EqNotations.

Local Definition noSelfLt n: n.+1 <= n -> SFalse.
Proof.
  induction n as [|n IH]; intro h.
  - now exact h.
  - now exact (IH h).
Defined.

Local Definition transportFaceMap {A0 A1 B0 B1: Type}
  (p: A1 -> A0) (q: B1 -> B0)
  (u0: A0 -> B0) (u1: A1 -> B1) (v0: A0 -> B0) (v1: A1 -> B1)
  (e0: u0 = v0) (e1: u1 = v1)
  (old: forall x, q (v1 x) = v0 (p x)):
  forall x, q (u1 x) = u0 (p x).
Proof. destruct e0, e1. now exact old. Defined.

Local Lemma transportExchangeSquare {A0 A1 A2 B0 B1 B2: Type}
  (p0 r0: A1 -> A0) (p1 r1: A2 -> A1)
  (q0 s0: B1 -> B0) (q1 s1: B2 -> B1)
  (u0: A0 -> B0) (u1: A1 -> B1) (u2: A2 -> B2)
  (v0: A0 -> B0) (v1: A1 -> B1) (v2: A2 -> B2)
  (e0: u0 = v0) (e1: u1 = v1) (e2: u2 = v2)
  (C: forall x, p0 (p1 x) = r0 (r1 x))
  (D: forall y, q0 (q1 y) = s0 (s1 y))
  (a0: forall x, q0 (v1 x) = v0 (p0 x))
  (a1: forall x, q1 (v2 x) = v1 (p1 x))
  (b0: forall x, s0 (v1 x) = v0 (r0 x))
  (b1: forall x, s1 (v2 x) = v1 (r1 x))
  (oldSquare: forall x,
    (f_equal q0 (a1 x) • a0 (p1 x)) • f_equal v0 (C x) =
      D (v2 x) • (f_equal s0 (b1 x) • b0 (r1 x))):
  forall x,
    (f_equal q0 (transportFaceMap p1 q1 u1 u2 v1 v2 e1 e2 a1 x)
      • transportFaceMap p0 q0 u0 u1 v0 v1 e0 e1 a0 (p1 x))
      • f_equal u0 (C x) =
    D (u2 x)
      • (f_equal s0 (transportFaceMap r1 s1 u1 u2 v1 v2 e1 e2 b1 x)
        • transportFaceMap r0 s0 u0 u1 v0 v1 e0 e1 b0 (r1 x)).
Proof. destruct e0, e1, e2. now exact oldSquare. Defined.

Section Families.
Context {A: HSet} (P Q: FaceStr A) (cP: CohOf P) (cQ: CohOf Q).

Definition CellMaps N: Type := forall n, n.+1 <= N -> P.(S0) n -> Q.(S0) n.
Definition FacePaths {N} (f: CellMaps N): Type :=
  forall n q (Hq: q <= n) a (h: n.+2 <= N) (x: P.(S0) n.+1),
    Q.(SFace) n q Hq a (f n.+1 h x) = f n (↓ h) (P.(SFace) n q Hq a x).
Definition ExchangeSquares {N} (f: CellMaps N) (φ: FacePaths f): Type :=
  forall n q (Hq: q <= n) r (Hr: r <= q) a b (h: n.+3 <= N) (x: P.(S0) n.+2),
    (f_equal (Q.(SFace) n q Hq a) (φ n.+1 r (Hr ↕ ↑ Hq) b h x)
      • φ n q Hq a (↓ h) (P.(SFace) n.+1 r (Hr ↕ ↑ Hq) b x))
      • f_equal (f n (↓ (↓ h))) (cP n q Hq r Hr a b x) =
    cQ n q Hq r Hr a b (f n.+2 h x)
      • (f_equal (Q.(SFace) n r (Hr ↕ Hq) b) (φ n.+1 q.+1 (⇑ Hq) a h x)
        • φ n r (Hr ↕ Hq) b (↓ h) (P.(SFace) n.+1 q.+1 (⇑ Hq) a x)).

Definition TopFace {N} (f: CellMaps N) (t: P.(S0) N -> Q.(S0) N): Type :=
  match N as K return CellMaps K -> (P.(S0) K -> Q.(S0) K) -> Type with
  | 0 => fun _ _ => unit
  | S n => fun f t => forall q (Hq: q <= n) a (x: P.(S0) n.+1),
      Q.(SFace) n q Hq a (t x) = f n leR_refl (P.(SFace) n q Hq a x)
  end f t.

Definition TopExchange {N} (f: CellMaps N) (φ: FacePaths f)
  (t: P.(S0) N -> Q.(S0) N) (tf: TopFace f t): Type :=
  match N as K return forall (f: CellMaps K) (φ: FacePaths f)
    (t: P.(S0) K -> Q.(S0) K), TopFace f t -> Type with
  | 0 => fun _ _ _ _ => unit
  | S 0 => fun _ _ _ _ => unit
  | S (S n) => fun f φ t tf => forall q (Hq: q <= n) r (Hr: r <= q) a b
      (x: P.(S0) n.+2),
      (f_equal (Q.(SFace) n q Hq a) (tf r (Hr ↕ ↑ Hq) b x)
        • φ n q Hq a leR_refl (P.(SFace) n.+1 r (Hr ↕ ↑ Hq) b x))
        • f_equal (f n (↓ leR_refl)) (cP n q Hq r Hr a b x) =
      cQ n q Hq r Hr a b (t x)
        • (f_equal (Q.(SFace) n r (Hr ↕ Hq) b) (tf q.+1 (⇑ Hq) a x)
          • φ n r (Hr ↕ Hq) b leR_refl (P.(SFace) n.+1 q.+1 (⇑ Hq) a x))
  end f φ t tf.

Section Cells.
Context (N: nat) (f: CellMaps N) (t: P.(S0) N -> Q.(S0) N).

Definition extendCell: CellMaps N.+1.
Proof.
  intros n h. destruct (natOrder n N) as [H|e|H].
  - now exact (f n H).
  - destruct e. now exact t.
  - now destruct (noSelfLt N (H ↕ h)).
Defined.

Lemma extendCellBelow n (h: n.+1 <= N): extendCell n (↑ h) = f n h.
Proof.
  unfold extendCell. destruct (natOrder n N) as [H|e|H].
  - now reflexivity.
  - destruct e. now destruct (noSelfLt n h).
  - now destruct (noSelfLt N (H ↕ ↓ h)).
Defined.

Lemma extendCellTop: extendCell N leR_refl = t.
Proof.
  unfold extendCell. destruct (natOrder N N) as [H|e|H].
  - now destruct (noSelfLt N H).
  - replace e with (@eq_refl nat N) by now apply natUIP.
    now reflexivity.
  - now destruct (noSelfLt N H).
Defined.

Lemma extendCellBelowPoint n (h: n.+1 <= N) (x: P.(S0) n):
  extendCell n (↑ h) x = f n h x.
Proof. now exact (f_equal (fun u => u x) (extendCellBelow n h)). Defined.

Lemma extendCellTopPoint (x: P.(S0) N): extendCell N leR_refl x = t x.
Proof. now exact (f_equal (fun u => u x) extendCellTop). Defined.
End Cells.

Section Faces.
Context (N: nat) (f: CellMaps N) (φ: FacePaths f)
  (t: P.(S0) N -> Q.(S0) N) (tf: TopFace f t).

Definition extendFace: FacePaths (extendCell N f t).
Proof.
  intros n q Hq a h. destruct (natOrder n.+1 N) as [H|e|H].
  - exact (transportFaceMap (P.(SFace) n q Hq a) (Q.(SFace) n q Hq a)
      (extendCell N f t n (↑ (↓ H))) (extendCell N f t n.+1 (↑ H))
      (f n (↓ H)) (f n.+1 H)
      (extendCellBelow N f t n (↓ H)) (extendCellBelow N f t n.+1 H)
      (φ n q Hq a H)).
  - destruct e.
    exact (transportFaceMap (P.(SFace) n q Hq a) (Q.(SFace) n q Hq a)
      (extendCell n.+1 f t n (↑ leR_refl)) (extendCell n.+1 f t n.+1 leR_refl)
      (f n leR_refl) t
      (extendCellBelow n.+1 f t n leR_refl) (extendCellTop n.+1 f t)
      (tf q Hq a)).
  - now destruct (noSelfLt N (H ↕ h)).
Defined.

Local Lemma extendFaceBelowData n q (Hq: q <= n) a (h: n.+2 <= N):
  extendFace n q Hq a (↑ h) =
  transportFaceMap (P.(SFace) n q Hq a) (Q.(SFace) n q Hq a)
    (extendCell N f t n (↑ (↓ h))) (extendCell N f t n.+1 (↑ h))
    (f n (↓ h)) (f n.+1 h)
    (extendCellBelow N f t n (↓ h)) (extendCellBelow N f t n.+1 h)
    (φ n q Hq a h).
Proof.
  unfold extendFace. destruct (natOrder n.+1 N) as [H|e|H].
  - now reflexivity.
  - destruct e. now destruct (noSelfLt n.+1 h).
  - now destruct (noSelfLt N (H ↕ ↓ h)).
Defined.

End Faces.

Local Lemma extendFaceTopData n (f: CellMaps n.+1) (φ: FacePaths f)
  (t: P.(S0) n.+1 -> Q.(S0) n.+1) (tf: TopFace f t) q (Hq: q <= n) a:
  extendFace n.+1 f φ t tf n q Hq a leR_refl =
  transportFaceMap (P.(SFace) n q Hq a) (Q.(SFace) n q Hq a)
    (extendCell n.+1 f t n (↑ leR_refl)) (extendCell n.+1 f t n.+1 leR_refl)
    (f n leR_refl) t
    (extendCellBelow n.+1 f t n leR_refl) (extendCellTop n.+1 f t) (tf q Hq a).
Proof.
  unfold extendFace. destruct (natOrder n.+1 n.+1) as [H|e|H].
  - now destruct (noSelfLt n.+1 H).
  - replace e with (@eq_refl nat n.+1) by now apply natUIP.
    now reflexivity.
  - now destruct (noSelfLt n.+1 H).
Defined.

Section Squares.
Context (N: nat) (f: CellMaps N) (φ: FacePaths f) (coh: ExchangeSquares f φ)
  (t: P.(S0) N -> Q.(S0) N) (tf: TopFace f t) (tc: TopExchange f φ t tf).

Definition extendExchange:
  ExchangeSquares (extendCell N f t) (extendFace N f φ t tf).
Proof.
  intros n q Hq r Hr a b h x. destruct (natOrder n.+2 N) as [H|e|H].
  - change h with (↑ H).
    change (↓ (↑ H)) with (↑ (↓ H)).
    rewrite (extendFaceBelowData N f φ t tf n.+1 r (Hr ↕ ↑ Hq) b H),
      (extendFaceBelowData N f φ t tf n q Hq a (↓ H)),
      (extendFaceBelowData N f φ t tf n.+1 q.+1 (⇑ Hq) a H),
      (extendFaceBelowData N f φ t tf n r (Hr ↕ Hq) b (↓ H)).
    exact (transportExchangeSquare
      (P.(SFace) n q Hq a) (P.(SFace) n r (Hr ↕ Hq) b)
      (P.(SFace) n.+1 r (Hr ↕ ↑ Hq) b) (P.(SFace) n.+1 q.+1 (⇑ Hq) a)
      (Q.(SFace) n q Hq a) (Q.(SFace) n r (Hr ↕ Hq) b)
      (Q.(SFace) n.+1 r (Hr ↕ ↑ Hq) b) (Q.(SFace) n.+1 q.+1 (⇑ Hq) a)
      (extendCell N f t n (↑ (↓ (↓ H)))) (extendCell N f t n.+1 (↑ (↓ H)))
      (extendCell N f t n.+2 (↑ H))
      (f n (↓ (↓ H))) (f n.+1 (↓ H)) (f n.+2 H)
      (extendCellBelow N f t n (↓ (↓ H))) (extendCellBelow N f t n.+1 (↓ H))
      (extendCellBelow N f t n.+2 H)
      (cP n q Hq r Hr a b) (cQ n q Hq r Hr a b)
      (φ n q Hq a (↓ H)) (φ n.+1 r (Hr ↕ ↑ Hq) b H)
      (φ n r (Hr ↕ Hq) b (↓ H)) (φ n.+1 q.+1 (⇑ Hq) a H)
      (coh n q Hq r Hr a b H) x).
  - destruct e.
    change h with (@leR_refl n.+3).
    change (↓ (@leR_refl n.+3)) with (↑ (@leR_refl n.+2)).
    rewrite (extendFaceTopData n.+1 f φ t tf r (Hr ↕ ↑ Hq) b),
      (extendFaceBelowData n.+2 f φ t tf n q Hq a leR_refl),
      (extendFaceTopData n.+1 f φ t tf q.+1 (⇑ Hq) a),
      (extendFaceBelowData n.+2 f φ t tf n r (Hr ↕ Hq) b leR_refl).
    exact (transportExchangeSquare
      (P.(SFace) n q Hq a) (P.(SFace) n r (Hr ↕ Hq) b)
      (P.(SFace) n.+1 r (Hr ↕ ↑ Hq) b) (P.(SFace) n.+1 q.+1 (⇑ Hq) a)
      (Q.(SFace) n q Hq a) (Q.(SFace) n r (Hr ↕ Hq) b)
      (Q.(SFace) n.+1 r (Hr ↕ ↑ Hq) b) (Q.(SFace) n.+1 q.+1 (⇑ Hq) a)
      (extendCell n.+2 f t n (↑ (↓ leR_refl)))
      (extendCell n.+2 f t n.+1 (↑ leR_refl)) (extendCell n.+2 f t n.+2 leR_refl)
      (f n (↓ leR_refl)) (f n.+1 leR_refl) t
      (extendCellBelow n.+2 f t n (↓ leR_refl)) (extendCellBelow n.+2 f t n.+1 leR_refl)
      (extendCellTop n.+2 f t)
      (cP n q Hq r Hr a b) (cQ n q Hq r Hr a b)
      (φ n q Hq a leR_refl) (tf r (Hr ↕ ↑ Hq) b)
      (φ n r (Hr ↕ Hq) b leR_refl) (tf q.+1 (⇑ Hq) a)
      (tc q Hq r Hr a b) x).
  - now destruct (noSelfLt N (H ↕ h)).
Defined.
End Squares.

End Families.
