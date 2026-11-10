(** Maps preserving the chosen face exchanges induce pseudonatural maps. *)
Set Warnings "-notation-overridden".
From Bonak.Lib Require Import HSet HGpd SigT Funext Notation RewLemmas LeSProp.
From Bonak.Presheaf Require Import νSemiShape WordAction WordMap.
From Bonak.Presheaf.Gpd Require Import Pseudofunctor Icon Bounded.
From Bonak.Category Require Import Category.
From Bonak.Category.Bicategory Require Import PathDiagramLemmas
  LocallyDiscretePseudofunctor Pseudonatural IconPath PathDiagramTransformation.
Set Primitive Projections.
Set Printing Projections.
Set Universe Polymorphism.

Record PresentationMap {A: HSet} {P Q: νGpdPresentation A} := {
  gMapCell n: P.(G0) n -> Q.(G0) n;
  gMapFace n q (Hq: q <= n) a (x: P.(G0) n.+1):
    Q.(GFace) n q Hq a (gMapCell n.+1 x) = gMapCell n (P.(GFace) n q Hq a x);
  gMapCoh n q (Hq: q <= n) r (Hr: r <= q) a b (x: P.(G0) n.+2):
    (f_equal (Q.(GFace) n q Hq a) (gMapFace n.+1 r (Hr ↕ ↑ Hq) b x)
      • gMapFace n q Hq a (P.(GFace) n.+1 r (Hr ↕ ↑ Hq) b x))
      • f_equal (gMapCell n) (P.(GFaceCoh) n q Hq r Hr a b x) =
    Q.(GFaceCoh) n q Hq r Hr a b (gMapCell n.+2 x)
      • (f_equal (Q.(GFace) n r (Hr ↕ Hq) b) (gMapFace n.+1 q.+1 (⇑ Hq) a x)
        • gMapFace n r (Hr ↕ Hq) b (P.(GFace) n.+1 q.+1 (⇑ Hq) a x));
}.
Arguments PresentationMap {A} P Q.

Local Lemma reverseUnit {T: Type} {x y z: T}
  (h: x = y) (p: y = z) (q: x = z) (e: h • p = q): p = eq_sym h • q.
Proof. destruct h; cbn in e |- *. now exact (eq_sym (eq_trans_refl_l p) • e • eq_sym (eq_trans_refl_l q)). Defined.

Local Lemma reverseComp {T: Type} {x y z a b: T}
  (q: x = y) (h: y = z) (u: x = a) (v: a = b) (p: b = z)
  (e: q • h = u • (v • p)):
  p • eq_sym h = eq_sym v • (eq_sym u • q).
Proof.
  destruct h, u, v. cbn in e |- *.
  rewrite 2 eq_trans_refl_l in e.
  now exact (eq_sym e • eq_sym (eq_trans_refl_l q) • eq_sym (eq_trans_refl_l (eq_refl • q))).
Defined.

Section Generated.
Context {A: HSet} {P Q: νGpdPresentation A} (F: PresentationMap P Q).

Definition mapWord {m n} (w: Word A n m) (x: P.(G0) m):
  F.(gMapCell) n (applyW m w (gpdStr P) x) =
    applyW m w (gpdStr Q) (F.(gMapCell) m x) :=
  eq_sym (applyWMap m n w (gpdStr P) (gpdStr Q) F.(gMapCell) F.(gMapFace) x).

Lemma mapWordUnit n (x: P.(G0) n):
  f_equal (F.(gMapCell) n) (pidPt (toPsfOn A P) n x) =
    mapWord (wid n) x • pidPt (toPsfOn A Q) n (F.(gMapCell) n x).
Proof.
  change (f_equal (F.(gMapCell) n) (happly (toPsfPid A P n) x) =
    mapWord (wid n) x • happly (toPsfPid A Q n) (F.(gMapCell) n x)).
  rewrite 2 toPsfPidComp. apply reverseUnit.
  now exact (applyWMapId n (gpdStr P) (gpdStr Q) F.(gMapCell) F.(gMapFace) x).
Defined.

Lemma mapWordComp {p m n} (g: Word A m p) (f: Word A n m) (x: P.(G0) p):
  f_equal (F.(gMapCell) n) (pshGpdComp P g f x) • mapWord (wcomp g f) x =
    mapWord f (applyW p g (gpdStr P) x) •
      (f_equal (applyW m f (gpdStr Q)) (mapWord g x)
        • pshGpdComp Q g f (F.(gMapCell) p x)).
Proof.
  unfold mapWord. rewrite fEqualSym. apply reverseComp.
  now exact (applyWMapComp p m n g f (gpdStr P) (gpdStr Q)
    F.(gMapCell) F.(gMapFace) P.(GFaceCoh) Q.(GFaceCoh) F.(gMapCoh) x).
Defined.

Definition generatedTransformation:
  Pseudonatural (expandPseudofunctor (toPsfTot A P))
    (expandPseudofunctor (toPsfTot A Q)) :=
  pathDiagramTransformation (toPsfTot A P) (toPsfTot A Q) F.(gMapCell)
    (fun p n w x => mapWord w x) mapWordUnit
    (fun p m n g f x => mapWordComp g f x).

End Generated.

(** Maps need only be supplied at the ranks retained by the bound. *)
Section BoundedMaps.
Context {A: HSet} (B: nat -> SProp) (down: forall n, B n.+1 -> B n)
  (P Q: νGpdPresentation A)
  (T: forall n, B n -> P.(G0) n -> Q.(G0) n)
  (Hface: forall n q (Hq: q <= n) a (h: B n.+1) (x: P.(G0) n.+1),
    Q.(GFace) n q Hq a (T n.+1 h x) = T n (down n h) (P.(GFace) n q Hq a x))
  (Hcoh: forall n q (Hq: q <= n) r (Hr: r <= q) a b
    (h: B n.+2) (x: P.(G0) n.+2),
    (f_equal (Q.(GFace) n q Hq a) (Hface n.+1 r (Hr ↕ ↑ Hq) b h x)
      • Hface n q Hq a (down n.+1 h) (P.(GFace) n.+1 r (Hr ↕ ↑ Hq) b x))
      • f_equal (T n (down n (down n.+1 h))) (P.(GFaceCoh) n q Hq r Hr a b x) =
    Q.(GFaceCoh) n q Hq r Hr a b (T n.+2 h x)
      • (f_equal (Q.(GFace) n r (Hr ↕ Hq) b) (Hface n.+1 q.+1 (⇑ Hq) a h x)
        • Hface n r (Hr ↕ Hq) b (down n.+1 h) (P.(GFace) n.+1 q.+1 (⇑ Hq) a x))).

Definition boundMapCell n (z: boundCell B P n): boundCell B Q n :=
  (z.1; T n (unbox z.1) z.2).

Lemma boundMapPathProject {n} {x y: boundCell B P n} (p: x = y):
  f_equal (fun z: boundCell B Q n => z.2) (f_equal (boundMapCell n) p) =
    f_equal (T n (unbox x.1)) (f_equal (fun z: boundCell B P n => z.2) p).
Proof. now destruct p. Defined.

Definition boundMapFace n q (Hq: q <= n) a (z: boundCell B P n.+1):
  boundFace B down Q n q Hq a (boundMapCell n.+1 z) =
    boundMapCell n (boundFace B down P n q Hq a z) :=
  f_equal (boundInclude B Q n (down n (unbox z.1)))
    (Hface n q Hq a (unbox z.1) z.2).

Lemma boundMapFaceProject n q (Hq: q <= n) a (z: boundCell B P n.+1):
  f_equal (fun z: boundCell B Q n => z.2) (boundMapFace n q Hq a z) =
    Hface n q Hq a (unbox z.1) z.2.
Proof.
  exact (f_equal_compose (boundInclude B Q n (down n (unbox z.1)))
    (fun z: boundCell B Q n => z.2) (Hface n q Hq a (unbox z.1) z.2)
    • f_equal_id (Hface n q Hq a (unbox z.1) z.2)).
Defined.

Lemma boundMapCoh n q (Hq: q <= n) r (Hr: r <= q) a b
  (z: boundCell B P n.+2):
  (f_equal (boundFace B down Q n q Hq a) (boundMapFace n.+1 r (Hr ↕ ↑ Hq) b z)
    • boundMapFace n q Hq a (boundFace B down P n.+1 r (Hr ↕ ↑ Hq) b z))
    • f_equal (boundMapCell n) (boundFaceCoh B down P n q Hq r Hr a b z) =
  boundFaceCoh B down Q n q Hq r Hr a b (boundMapCell n.+2 z)
    • (f_equal (boundFace B down Q n r (Hr ↕ Hq) b)
        (boundMapFace n.+1 q.+1 (⇑ Hq) a z)
      • boundMapFace n r (Hr ↕ Hq) b (boundFace B down P n.+1 q.+1 (⇑ Hq) a z)).
Proof.
  apply (boundPathInjective B Q (k := n)).
  rewrite 4 eq_trans_map_distr, 2 boundFacePathProject.
  refine (f_equal2 (fun p q => p • q)
    (f_equal2 (fun p q => p • q)
      (f_equal (fun p => f_equal (Q.(GFace) n q Hq a) p)
        (boundMapFaceProject n.+1 r (Hr ↕ ↑ Hq) b z))
      (boundMapFaceProject n q Hq a (boundFace B down P n.+1 r (Hr ↕ ↑ Hq) b z)))
    (boundMapPathProject (boundFaceCoh B down P n q Hq r Hr a b z)
      • f_equal (fun p => f_equal (T n (down n (down n.+1 (unbox z.1)))) p)
        (boundFaceCohProject B down P n q Hq r Hr a b z)) • _).
  refine (Hcoh n q Hq r Hr a b (unbox z.1) z.2 • _).
  exact (eq_sym (f_equal2 (fun p q => p • q)
    (boundFaceCohProject B down Q n q Hq r Hr a b (boundMapCell n.+2 z))
    (f_equal2 (fun p q => p • q)
      (f_equal (fun p => f_equal (Q.(GFace) n r (Hr ↕ Hq) b) p)
        (boundMapFaceProject n.+1 q.+1 (⇑ Hq) a z))
      (boundMapFaceProject n r (Hr ↕ Hq) b (boundFace B down P n.+1 q.+1 (⇑ Hq) a z))))).
Defined.

Definition boundPresentationMap:
  PresentationMap (boundPresentation B down P) (boundPresentation B down Q) :=
  @Build_PresentationMap A (boundPresentation B down P) (boundPresentation B down Q)
    boundMapCell boundMapFace boundMapCoh.

End BoundedMaps.

