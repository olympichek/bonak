(** Maps preserving the chosen face exchanges induce pseudonatural maps. *)
Set Warnings "-notation-overridden".
From Bonak.Lib Require Import HSet HGpd SigT Funext Notation RewLemmas LeSProp.
From Bonak.Presheaf Require Import νSemiShape WordAction WordMap.
From Bonak.Presheaf.Gpd Require Import Pseudofunctor Icon.
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
