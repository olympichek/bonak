(** Pointwise maps and fixed-object changes of coherent diagrams. *)
Set Warnings "-notation-overridden".
Set Universe Polymorphism.
From Bonak.Lib Require Import HSet HGpd Notation RewLemmas.
From Bonak.Category Require Import Category.
From Bonak.Category.Bicategory Require Import HGpdBicat Pseudonatural
  LocallyDiscretePseudofunctor PathDiagramLemmas.
Set Primitive Projections.
Set Printing Projections.

(** Transport along equalities of the diagram structures leaves their
    object families, and hence the component types, fixed. *)
Definition structureTransformation {C: Category} {X Y: C.(CObj) -> HGpd}
  {F0 F1: PathDiagram C X} {G0 G1: PathDiagram C Y}
  (p: F0 = F1) (q: G0 = G1)
  (α: Pseudonatural
    (expandPseudofunctor (@Build_PathDiagramFamily C X F0))
    (expandPseudofunctor (@Build_PathDiagramFamily C Y G0))):
  Pseudonatural
    (expandPseudofunctor (@Build_PathDiagramFamily C X F1))
    (expandPseudofunctor (@Build_PathDiagramFamily C Y G1)).
Proof. now destruct p, q. Defined.

Lemma structureTransformationComponent {C: Category} {X Y: C.(CObj) -> HGpd}
  {F0 F1: PathDiagram C X} {G0 G1: PathDiagram C Y}
  (p: F0 = F1) (q: G0 = G1)
  (α: Pseudonatural
    (expandPseudofunctor (@Build_PathDiagramFamily C X F0))
    (expandPseudofunctor (@Build_PathDiagramFamily C Y G0))) i:
  (structureTransformation p q α).(pnComponent) i = α.(pnComponent) i.
Proof. now destruct p, q. Defined.

Section Pointwise.
Context {C: Category} (X Y: PathDiagramFamily C)
  (α: Pseudonatural (expandPseudofunctor X) (expandPseudofunctor Y)).
Local Abbreviation XD := (pathData _ _ X.(pfStr)).
Local Abbreviation YD := (pathData _ _ Y.(pfStr)).

Lemma pseudonaturalUnitPoint (i: C.(CObj)) (x: X.(pfObj) i):
  f_equal (α.(pnComponent) i) (pidPt XD i x) =
    (α.(pnNaturality) (C.(cid) i)).(isoHom) x
      • pidPt YD i (α.(pnComponent) i x).
Proof.
  pose proof (f_equal (fun h => h x) (α.(pnUnit) i)) as H.
  change (f_equal (α.(pnComponent) i)
      (@idTo2 HGpdBicat (X.(pfObj) i) (X.(pfObj) i) _ _ (XD.(pid) i) x) =
    (α.(pnNaturality) (C.(cid) i)).(isoHom) x
      • @idTo2 HGpdBicat (Y.(pfObj) i) (Y.(pfObj) i) _ _
        (YD.(pid) i) (α.(pnComponent) i x)) in H.
  rewrite 2 idTo2Point in H. now exact H.
Defined.

Lemma pseudonaturalCompPoint {i j k: C.(CObj)}
  (f: C.(CHom) i j) (g: C.(CHom) j k) (x: X.(pfObj) i):
  f_equal (α.(pnComponent) k) (XD.(pcomp) f g x)
    • (α.(pnNaturality) (f ⨟ g)).(isoHom) x =
  (α.(pnNaturality) g).(isoHom) (XD.(phom) f x)
    • (f_equal (YD.(phom) g) ((α.(pnNaturality) f).(isoHom) x)
      • YD.(pcomp) f g (α.(pnComponent) i x)).
Proof.
  pose proof (f_equal (fun h => h x) (α.(pnComp) f g)) as H.
  cbn in H. rewrite 3 eq_trans_refl_l in H. now exact H.
Defined.
End Pointwise.

