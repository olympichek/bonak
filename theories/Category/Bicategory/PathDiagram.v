(** Diagrams from a category into h-groupoids, with unit comparisons
    expressed as paths.

    The arrow action and composition comparison are accompanied by unit
    paths and the three coherence laws. The object family is kept as a
    parameter, so icons compare diagrams without transporting their objects. *)

Set Warnings "-notation-overridden".
From Bonak.Lib Require Import HSet Notation.
From Bonak.Category Require Import Category.
From Bonak.νGpd Require Import HGpd.
From Bonak.Category.Bicategory Require Import HGpd2Cat.

Set Primitive Projections.
Set Printing Projections.

Section PathDiagram.
Context (C: Category) (ob: C.(CObj) -> HGpd2Cat.(BObj)).

Record PathDiagramData := {
  phom {a b} (f: C.(CHom) a b): (Hom HGpd2Cat) (ob a) (ob b);
  pid a: phom (C.(cid) a) = id1 (ob a);
  pcomp {a b c} (f: C.(CHom) a b) (g: C.(CHom) b c):
    Hom2 (phom f ⨟₁ phom g) (phom (f ⨟ g));
}.

Arguments phom _ {a b} f.
Arguments pcomp _ {a b c} f g.

Definition psfUnitL (F: PathDiagramData) {a b} (f: C.(CHom) a b):
  (F.(phom) (C.(cid) a)) ⨟₁ F.(phom) f = F.(phom) f :=
  f_equal (fun u => u ⨟₁ F.(phom) f) (F.(pid) a)
  • hgpdUnitL (F.(phom) f).

Definition psfUnitR (F: PathDiagramData) {a b} (f: C.(CHom) a b):
  F.(phom) f ⨟₁ (F.(phom) (C.(cid) b)) = F.(phom) f :=
  f_equal (comp1 (F.(phom) f)) (F.(pid) b) • hgpdUnitR (F.(phom) f).

(** The unit and associativity coherence laws. *)

Definition PathDiagramUnitL (F: PathDiagramData): Type :=
  forall a b (f: C.(CHom) a b),
    F.(pcomp) (C.(cid) a) f
    = hom2Rew (B := HGpd2Cat) (eq_sym (psfUnitL F f))
        (eq_sym (f_equal (F.(phom) (a := a) (b := b)) (C.(cidl) f)))
        (id2 (F.(phom) f)).

Definition PathDiagramUnitR (F: PathDiagramData): Type :=
  forall a b (f: C.(CHom) a b),
    F.(pcomp) f (C.(cid) b)
    = hom2Rew (B := HGpd2Cat) (eq_sym (psfUnitR F f))
        (eq_sym (f_equal (F.(phom) (a := a) (b := b)) (C.(cidr) f)))
        (id2 (F.(phom) f)).

Definition PathDiagramAssoc (F: PathDiagramData): Type :=
  forall a b c d (f: C.(CHom) a b) (g: C.(CHom) b c) (h: C.(CHom) c d),
    (F.(pcomp) f g ▷ F.(phom) h) ⨟₂ (F.(pcomp) (f ⨟ g) h)
    = hom2Rew (B := HGpd2Cat)
        (eq_sym (hgpdAssoc (F.(phom) f) (F.(phom) g) (F.(phom) h)))
        (eq_sym (f_equal (F.(phom) (a := a) (b := d)) (C.(cassoc) f g h)))
        ((F.(phom) f ◁ F.(pcomp) g h) ⨟₂ (F.(pcomp) f (g ⨟ h))).

Record PathDiagram := {
  pathData: PathDiagramData;
  pathUnitL: PathDiagramUnitL pathData;
  pathUnitR: PathDiagramUnitR pathData;
  pathAssoc: PathDiagramAssoc pathData;
}.

(** Icons compare diagrams sharing an object part. Their
    components are invertible 2-cells. The two axioms require compatibility
    with the compositors and with the identity laws. *)

Record Icon (F G: PathDiagramData) := {
  icCell {a b} (f: C.(CHom) a b): Hom2 (F.(phom) f) (G.(phom) f);
  icComp {a b c} (f: C.(CHom) a b) (g: C.(CHom) b c):
    ((icCell f ▷ F.(phom) g) ⨟₂ (G.(phom) f ◁ icCell g)) ⨟₂ G.(pcomp) f g
    = F.(pcomp) f g ⨟₂ (icCell (f ⨟ g));
  icId a:
    hom2Rew (B := HGpd2Cat) (F.(pid) a) (G.(pid) a) (icCell (C.(cid) a)) = id2 (id1 (ob a));
}.

End PathDiagram.

(** A diagram together with its family of objects. *)

Record PathDiagramFamily (C: Category) := {
  pfObj: C.(CObj) -> HGpd2Cat.(BObj);
  pfStr: PathDiagram C pfObj;
}.

Arguments pfObj {C} _ _.
Arguments pfStr {C} _.
Arguments phom {C ob} _ {a b} f.
Arguments pid {C ob} _ a.
Arguments pcomp {C ob} _ {a b c} f g.
Arguments Icon {C ob} F G.
Arguments icCell {C ob F G} _ {a b} f.
