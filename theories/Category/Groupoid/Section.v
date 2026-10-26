(** Displayed sections over a functor and their total functors. *)
Set Warnings "-notation-overridden".
From Bonak.Category.Groupoid Require Export Map.
From Bonak.Lib Require Import HSet SigT Notation.
Set Primitive Projections.
Set Printing Projections.
Set Universe Polymorphism.

Definition unitFamily (G: HSetGroupoid): Family G := {|
  dobj _ := hunit;
  dhom x y _ _ := G.(CHom) x y;
  dbase x y a b f := f;
  did x _ := cid x;
  dcomp x y z a b c := @ccomp G x y z;
  dinv x y a b := @ginv G x y;
  didl x y a b := @cidl G x y;
  didr x y a b := @cidr G x y;
  dassoc w x y z a b c d := @cassoc G w x y z;
  dinvL x y a b := @ginvL G x y;
  dinvR x y a b := @ginvR G x y;
  dbaseId x a := eq_refl;
  dbaseComp x y z a b c f g := eq_refl;
  dbaseInv x y a b f := eq_refl;
|}.

Definition Section {G H: HSetGroupoid} (E: Family H) (F: Functor G H) :=
  Map (unitFamily G) E F.

Definition sectionTotal {G H: HSetGroupoid} {E: Family H} {F: Functor G H}
  (s: Section E F): Functor G (total E) :=
  {| fobj := fun x => (F.(fobj) x; s.(mobj) x tt);
     fhom := fun x y f => s.(mhom) (a := tt) (b := tt) f;
     fid := fun x => s.(mid) tt;
     fcomp := fun x y z f g => s.(mcomp) (a := tt) (b := tt) (c := tt) f g |}.

Definition sectionProj {G H: HSetGroupoid} {E: Family H} {F: Functor G H}
  (s: Section E F): sectionTotal s ⨟ᶠ proj E ≐ F.
Proof.
  unshelve econstructor; [now intros|]. intros x y f.
  now apply s.(mbase).
Defined.

Definition unitMap {G H: HSetGroupoid} (F: Functor G H):
  Map (unitFamily G) (unitFamily H) F :=
  Build_Map (fun _ _ => tt)
    (fun x y a b f => F.(fhom) f) (fun x a => F.(fid) x)
    (fun x y z a b c f g => F.(fcomp) f g)
    (fun x y a b f => eq_refl).

Definition sectionPrecompose {G H K: HSetGroupoid} {E: Family K}
  (F: Functor G H) {R: Functor H K} (s: Section E R): Section E (F ⨟ᶠ R) :=
  compMap (unitMap F) s.

Definition sectionSigma {G H: HSetGroupoid} {E: Family H} {F: Functor G H}
  (s: Section E F) {P: Family (total E)} (t: Section P (sectionTotal s)):
  Section (sigma E P) F.
Proof.
  refine (Build_Map (fun x _ => (s.(mobj) x tt; t.(mobj) x tt))
    (fun x y a b f => t.(mhom) (a := tt) (b := tt) f)
    (fun x a => t.(mid) tt)
    (fun x y z a b c f g => t.(mcomp) (a := tt) (b := tt) (c := tt) f g) _).
  intros x y a b f.
  change (E.(dbase) (P.(dbase) (t.(mhom) (a := tt) (b := tt) f)) = F.(fhom) f).
  rewrite t.(mbase). now apply s.(mbase).
Defined.

Lemma sectionPrecomposeTotal {G H K: HSetGroupoid} {E: Family K}
  (F: Functor G H) {R: Functor H K} (s: Section E R):
  sectionTotal (sectionPrecompose F s) ≐ F ⨟ᶠ sectionTotal s.
Proof. unshelve econstructor; now intros. Defined.

Lemma sectionSigmaTotal {G H: HSetGroupoid} {E: Family H} {F: Functor G H}
  (s: Section E F) {P: Family (total E)} (t: Section P (sectionTotal s)):
  sectionTotal (sectionSigma s t) ≐ sectionTotal t ⨟ᶠ totalUnassoc E P.
Proof. unshelve econstructor; now intros. Defined.

Definition unitSection (G: HSetGroupoid): Functor G (total (unitFamily G)) :=
  {| fobj := fun x => (x; tt);
     fhom := fun x y f => f;
     fid := fun x => eq_refl;
     fcomp := fun x y z f g => eq_refl |}.

Lemma sectionTotalMap {G H: HSetGroupoid} {E: Family H} {F: Functor G H}
  (s: Section E F): sectionTotal s ≐ unitSection G ⨟ᶠ totalMap s.
Proof. unshelve econstructor; now intros. Defined.

Lemma sectionCastTotal {G H: HSetGroupoid} {E: Family H} {F L: Functor G H}
  (e: F ≐ L) (s: Section E F): sectionTotal (castBase e s) ≐ sectionTotal s.
Proof.
  refine (sectionTotalMap _ •ᶠ _).
  refine (feqWhiskerL (unitSection G) (castBaseTotal e s) •ᶠ _).
  now apply feqSym, sectionTotalMap.
Defined.

Lemma sectionIntoPullTotal {G H K: HSetGroupoid} {E: Family K}
  (F: Functor G H) (R: Functor H K) (s: Section E (F ⨟ᶠ R)):
  sectionTotal (intoPull F R s) ⨟ᶠ reindexTotal E R ≐ sectionTotal s.
Proof. unshelve econstructor; now intros. Defined.

Lemma sectionSigmaFst {G H: HSetGroupoid} {E: Family H} {F: Functor G H}
  (s: Section E F) {P: Family (total E)} (t: Section P (sectionTotal s)):
  sectionTotal (sectionSigma s t) ⨟ᶠ totalMap (sigmaFst E P) ≐ sectionTotal s.
Proof.
  unshelve econstructor; [now intros|]. intros x y f.
  now exact (t.(mbase) (a := tt) (b := tt) f).
Defined.

Lemma sectionSigmaMap {G H K: HSetGroupoid} {E: Family H} {P: Family K}
  {F: Functor G H} {R: Functor H K} (s: Section E F)
  {Q: Family (total E)} (t: Section Q (sectionTotal s))
  (m: Map E P R) {U: Family (total P)} (n: Map Q U (totalMap m)):
  sectionTotal (sectionSigma s t) ⨟ᶠ totalMap (sigmaMap m n) ≐
  (sectionTotal t ⨟ᶠ totalMap n) ⨟ᶠ totalUnassoc P U.
Proof. unshelve econstructor; now intros. Defined.

Lemma sectionSigmaAssoc {G H: HSetGroupoid} {E: Family H} {F: Functor G H}
  (s: Section E F) {P: Family (total E)} (t: Section P (sectionTotal s)):
  sectionTotal (sectionSigma s t) ⨟ᶠ totalAssoc E P ≐ sectionTotal t.
Proof. unshelve econstructor; now intros. Defined.
