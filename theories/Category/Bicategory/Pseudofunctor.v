(** Pseudofunctors between bicategories. The comparison cells are
    invertible; the unit comparison points from the image identity to the
    target identity. No normality or strictness condition is imposed. *)

Set Warnings "-notation-overridden".
From Bonak.Lib Require Import HSet Notation.
From Bonak.Category.Bicategory Require Export Bicategory.
From Stdlib Require Import Logic.FunctionalExtensionality.
Set Primitive Projections.
Set Printing Projections.

Record PsfData (S T: Bicategory) (ob: S.(BObj) -> T.(BObj)) := {
  psHom {a b}: (S.(BHom) a b).(CObj) -> (T.(BHom) (ob a) (ob b)).(CObj);
  psCell {a b} {f g: (S.(BHom) a b).(CObj)}:
    (S.(BHom) a b).(CHom) f g -> (T.(BHom) (ob a) (ob b)).(CHom) (psHom f) (psHom g);
  psUnit a: (T.(BHom) (ob a) (ob a)).(CHom) (psHom (bid a)) (bid (ob a));
  psComp {a b c} (f: (S.(BHom) a b).(CObj)) (g: (S.(BHom) b c).(CObj)):
    (T.(BHom) (ob a) (ob c)).(CHom) (bcomp (psHom f) (psHom g)) (psHom (bcomp f g));
}.
Arguments psHom {S T ob} _ {a b} _.
Arguments psCell {S T ob} _ {a b f g} _.
Arguments psUnit {S T ob} _ _.
Arguments psComp {S T ob} _ {a b c} _ _.

(** Functoriality, naturality, and associativity of the compositor can be
    used independently of the unit comparisons. *)

Definition PsfCellComp {S T: Bicategory} {ob: S.(BObj) -> T.(BObj)}
  (F: PsfData S T ob): Type :=
  forall a b (f g h: (S.(BHom) a b).(CObj))
    (α: (S.(BHom) a b).(CHom) f g) (β: (S.(BHom) a b).(CHom) g h),
    F.(psCell) (α ⨟ β) = F.(psCell) α ⨟ F.(psCell) β.

Definition PsfCompNatL {S T: Bicategory} {ob: S.(BObj) -> T.(BObj)}
  (F: PsfData S T ob): Type :=
  forall a b c (f: (S.(BHom) a b).(CObj)) (g h: (S.(BHom) b c).(CObj))
    (α: (S.(BHom) b c).(CHom) g h),
    bwhiskerL (F.(psHom) f) (F.(psCell) α) ⨟ F.(psComp) f h
    = F.(psComp) f g ⨟ F.(psCell) (bwhiskerL f α).

Definition PsfCompNatR {S T: Bicategory} {ob: S.(BObj) -> T.(BObj)}
  (F: PsfData S T ob): Type :=
  forall a b c (f g: (S.(BHom) a b).(CObj)) (α: (S.(BHom) a b).(CHom) f g)
    (h: (S.(BHom) b c).(CObj)),
    bwhiskerR (F.(psCell) α) (F.(psHom) h) ⨟ F.(psComp) g h
    = F.(psComp) f h ⨟ F.(psCell) (bwhiskerR α h).

Definition PsfAssoc {S T: Bicategory} {ob: S.(BObj) -> T.(BObj)}
  (F: PsfData S T ob): Type :=
  forall a b c d (f: (S.(BHom) a b).(CObj)) (g: (S.(BHom) b c).(CObj))
    (h: (S.(BHom) c d).(CObj)),
    (bwhiskerR (F.(psComp) f g) (F.(psHom) h) ⨟ F.(psComp) (bcomp f g) h)
      ⨟ F.(psCell) (bassoc f g h).(isoHom)
    = (bassoc (F.(psHom) f) (F.(psHom) g) (F.(psHom) h)).(isoHom)
      ⨟ (bwhiskerL (F.(psHom) f) (F.(psComp) g h) ⨟ F.(psComp) f (bcomp g h)).

Record PsfLaws {S T: Bicategory} {ob: S.(BObj) -> T.(BObj)} (F: PsfData S T ob) := {
  psUnitInvertible a: IsInvertible (F.(psUnit) a);
  psCompInvertible a b c (f: (S.(BHom) a b).(CObj)) (g: (S.(BHom) b c).(CObj)):
    IsInvertible (F.(psComp) f g);
  psCellId a b (f: (S.(BHom) a b).(CObj)): F.(psCell) (cid f) = cid (F.(psHom) f);
  psCellComp: PsfCellComp F;
  psCompNatL: PsfCompNatL F;
  psCompNatR: PsfCompNatR F;
  psUnitL a b (f: (S.(BHom) a b).(CObj)):
    F.(psComp) (bid a) f ⨟ F.(psCell) (bunitL f).(isoHom)
    = bwhiskerR (F.(psUnit) a) (F.(psHom) f) ⨟ (bunitL (F.(psHom) f)).(isoHom);
  psUnitR a b (f: (S.(BHom) a b).(CObj)):
    F.(psComp) f (bid b) ⨟ F.(psCell) (bunitR f).(isoHom)
    = bwhiskerL (F.(psHom) f) (F.(psUnit) b) ⨟ (bunitR (F.(psHom) f)).(isoHom);
  psAssoc: PsfAssoc F;
}.

Lemma psfLawsProp {S T ob} {F: PsfData S T ob} (u v: PsfLaws F): u = v.
Proof.
  destruct u as [ui uc u1 u2 ul ur uil uir ua], v as [vi vc v1 v2 vl vr vil vir va].
  assert (ui = vi) by (repeat (apply functional_extensionality_dep; intro); apply isInvertibleProp).
  assert (uc = vc) by (repeat (apply functional_extensionality_dep; intro); apply isInvertibleProp).
  assert (u1 = v1) by (repeat (apply functional_extensionality_dep; intro); apply (T.(BHom) _ _).(CHom)).
  assert (u2 = v2) by (repeat (apply functional_extensionality_dep; intro); apply (T.(BHom) _ _).(CHom)).
  assert (ul = vl) by (repeat (apply functional_extensionality_dep; intro); apply (T.(BHom) _ _).(CHom)).
  assert (ur = vr) by (repeat (apply functional_extensionality_dep; intro); apply (T.(BHom) _ _).(CHom)).
  assert (uil = vil) by (repeat (apply functional_extensionality_dep; intro); apply (T.(BHom) _ _).(CHom)).
  assert (uir = vir) by (repeat (apply functional_extensionality_dep; intro); apply (T.(BHom) _ _).(CHom)).
  assert (ua = va) by (repeat (apply functional_extensionality_dep; intro); apply (T.(BHom) _ _).(CHom)).
  now subst.
Qed.

Record Psf (S T: Bicategory) (ob: S.(BObj) -> T.(BObj)) := {
  psData: PsfData S T ob;
  psLaws: PsfLaws psData;
}.
Arguments psData {S T ob} _.
Arguments psLaws {S T ob} _.
Record Pseudofunctor (S T: Bicategory) := {
  psObj: S.(BObj) -> T.(BObj);
  psStr: Psf S T psObj;
}.
Arguments psObj {S T} _ _.
Arguments psStr {S T} _.

Lemma psfEqData {S T: Bicategory} {ob: S.(BObj) -> T.(BObj)}
  (F G: Psf S T ob) (e: F.(psData) = G.(psData)): F = G.
Proof.
  destruct F as [f fl], G as [g gl]; cbn in e. destruct e.
  now rewrite (psfLawsProp fl gl).
Qed.

