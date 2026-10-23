(** Pseudonatural transformations between bicategory-valued diagrams.
    Their naturality cells are invertible. *)
Set Warnings "-notation-overridden".
From Bonak.Lib Require Import HSet Notation.
From Bonak.Category.Bicategory Require Export Pseudofunctor.
Set Primitive Projections.
Set Universe Polymorphism.

Record Pseudonatural {S T: Bicategory} {F G: Pseudofunctor S T} := {
  pnComponent a: Hom T (F.(psObj) a) (G.(psObj) a);
  pnNaturality {a b} (f: Hom S a b):
    Iso (T.(BHom) (F.(psObj) a) (G.(psObj) b))
      (bcomp ((psfData F).(psHom) f) (pnComponent b))
      (bcomp (pnComponent a) ((psfData G).(psHom) f));
  pnCell {a b} {f g: Hom S a b} (α: Hom2 f g):
    bwhiskerR ((psfData F).(psCell) α) (pnComponent b) ⨟ (pnNaturality g).(isoHom)
    = (pnNaturality f).(isoHom) ⨟ bwhiskerL (pnComponent a) ((psfData G).(psCell) α);
  pnUnit a:
    bwhiskerR ((psfData F).(psUnit) a) (pnComponent a) ⨟ (bunitL (pnComponent a)).(isoHom)
    = (pnNaturality (bid a)).(isoHom)
      ⨟ (bwhiskerL (pnComponent a) ((psfData G).(psUnit) a)
        ⨟ (bunitR (pnComponent a)).(isoHom));
  pnComp {a b c} (f: Hom S a b) (g: Hom S b c):
    bwhiskerR ((psfData F).(psComp) f g) (pnComponent c)
      ⨟ (pnNaturality (bcomp f g)).(isoHom)
    = (bassoc ((psfData F).(psHom) f) ((psfData F).(psHom) g) (pnComponent c)).(isoHom)
      ⨟ (bwhiskerL ((psfData F).(psHom) f) (pnNaturality g).(isoHom)
      ⨟ (inverse (bassoc ((psfData F).(psHom) f) (pnComponent b)
          ((psfData G).(psHom) g)).(isoInvertible)
      ⨟ (bwhiskerR (pnNaturality f).(isoHom) ((psfData G).(psHom) g)
      ⨟ ((bassoc (pnComponent a) ((psfData G).(psHom) f) ((psfData G).(psHom) g)).(isoHom)
      ⨟ bwhiskerL (pnComponent a) ((psfData G).(psComp) f g)))));
}.
Arguments Pseudonatural {_ _} _ _.
