(** A pseudofunctor preserves composition diagrams with specified 2-cells.
    The source and target associators account for the two bracketings. *)

Set Warnings "-notation-overridden".
From Bonak.Lib Require Import HSet.
From Bonak.Category.Bicategory Require Export Pseudofunctor.
Set Keyed Unification.

Section PseudofunctorPasting.
Context {S T: Bicategory} {ob: S.(BObj) -> T.(BObj)} (F: PsfData S T ob).
Context (cellComp: PsfCellComp F) (compNatL: PsfCompNatL F)
        (compNatR: PsfCompNatR F) (compAssoc: PsfAssoc F).
Local Abbreviation Fh := (psHom F).
Local Abbreviation Fc := (psCell F).
Local Abbreviation Fm := (psComp F).

Definition psCompareComp {a b c} (f: Hom S a b) (g: Hom S b c)
  {u: Hom S a c} (α: Hom2 (bcomp f g) u): Hom2 (Fh f ⨟₁ Fh g) (Fh u) :=
  Fm f g ⨟ Fc α.

Lemma psCompPaste {a b c d}
  (f: Hom S a b) (g: Hom S b c) (h: Hom S c d)
  {u: Hom S a c} {v: Hom S b d} {w: Hom S a d}
  (α: Hom2 (bcomp f g) u) (β: Hom2 (bcomp g h) v)
  (γ: Hom2 (u ⨟₁ h) w) (δ: Hom2 (f ⨟₁ v) w)
  (E: (α ▷ h) ⨟ γ = (bassoc f g h).(isoHom) ⨟ ((f ◁ β) ⨟ δ)):
  (psCompareComp f g α ▷ Fh h) ⨟ psCompareComp u h γ
  = (bassoc (Fh f) (Fh g) (Fh h)).(isoHom)
      ⨟ ((Fh f ◁ psCompareComp g h β) ⨟ psCompareComp f v δ).
Proof.
  unfold psCompareComp, whiskerL, whiskerR, comp1 in *.
  rewrite T.(bwhiskerRComp).
  rewrite !cassoc.
  rewrite <- (cassoc (T.(BHom) (ob a) (ob d)) (bwhiskerR (Fc α) (Fh h)) (Fm u h) (Fc γ)).
  rewrite compNatR.
  rewrite !cassoc, <- cellComp, E.
  rewrite !cellComp.
  rewrite <- !cassoc.
  rewrite compAssoc.
  rewrite !cassoc.
  rewrite <- (cassoc (T.(BHom) (ob a) (ob d)) (Fm f (bcomp g h)) (Fc (bwhiskerL f β)) (Fc δ)).
  rewrite <- compNatL.
  rewrite T.(bwhiskerLComp), !cassoc.
  reflexivity.
Qed.
End PseudofunctorPasting.
