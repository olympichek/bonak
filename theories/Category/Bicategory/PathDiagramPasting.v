(** Composition diagrams of arrows, evaluated by a path diagram.
    Equalities between parallel arrows form propositions, so the source
    pasting equation is independent of the chosen equality witnesses. *)

Set Warnings "-notation-overridden".
From Bonak.Lib Require Import HSet Notation RewLemmas.
From Bonak.νGpd Require Import HGpd.
From Bonak.Category.Bicategory Require Export PathDiagramLemmas.
From Bonak.Category.Bicategory Require Import PseudofunctorPasting
  LocallyDiscretePseudofunctor LocallyDiscrete HGpd2Cat.

Set Primitive Projections.
Set Printing Projections.

Lemma pcompPaste {C: Category} {ob: C.(CObj) -> HGpd}
  (F: PathDiagramData C ob) (PA: PathDiagramAssocPt F) {a b c d}
  (f: C.(CHom) a b) (g: C.(CHom) b c) (h: C.(CHom) c d)
  {u: C.(CHom) a c} {v: C.(CHom) b d} {w: C.(CHom) a d}
  (α: f ⨟ g = u) (β: g ⨟ h = v) (γ: u ⨟ h = w) (δ: f ⨟ v = w)
  (x: ob a):
  f_equal (F.(phom) h) (F.(pcomp) f g x • phomEq F α x)
    • (F.(pcomp) u h x • phomEq F γ x)
  = (F.(pcomp) g h (F.(phom) f x) • phomEq F β (F.(phom) f x))
      • (F.(pcomp) f v x • phomEq F δ x).
Proof.
  pose proof (psCompPaste (expandData C ob F)
    (expandCellComp C ob F) (expandCompNatL C ob F) (expandCompNatR C ob F)
    (expandAssoc C ob F (pathDiagramAssocOfPt F PA))
    f g h α β γ δ ((C.(CHom) a d).(UIP))) as E.
  exact (f_equal (fun α => α x) E • eq_trans_refl_l _).
Qed.
