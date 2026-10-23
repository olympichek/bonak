(** Coherent evaluation of a strict groupoid diagram in a diagram of 1-types.
    The components are functors; their naturality cells respect the unit
    paths and composition comparisons of the target diagram. *)
Set Warnings "-notation-overridden".
From Bonak.Lib Require Import HSet Notation RewLemmas.
From Bonak.νGpd Require Import HGpd.
From Bonak.Category.Groupoid Require Import SetBased.
From Bonak.Category.Bicategory Require Import PathDiagram PathGroupoid.
Set Primitive Projections.
Set Printing Projections.
Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Record DiagramEvaluation {C: Category} {D: Functor C HSetGroupoidCat}
  {X: PathDiagramFamily C} := {
  evalFunctor a: Functor (D.(fobj) a) (pathGpd (X.(pfObj) a));
  evalNaturality {a b} (f: C.(CHom) a b):
    NatTrans (D.(fhom) f ⨟ᶠ evalFunctor b)
      (evalFunctor a ⨟ᶠ pathFunctor ((pathData C X.(pfObj) X.(pfStr)).(phom) f));
  evalUnit a (x: D.(fobj) a):
    (evalNaturality (C.(cid) a)).(ncomp) x
      • f_equal (fun k => k ((evalFunctor a).(fobj) x))
          ((pathData C X.(pfObj) X.(pfStr)).(pid) a)
    = f_equal (evalFunctor a).(fobj)
        (f_equal (fun F: Functor (D.(fobj) a) (D.(fobj) a) => F.(fobj) x) (D.(fid) a));
  evalComp {a b c} (f: C.(CHom) a b) (g: C.(CHom) b c) (x: D.(fobj) a):
    f_equal (evalFunctor c).(fobj)
        (f_equal (fun F: Functor (D.(fobj) a) (D.(fobj) c) => F.(fobj) x) (D.(fcomp) f g))
      • ((evalNaturality g).(ncomp) ((D.(fhom) f).(fobj) x)
      • (f_equal ((pathData C X.(pfObj) X.(pfStr)).(phom) g)
          ((evalNaturality f).(ncomp) x)
      • (pathData C X.(pfObj) X.(pfStr)).(pcomp) f g ((evalFunctor a).(fobj) x)))
    = (evalNaturality (f ⨟ g)).(ncomp) x;
}.
Arguments DiagramEvaluation {C} D X.
