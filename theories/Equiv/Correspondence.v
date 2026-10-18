(** The correspondence theorem

    The top-level result: the two presentations of augmented semi-simplicial sets — the fibred one
    ([SSSetPresentation]) and the indexed one ([SSSets]) — are equivalent, and, upgraded
    by univalence, equal.

    This file is a thin wrapper on top of the two round trips:
    - [gf: PresheafEquiv (g (f psh)) psh] from [PresheafRoundtrip.v]
    - [fg: SSSetsEquiv (f (g X)) X] from [SSSetRoundtrip.v]
    It combines them into an [Equiv] between the type of presheaves and the
    type of SSSets. Each side's notion of sameness is turned into an equality
    by a theorem assuming univalence and functional extensionality:
    [presheafEquivEq] from [PresheafEquiv.v] on the fibred side,
    [SSSetsEquivEq] from [SSSetEquiv.v] on the indexed side. *)

Set Warnings "-notation-overridden".
From Bonak.Lib Require Import HSet Notation Univalence Limit Equiv.
From Bonak.SSSet Require Import SSSet.
From Bonak.Presheaf Require Import Presentation.
From Bonak.Equiv Require Import Face PresheafEquiv SSSetOfPresheaf PresheafOfSSSet
  SSSetRoundtrip PresheafRoundtrip.

Set Primitive Projections.
Set Printing Projections.
Set Keyed Unification.

Module Correspondence.

Module Export PresheafRoundtrip := Bonak.Equiv.PresheafRoundtrip.PresheafRoundtrip.

(** The two round trips give inverse maps after converting their
    levelwise equivalences to equalities by univalence and functional
    extensionality. *)

Definition presheafSSSetsEquiv: Equiv SSSetPresentation SSSets :=
  qinvEquiv f g
    (fun psh => presheafEquivEq (gf psh))
    (fun X => SSSetsEquivEq (fg X)).

Definition presheafEqSSSets: SSSetPresentation = SSSets := ua presheafSSSetsEquiv.

End Correspondence.
