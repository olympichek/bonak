(** Face presentations equipped with cubical-style degeneracies. *)

Set Warnings "-notation-overridden".
From Bonak.Lib Require Import HSet Notation LeSProp SigT Funext.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Bonak.Presentation.Set Require Export Presentation.
Set Primitive Projections.
Set Printing Projections.

Record νDgnStructure {arity: HSet} (psh: νSetPresentation arity): Type := {
  Dgn n q (Hq: q <= n): psh.(F0) n -> psh.(F0) n.+1;
  FaceDgnInf n r q (Hr: r <= q) (Hq: q <= n) (ε: arity) (X: psh.(F0) n.+1):
    psh.(Face) n.+1 r (Hr ↕ (↑ Hq)) ε (Dgn n.+1 q.+1 (⇑ Hq) X) =
    Dgn n q Hq (psh.(Face) n r (Hr ↕ Hq) ε X);
  FaceDgnId n q (Hq: q <= n) (ε: arity) (X: psh.(F0) n):
    psh.(Face) n q Hq ε (Dgn n q Hq X) = X;
  FaceDgnSup n q (Hq: q <= n) r (Hr: r <= q) (ε: arity) (X: psh.(F0) n.+1):
    psh.(Face) n.+1 q.+1 (⇑ Hq) ε (Dgn n.+1 r (Hr ↕ (↑ Hq)) X) =
    Dgn n r (Hr ↕ Hq) (psh.(Face) n q Hq ε X);
  DgnDgn n r q (Hr: r <= q) (Hq: q <= n) (X: psh.(F0) n):
    Dgn n.+1 r (Hr ↕ (↑ Hq)) (Dgn n q Hq X) =
    Dgn n.+1 q.+1 (⇑ Hq) (Dgn n r (Hr ↕ Hq) X)
}.

Arguments Build_νDgnStructure {arity} _ _ _ _ _ _.
Arguments Dgn {arity} _ _ _ _ _.
Arguments FaceDgnInf {arity} _ _ _ _ _ _ _ _ _.
Arguments FaceDgnId {arity} _ _ _ _ _ _ _.
Arguments FaceDgnSup {arity} _ _ _ _ _ _ _ _ _.
Arguments DgnDgn {arity} _ _ _ _ _ _ _ _.

Definition νDgnSetPresentation (arity: HSet): Type :=
  { P: νSetPresentation arity &T νDgnStructure P }.

Definition shiftPresheaf {A: HSet} (P: νSetPresentation A): νSetPresentation A := {|
  F0 n := P.(F0) (S n);
  Face n q Hq a := P.(Face) (S n) q (↑ Hq) a;
  FaceCoh n q Hq r Hr a b x := P.(FaceCoh) (S n) q (↑ Hq) r Hr a b x;
|}.

Definition shiftDgn {A: HSet} {P: νSetPresentation A} (R: νDgnStructure P):
  νDgnStructure (shiftPresheaf P) :=
  Build_νDgnStructure (shiftPresheaf P)
    (fun n q Hq => R.(Dgn _) (S n) q (↑ Hq))
    (fun n r q Hr Hq a x => R.(FaceDgnInf _) (S n) r q Hr (↑ Hq) a x)
    (fun n q Hq a x => R.(FaceDgnId _) (S n) q (↑ Hq) a x)
    (fun n q Hq r Hr a x => R.(FaceDgnSup _) (S n) q (↑ Hq) r Hr a x)
    (fun n r q Hr Hq x => R.(DgnDgn _) (S n) r q Hr (↑ Hq) x).

(** The levels, faces and degeneracies determine the complete presentation. *)

Lemma presheafDgnEq {arity: HSet} {psh: νSetPresentation arity} (R S: νDgnStructure psh)
  (e: R.(Dgn _) = S.(Dgn _)): R = S.
Proof.
  destruct R as [d ri rid rs rr], S as [d' si sid ss sr]; cbn in e.
  destruct e.
  f_equal;
    repeat first [apply functional_extensionality_dep_good; intro
                 |apply spropFunext; intro];
    apply (psh.(F0) _).(UIP).
Qed.

Lemma presheafWithDgnEq {arity: HSet} (X Y: νDgnSetPresentation arity)
  (e0: X.1.(F0) = Y.1.(F0))
  (ef: rew [fun F: nat -> HSet =>
         forall n i (Hi: i <= n) (ε: arity), F n.+1 -> F n] e0 in
       X.1.(Face) = Y.1.(Face))
  (ed: rew [fun F: nat -> HSet =>
         forall n i (Hi: i <= n), F n -> F n.+1] e0 in
       X.2.(Dgn _) = Y.2.(Dgn _)): X = Y.
Proof.
  destruct X as [[F f c] R], Y as [[F' f' c'] S]; cbn in e0, ef, ed.
  destruct e0; cbn in ef, ed. destruct ef.
  assert (ec: c = c').
  { repeat first [apply functional_extensionality_dep_good; intro
                 |apply spropFunext; intro].
    apply (F _).(UIP). }
  destruct ec.
  now destruct (presheafDgnEq R S ed).
Qed.
