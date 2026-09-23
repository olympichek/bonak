(** Contracting fibres through an equivalence of total spaces.

    A comparison of frame maps identifies the graph fibre over a translated
    frame with the source filler fibre. The contraction and its projection
    laws remain transparent so that they compute at identity paths. *)

Set Warnings "-notation-overridden".
From Bonak Require Import SigT RewLemmas HSet Notation νGpd.HGpd.
From Bonak.Lib Require Import Equiv.
From Bonak.Equiv.Gpd Require Import PathAlgebra.
Import Logic.EqNotations.

Set Primitive Projections.
Set Keyed Unification.

(** The identification [HF] presents cells as a total space. [FRT]
    compares their candidate-frame map with the frame equivalence [tr].
    The fibre equivalence is assembled from the equivalence combinators
    of [Lib/Equiv.v]. *)

Definition fillerEquivOf {FrB FrA CellH: HGpd} (tr: Equiv FrB FrA)
  {E: FrB -> HGpd} (HF: CellH = {D: FrB & E D})
  (pshF: CellH -> FrA)
  (FRT: forall (D: FrB) (c: E D),
    pshF (rew [GDom] (eq_sym HF) in ((D; c): ({D0: FrB & E D0}: HGpd)))
      = tr D)
  (D: FrB):
  Equiv {cell: CellH &T tr D = pshF cell} (E D) :=
  compEquiv
    (sigTEquivSnd (fun cell =>
      eqTransMapEquiv pshF (rewSymCancel (P := GDom) HF cell)))
  (compEquiv
    (sigTEquivFst (rewEquivD GDom HF))
  (compEquiv
    (sigTEquivSnd (fun t => eqTransEquiv (FRT t.1 t.2)))
  (compEquiv
    (sigTEquivSnd (fun t => eqvInjEquiv tr))
    (basePairEquiv (fun D0: FrB => GDom (E D0)) D)))).

(** The inverse fibre equivalence, paired with [tr], sends the source
    cell to its candidate frame and tautological filler. Its first
    component retains the cell by conversion, so the comparison is the
    contraction of the candidate-frame map's graph. *)

Lemma fillerEquivOfWhole {FrB FrA CellH: HGpd} (tr: Equiv FrB FrA)
  {E: FrB -> HGpd} (HF: CellH = {D: FrB & E D})
  (pshF: CellH -> FrA)
  (FRT: forall (D: FrB) (c: E D),
    pshF (rew [GDom] (eq_sym HF) in ((D; c): ({D0: FrB & E D0}: HGpd)))
      = tr D)
  (D: FrB) (c: E D):
  ((pshF (rew [GDom] (eq_sym HF) in ((D; c): ({D0: FrB & E D0}: HGpd)));
    (rew [GDom] (eq_sym HF) in ((D; c): ({D0: FrB & E D0}: HGpd)); eq_refl))
   : {D0: FrA &T {cell: CellH &T D0 = pshF cell}})
  = (tr D; symEquiv (fillerEquivOf tr HF pshF FRT D) c).
Proof.
  now exact (graphContract pshF
    ((tr D; symEquiv (fillerEquivOf tr HF pshF FRT D) c)
     : {D0: FrA &T {cell: CellH &T D0 = pshF cell}})).
Defined.

(** A comparison stated on cells can be evaluated on a frame and a
    filler using the total-space identification [HF]. *)

Definition frtOfCellRule {FrB FrA CellH: HGpd} (tr: Equiv FrB FrA)
  {E: FrB -> HGpd} (HF: CellH = {D: FrB & E D}) (pshF: CellH -> FrA)
  (G: forall u: CellH, pshF u = tr (rew [GDom] HF in u).1)
  (D: FrB) (c: E D):
  pshF (rew [GDom] (eq_sym HF) in ((D; c): ({D0: FrB & E D0}: HGpd))) = tr D :=
  G (rew [GDom] (eq_sym HF) in ((D; c): ({D0: FrB & E D0}: HGpd)))
  • f_equal tr (f_equal (fun w: {D0: FrB &T E D0} => w.1)
      (rewSymCancelR (P := GDom) HF ((D; c): ({D0: FrB & E D0}: HGpd)))).

(** The fibre component of [fillerEquivOfWhole], expressed over the
    frame comparison used to construct the equivalence.

    [eqIndL] eliminates the cell identification, whose variable is on the
    left. Transparent cancellations reduce at [eq_refl], leaving the
    unit law. *)

Lemma fillerEquivOfTopEntry0 {FrB FrA: HGpd} (tr: Equiv FrB FrA)
  {E: FrB -> HGpd} (pshF: ({D: FrB & E D}: HGpd) -> FrA)
  (G: forall u: ({D: FrB & E D}: HGpd),
     pshF u
     = tr (rew [GDom] (eq_refl: ({D: FrB & E D}: HGpd) = {D: FrB & E D})
             in u).1)
  (u: ({D: FrB & E D}: HGpd)):
  rew [fun D0: FrA => {cell: ({D: FrB & E D}: HGpd) &T D0 = pshF cell}] (G u) in
    ((u; eq_refl): {cell: ({D: FrB & E D}: HGpd) &T pshF u = pshF cell})
  = symEquiv (fillerEquivOf tr eq_refl pshF (frtOfCellRule tr eq_refl pshF G)
      (rew [GDom] eq_refl in u).1) ((rew [GDom] eq_refl in u).2).
Proof.
  unfold frtOfCellRule.
  cbn.
  rewrite eq_trans_refl_l.
  now exact (rewFibrePair (G u)).
Defined.

Lemma fillerEquivOfTopEntry {FrB FrA CellH: HGpd} (tr: Equiv FrB FrA)
  {E: FrB -> HGpd} (HF: CellH = {D: FrB & E D}) (pshF: CellH -> FrA)
  (G: forall u: CellH, pshF u = tr (rew [GDom] HF in u).1)
  (u: CellH):
  rew [fun D0: FrA => {cell: CellH &T D0 = pshF cell}] (G u) in
    ((u; eq_refl): {cell: CellH &T pshF u = pshF cell})
  = symEquiv (fillerEquivOf tr HF pshF (frtOfCellRule tr HF pshF G)
      (rew [GDom] HF in u).1) ((rew [GDom] HF in u).2).
Proof.
  now exact (eqIndL (fun C0 (HF0: C0 = ({D: FrB & E D}: HGpd)) =>
    forall (pshF0: C0 -> FrA)
      (G0: forall u0: C0, pshF0 u0 = tr (rew [GDom] HF0 in u0).1) (u0: C0),
    rew [fun D0: FrA => {cell: C0 &T D0 = pshF0 cell}] (G0 u0) in
      ((u0; eq_refl): {cell: C0 &T pshF0 u0 = pshF0 cell})
    = symEquiv (fillerEquivOf tr HF0 pshF0 (frtOfCellRule tr HF0 pshF0 G0)
        (rew [GDom] HF0 in u0).1) ((rew [GDom] HF0 in u0).2))
    (fun pshF0 G0 u0 => fillerEquivOfTopEntry0 tr pshF0 G0 u0) HF pshF G u).
Defined.
