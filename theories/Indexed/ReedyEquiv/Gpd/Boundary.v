(** Homotopy pullback descriptions of the layers of an indexed frame. *)

Set Warnings "-notation-overridden".
From Stdlib Require Import Logic.FunctionalExtensionality.
From Bonak.Lib Require Import SigT HSet HGpd Equiv Notation RewLemmas LeSProp.
From Bonak.νGpd Require Import Layer νGpd.
From Bonak.Indexed.ReedyEquiv.Gpd Require Import Face.

Set Primitive Projections.
Set Printing Projections.
Set Keyed Unification.
Import Logic.EqNotations.

Module BoundaryOn (A: LayerGpdSig) (Core: νGpdSig A)
  (Faces: FaceSig A Core).

(** Painting along a chain of projections identifies the corresponding whole cells. *)
Module Paths.
Import A Faces.

Definition Cell {p k} {deps: DepsRestr p k}
  (ext: DepsRestrExtension p k deps): HGpd :=
  {d: mkFrame deps & mkPainting ext d}.

Fixpoint unpackPainting {P K} {depsTop: DepsRestr P K}
  {extTop: DepsRestrExtension P K depsTop}
  {p k} {deps: DepsRestr p k} {ext: DepsRestrExtension p k deps}
  (c: ExtChain extTop ext): Cell extTop -> Cell ext :=
  match c with
  | ExtChainNil => fun x => x
  | ExtChainCons c => fun x =>
      let y := unpackPainting c x in (y.1.1; (y.1.2; y.2))
  end.

Lemma unpackGetPainting {P K} {depsTop: DepsRestr P K}
  {extTop: DepsRestrExtension P K depsTop}
  {p k} {deps: DepsRestr p k} {ext: DepsRestrExtension p k deps}
  (c: ExtChain extTop ext) (x: Cell ext):
  unpackPainting c (getPainting c x.1 x.2) = x.
Proof.
  revert x; induction c as [|p k deps e c IHc]; intro x; cbn; [now reflexivity|].
  now exact (f_equal (fun y: Cell e =>
    ((y.1.1; (y.1.2; y.2)): Cell (AddRestrDep deps e)))
    (IHc ((x.1; x.2.1); x.2.2))).
Defined.

Lemma getUnpackPainting {P K} {depsTop: DepsRestr P K}
  {extTop: DepsRestrExtension P K depsTop}
  {p k} {deps: DepsRestr p k} {ext: DepsRestrExtension p k deps}
  (c: ExtChain extTop ext) (x: Cell extTop):
  getPainting c (unpackPainting c x).1 (unpackPainting c x).2 = x.
Proof.
  induction c; cbn; [now reflexivity|]. now exact IHc.
Defined.

Definition paintingChainEquiv {P K} {depsTop: DepsRestr P K}
  {extTop: DepsRestrExtension P K depsTop}
  {p k} {deps: DepsRestr p k} {ext: DepsRestrExtension p k deps}
  (c: ExtChain extTop ext): Equiv (Cell ext) (Cell extTop) :=
  qinvEquiv (fun x => getPainting c x.1 x.2) (unpackPainting c)
    (unpackGetPainting c) (getUnpackPainting c).

End Paths.

Module Attach.
Import A.
Module Export Indexed := Faces.

Definition layerProductEquiv (E: arity -> HGpd):
  Equiv (Layer E) (forall a, E a).
Proof.
  refine (qinvEquiv (fun l a => nth l a) (fun f => lam f) _ _).
  - intro l. apply ext; intro a. now apply nth_lam.
  - intro f. apply functional_extensionality_dep; intro a. now apply nth_lam.
Defined.

(** A layer can be given by whole cells together with paths identifying
    their bases with the prescribed restrictions. These paths are retained
    as data, and both composites of the equivalence recover them. *)
Definition attachedLayerEquiv {B C: HGpd} (E: C -> HGpd)
  (r: arity -> B -> C):
  Equiv {w: B &T Layer (fun a => E (r a w))}
    {w: B &T forall a, {t: {c: C &T E c} &T r a w = t.1}} :=
  sigTEquivSnd (fun w =>
    compEquiv (layerProductEquiv (fun a => E (r a w)))
      (piEquiv (fun a => symEquiv (basePairEquiv (fun c => E c) (r a w))))).

Definition FrameAttachment {p k} (dc: DepsCohs p k): Type :=
  {w: mkFrame (mkDepsRestr (depsCohs := dc)).(1) &T
    forall a, {t: {d: mkFrame dc.(_deps) &T mkPainting dc.(_extraDeps) d} &T
      mkRestrFrame (depsCohs := dc) 0 leR_O a w = t.1}}.

Definition frameAttachmentEquiv {p k} (dc: DepsCohs p k):
  Equiv (mkFrame (mkDepsRestr (depsCohs := dc))) (FrameAttachment dc) :=
  attachedLayerEquiv (mkPainting dc.(_extraDeps))
    (fun a w => mkRestrFrame (depsCohs := dc) 0 leR_O a w).

(** Changing a cone's three vertex types transports its comparison paths
    through the supplied commuting squares. *)
Local Definition pathEndsEquiv {T: Type} {x y x' y': T}
  (p: x' = x) (q: y = y'): Equiv (x = y) (x' = y').
Proof.
  refine (qinvEquiv (fun r => p • (r • q))
    (fun r => eq_sym p • (r • eq_sym q)) _ _);
    intro r; destruct p, q; now rewrite 2 eq_trans_refl_l.
Defined.

Section ConeStep.
Context {p k} (dc: DepsCohs p k).
Context (W B T: HGpd) (r: arity -> W -> B) (b: T -> B).
Context (partial: Equiv (mkFrame (mkDepsRestr (depsCohs := dc)).(1)) W).
Context (lower: Equiv (mkFrame dc.(_deps)) B).
Context (cell: Equiv {d: mkFrame dc.(_deps) &T mkPainting dc.(_extraDeps) d} T).
Context (restrictionSquare: forall a w,
  r a (partial w) = lower (mkRestrFrame (depsCohs := dc) 0 leR_O a w)).
Context (boundarySquare: forall t, lower t.1 = b (cell t)).

Definition frameConeStepEquiv:
  Equiv (mkFrame (mkDepsRestr (depsCohs := dc)))
    {w: W &T forall a, {t: T &T r a w = b t}} :=
  compEquiv (frameAttachmentEquiv dc)
    (sigTEquiv partial (fun w => piEquiv (fun a =>
      sigTEquiv cell (fun t =>
        compEquiv (symEquiv (eqvInjEquiv lower))
          (pathEndsEquiv (restrictionSquare a w) (boundarySquare t)))))).

Lemma frameConeStepPath (d: mkFrame (mkDepsRestr (depsCohs := dc))) a:
  ((frameConeStepEquiv d).2 a).2 =
    restrictionSquare a d.1 • boundarySquare (νFace DepsCohsChainNil a d).
Proof.
  change (restrictionSquare a d.1 •
      (eq_refl • boundarySquare (νFace DepsCohsChainNil a d)) =
    restrictionSquare a d.1 • boundarySquare (νFace DepsCohsChainNil a d)).
  now rewrite eq_trans_refl_l.
Defined.

End ConeStep.
(** A restriction carries an attached whole face to the corresponding
    face of the restricted frame. Its path is the stored frame coherence,
    together with the component computation of the layer map. *)
Definition restrictionLayerFace {p k} {dc2: DepsCohs2 p k}
  {P' K'} {depsTopN: DepsRestr P' K'}
  {extTopN: DepsRestrExtension P' K' depsTopN}
  (E: ExtChain extTopN (dc2.(_depsCohs)).(_extraDeps))
  (q: nat) (Hq: q <= k) (ε ω: arity)
  (W: mkFrame (mkDepsRestr (depsCohs := mkDepsCohs dc2)).(1)):
  getPainting E
    (mkRestrFrame (depsCohs := dc2.(_depsCohs)) q Hq ε
       (mkRestrFrame (depsCohs := proj1DepsCohs (mkDepsCohs dc2)) 0 leR_O ω
          W.1))
    (mkRestrPainting dc2.(_extraDepsCohs) q Hq ε
       (mkRestrFrame (depsCohs := proj1DepsCohs (mkDepsCohs dc2)) 0 leR_O ω
          W.1)
       (nth W.2 ω)) =
  getPainting E
    (mkRestrFrame (depsCohs := dc2.(_depsCohs)) 0 leR_O ω
       (mkRestrFrame (depsCohs := mkDepsCohs dc2) q Hq ε W).1)
    (nth (mkRestrFrame (depsCohs := mkDepsCohs dc2) q Hq ε W).2 ω).
Proof.
  refine (f_equal (fun z: {d0: mkFrame (dc2.(_depsCohs)).(_deps) &T
      mkPainting (dc2.(_depsCohs)).(_extraDeps) d0} =>
    getPainting E z.1 z.2)
    (eq_existT_curried
      ((mkDepsCohs dc2).(_cohs).2 q Hq 0 leR_O ε ω W.1) _)).
  symmetry. now exact (nth_lmap _ W.2 ω).
Defined.

Local Lemma pairPathBase {X: Type} {P: X -> Type} {x y: X}
  {u: P x} {v: P y} (p: x = y) (q: rew [P] p in u = v):
  projT1_eq (= p; q) = p.
Proof. now destruct q, p. Defined.

Lemma restrictionLayerFaceBase {p k} (dc2: DepsCohs2 p k)
  q (Hq: q <= k) a c
  (w: mkFrame (mkDepsRestr (depsCohs := mkDepsCohs dc2)).(1)):
  projT1_eq (restrictionLayerFace (dc2 := dc2) ExtChainNil q Hq a c w) =
    ((mkDepsCohs dc2).(_cohs).2 q Hq 0 leR_O a c w.1).
Proof.
  unfold restrictionLayerFace.
  cbn [getPainting].
  rewrite f_equal_id. now apply pairPathBase.
Defined.

(** The first attached face carries exactly the stored whole-cell
    exchange, including the component path of the layer map. *)
Lemma restrictionLayerFaceCoh {p k} (dc3: DepsCohs3 p k)
  q (Hq: q <= k) a c d painting:
  restrCellCoh dc3 q Hq 0 leR_O a c d painting =
    restrictionLayerFace (dc2 := dc3.(_depsCohs2)) ExtChainNil q Hq a c
      (d; painting.1).
Proof.
  unfold restrictionLayerFace. cbn [getPainting].
  rewrite f_equal_id. now reflexivity.
Defined.

(** The face of an attachment uses the exchange path of its base and
    the naturality square of its boundary map. *)
Lemma coneFaceAlgebra {T: Type}
  {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9: T}
  (a: x0 = x1) (b: x1 = x2) (k: x2 = x3)
  (h: x0 = x4) (r: x4 = x5) (p: x5 = x3)
  (eta: x0 = x6) (eta': x4 = x7) (z: x6 = x7)
  (d: x6 = x8) (l: x8 = x9) (e: x1 = x9)
  (composition: (a • b) • k = h • (r • p))
  (boundary: a • e = eta • (d • l))
  (naturality: h • eta' = eta • z):
  p • (eq_sym k • ((eq_sym b • e) • eq_sym l))
    = (eq_sym r • eta') • (eq_sym z • d).
Proof.
  destruct a, b, h, r, p, eta, eta', d, l.
  cbn [f_equal] in *.
  repeat rewrite eq_trans_refl_l in composition, boundary, naturality.
  rewrite composition, boundary, <- naturality. now reflexivity.
Defined.

Lemma coneBoundaryAlgebra {T: Type} {x0 x1 x2 x3 x4: T}
  (a: x0 = x1) (b: x1 = x2) (e: x2 = x3)
  (c: x0 = x4) (d: x4 = x3)
  (square: a • b = c • (d • eq_sym e)):
  b • e = (eq_sym a • c) • d.
Proof. now destruct a, b, c, e. Defined.

End Attach.

End BoundaryOn.
