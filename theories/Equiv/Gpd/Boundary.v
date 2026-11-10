(** Homotopy pullback descriptions of the layers of an indexed frame. *)

Set Warnings "-notation-overridden".
From Stdlib Require Import Logic.FunctionalExtensionality.
From Bonak.Lib Require Import SigT HSet HGpd Equiv Notation RewLemmas LeSProp.
From Bonak.νGpd Require Import Layer νGpd.
From Bonak.Equiv.Gpd Require Import Face.

Set Primitive Projections.
Set Printing Projections.
Set Keyed Unification.
Import Logic.EqNotations.

Module BoundaryOn (A: LayerGpdSig) (Core: νGpdSig A)
  (Faces: FaceSig A Core).

(** Paths of indexed frames from their layer components and whole faces. *)
Module Paths.
Import A Faces.

Definition layerDpathEquiv {T: Type} {Bd: T -> arity -> HGpd}
  {x y: T} (p: x = y) (l: Layer (Bd x)) (r: Layer (Bd y)):
  Equiv (rew [fun z => Layer (Bd z)] p in l = r)
    (forall ε, rew [fun z => Bd z ε] p in nth l ε = nth r ε).
Proof.
  refine (qinvEquiv (fun q ε => nth_dpath q ε) layer_dpath_intro _ _).
  - intro q. apply (layer_dpath2_eq (κ := eq_refl)); intro ε.
    now apply nth_dpath_intro.
  - intro h. apply functional_extensionality_dep; intro ε.
    now apply nth_dpath_intro.
Defined.

Definition layerTotalPathEquiv {T: Type} {Bd: T -> arity -> HGpd}
  (x y: {d: T &T Layer (Bd d)}):
  Equiv (x = y) {p: x.1 = y.1 &T
    forall ε, rew [fun d => Bd d ε] p in nth x.2 ε = nth y.2 ε} :=
  compEquiv (sigTPathEquiv x y)
    (sigTEquivSnd (fun p => layerDpathEquiv p x.2 y.2)).

(** The first component of a pair path is retained as part of its data. *)
Definition pairPathOverEquiv {X: Type} {P: X -> Type}
  (u v: {x: X &T P x}) (p: u.1 = v.1):
  Equiv (rew [P] p in u.2 = v.2)
    {q: u = v &T projT1_eq q = p}.
Proof.
  unshelve refine (qinvEquiv
    (fun h => ((= p; h); _))
    (fun q => rew [fun r => rew [P] r in u.2 = v.2] q.2 in projT2_eq q.1)
    _ _).
  - destruct u as [x a], v as [y b]; cbn in *. now destruct h, p.
  - intro h. destruct u as [x a], v as [y b]; cbn in *.
    now destruct h, p.
  - intros [q h]; cbn in h. destruct q; cbn in h. destruct h.
    destruct u; now reflexivity.
Defined.

Section LayerStep.
Context {T: Type} {X: HGpd} {P: X -> HGpd} (r: arity -> T -> X).
Let B d ε := P (r ε d).
Let L := {d: T &T Layer (B d)}.
Definition layerFace (ε: arity) (d: L): {x: X &T P x} :=
  (r ε d.1; nth d.2 ε).

Definition layerFacePath {u v: L} (p: u.1 = v.1)
  (h: forall ε, rew [fun d => B d ε] p in nth u.2 ε = nth v.2 ε):
  u = v := (= p; layer_dpath_intro h).

Lemma layerFacePathComponent {u v: L} (p: u.1 = v.1)
  (h: forall ε, rew [fun d => B d ε] p in nth u.2 ε = nth v.2 ε) ε:
  f_equal (layerFace ε) (layerFacePath p h) =
    (= f_equal (r ε) p;
      sigT_map_eq (Q := P) (fun _ z => z) (h ε)).
Proof.
  unfold layerFace, layerFacePath.
  etransitivity.
  { now exact (f_equal_eq_existT_curried (r ε)
      (fun d (l: Layer (B d)) => nth l ε) p (layer_dpath_intro h)). }
  apply eq_existT_curried_eq with (Hp := eq_refl).
  destruct u as [u l], v as [v l']; cbn in *.
  destruct p; cbn.
  rewrite 2 sigT_map_eq_refl, f_equal_id.
  change (ap_nth (layer_dpath_intro h) ε = h ε).
  unfold layer_dpath_intro. rewrite ap_nth_ext.
  now apply eq_trans_refl_l.
Defined.

Lemma layerFacePathsDetermine {u v: L} (p q: u = v)
  (base: projT1_eq p = projT1_eq q)
  (faces: forall ε, f_equal (layerFace ε) p = f_equal (layerFace ε) q):
  p = q.
Proof.
  apply (eqvInj (layerTotalPathEquiv u v)).
  refine (eq_existT_curried base _).
  apply functional_extensionality_dep; intro ε.
  destruct u as [u l], v as [v l']; cbn in *.
  rewrite (sigT_decompose_eq (p := p)), (sigT_decompose_eq (p := q)) in faces.
  specialize (faces ε).
  unfold layerFace in faces.
  rewrite (f_equal_eq_existT_curried (r ε)
    (fun d (l: Layer (B d)) => nth l ε) (projT1_eq p) (projT2_eq p)),
    (f_equal_eq_existT_curried (r ε)
    (fun d (l: Layer (B d)) => nth l ε) (projT1_eq q) (projT2_eq q)) in faces.
  pose proof (eqvInj (symEquiv (sigTPathEquiv
    (layerFace ε (u; l)) (layerFace ε (v; l')))) faces) as paths.
  clear faces.
  cbn [compEquiv eqvFun sigTEquivSnd qinvEquiv] in *.
  (* The equality between base paths is unique in the groupoid [X]. *)
  generalize (projT2_eq p), (projT2_eq q), paths.
  clear paths. generalize (projT1_eq p), (projT1_eq q), base.
  intros e e' α h h' H. destruct α; cbn in *.
  apply (sigT_map_eq_id_inj (r ε) (fun x => GDom (P x))).
  change (sigT_map_eq (Q := P) (fun _ z => z) (nth_dpath h ε) =
    sigT_map_eq (Q := P) (fun _ z => z) (nth_dpath h' ε)).
  destruct e; cbn in *.
  rewrite 2 sigT_map_eq_refl in H.
  unfold nth_dpath; cbn. rewrite 2 sigT_map_eq_refl, 2 f_equal_id,
    2 eq_trans_refl_l.
  now exact (sigTSecond (A := hpaths (r ε u) (r ε u)) H).
Defined.

End LayerStep.

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

Lemma frameAttachmentBase {p k} (dc: DepsCohs p k)
  (d: mkFrame (mkDepsRestr (depsCohs := dc))):
  (frameAttachmentEquiv dc d).1 = d.1.
Proof. now reflexivity. Defined.

Lemma frameAttachmentFace {p k} (dc: DepsCohs p k)
  (d: mkFrame (mkDepsRestr (depsCohs := dc))) a:
  ((frameAttachmentEquiv dc d).2 a).1 = νFace DepsCohsChainNil a d.
Proof. now reflexivity. Defined.

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

Lemma frameConeStepBase (d: mkFrame (mkDepsRestr (depsCohs := dc))):
  (frameConeStepEquiv d).1 = partial d.1.
Proof. now reflexivity. Defined.

Lemma frameConeStepFace (d: mkFrame (mkDepsRestr (depsCohs := dc))) a:
  ((frameConeStepEquiv d).2 a).1 = cell (νFace DepsCohsChainNil a d).
Proof. now reflexivity. Defined.

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

(** A partial painting is the fibre of projecting a whole cell to its
    partial frame. Reassociation of the cell supplies the comparison. *)
Definition paintingFiberEquiv {P K} {depsTop: DepsRestr P K}
  {extTop: DepsRestrExtension P K depsTop}
  {p k} {deps: DepsRestr p k} {ext: DepsRestrExtension p k deps}
  (c: ExtChain extTop ext) (d: mkFrame deps):
  Equiv (mkPainting ext d)
    {t: Paths.Cell extTop &T d = getFrame (extChainDeps c) t.1} :=
  compEquiv (symEquiv (basePairEquiv (fun d => mkPainting ext d) d))
    (sigTEquiv (Paths.paintingChainEquiv c)
      (fun t => eqTransEquiv (eq_sym (getFrameGetPainting c t.1 t.2)))).

Lemma paintingFiberCell {P K} {depsTop: DepsRestr P K}
  {extTop: DepsRestrExtension P K depsTop}
  {p k} {deps: DepsRestr p k} {ext: DepsRestrExtension p k deps}
  (c: ExtChain extTop ext) (d: mkFrame deps) (t: mkPainting ext d):
  (paintingFiberEquiv c d t).1 = getPainting c d t.
Proof. now reflexivity. Defined.


Section ConePaths.
Context {W B T: Type} (r: arity -> W -> B) (b: T -> B).
Local Definition ConePoint: Type :=
  {w: W &T forall a: arity, {t: T &T r a w = b t}}.

Local Definition coneFiberPath {w} (a: arity)
  (u v: {t: T &T r a w = b t}) (h: u.1 = v.1)
  (s: eq_refl • v.2 = u.2 • f_equal b h): u = v.
Proof.
  destruct u as [t u], v as [t' v]; cbn in h, s.
  refine (eq_existT_curried h _). destruct h.
  change (u = v). change (eq_refl • v = u) in s.
  now exact (eq_sym s • eq_trans_refl_l v).
Defined.

Local Lemma coneFiberPathBase {w} (a: arity)
  (u v: {t: T &T r a w = b t}) (h: u.1 = v.1)
  (s: eq_refl • v.2 = u.2 • f_equal b h):
  projT1_eq (coneFiberPath a u v h s) = h.
Proof. destruct u, v. unfold coneFiberPath. now apply pairPathBase. Defined.

(** Both the point paths and the square relating the attachment paths are
    needed to identify two homotopy-pullback cones. *)
Definition conePath (u v: ConePoint) (p: u.1 = v.1)
  (h: forall a, (u.2 a).1 = (v.2 a).1)
  (s: forall a, f_equal (r a) p • (v.2 a).2 = (u.2 a).2 • f_equal b (h a)):
  u = v.
Proof.
  destruct u as [w u], v as [w' v]; cbn in p, h, s. destruct p.
  now exact (f_equal (fun f => (w; f))
    (functional_extensionality_dep_good u v
      (fun a => coneFiberPath a (u a) (v a) (h a) (s a)))).
Defined.

Lemma conePathBase (u v: ConePoint) (p: u.1 = v.1)
  (h: forall a, (u.2 a).1 = (v.2 a).1)
  (s: forall a, f_equal (r a) p • (v.2 a).2 = (u.2 a).2 • f_equal b (h a)):
  projT1_eq (conePath u v p h s) = p.
Proof.
  destruct u as [w u], v as [w' v]; cbn in p, h, s. destruct p.
  unfold conePath, projT1_eq.
  rewrite f_equal_compose. now apply fEqualConst.
Defined.

Lemma conePathCell (u v: ConePoint) (p: u.1 = v.1)
  (h: forall a, (u.2 a).1 = (v.2 a).1)
  (s: forall a, f_equal (r a) p • (v.2 a).2 = (u.2 a).2 • f_equal b (h a)) a:
  f_equal (fun z: ConePoint => (z.2 a).1) (conePath u v p h s) = h a.
Proof.
  destruct u as [w u], v as [w' v]; cbn in p, h, s. destruct p.
  unfold conePath. rewrite f_equal_compose.
  refine (eq_sym (f_equal_compose (fun f => f a) (@projT1 _ _)
    (functional_extensionality_dep_good u v
      (fun a => coneFiberPath a (u a) (v a) (h a) (s a)))) • _).
  refine (f_equal (fun q => f_equal (@projT1 _ _) q)
    (f_equal__functional_extensionality_dep_good
      (fun a => coneFiberPath a (u a) (v a) (h a) (s a)) a) • _).
  now apply coneFiberPathBase.
Defined.

End ConePaths.



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

Local Lemma homotopyPathExt {X Y: Type} (f g: X -> Y)
  (h: forall x, f x = g x) {x y: X} (p q: x = y)
  (e: f_equal g p = f_equal g q): f_equal f p = f_equal f q.
Proof.
  apply (transCancelR _ _ (h y)).
  rewrite 2 homotopyNat. now rewrite e.
Defined.

Section ConePathExt.
Context {W: Type} {B T: HGpd} (r: arity -> W -> B) (b: T -> B).
Let Fibre (c: B): HGpd := {t: T & gpaths c (b t)}.
Let LayerCone: Type := {w: W &T Layer (fun a => Fibre (r a w))}.

Local Definition coneLayerEquiv: Equiv LayerCone (ConePoint r b) :=
  sigTEquivSnd (fun w => layerProductEquiv (fun a => Fibre (r a w))).

(** After the base and whole-cell paths are fixed, the attachment-square
    proofs are propositions because [B] is a homotopy groupoid. *)
Lemma conePathExt {u v: ConePoint r b} (p q: u = v)
  (base: projT1_eq p = projT1_eq q)
  (cells: forall a, f_equal (fun z: ConePoint r b => (z.2 a).1) p
    = f_equal (fun z: ConePoint r b => (z.2 a).1) q): p = q.
Proof.
  pose (e := symEquiv coneLayerEquiv).
  apply (eqvInj (symEquiv (eqvInjEquiv e))).
  apply (Paths.layerFacePathsDetermine (P := Fibre) r).
  - unfold projT1_eq. rewrite 2 f_equal_compose.
    now exact base.
  - intro a. apply (eqvInj (symEquiv (eqvInjEquiv (fillerEquiv b)))).
    cbn [symEquiv eqvInjEquiv invEq eqvFun eqvIsEquiv qinvEquiv linv].
    repeat rewrite f_equal_compose.
    change (f_equal (fun z: ConePoint r b => (nth (@lam (fun a => Fibre (r a z.1)) z.2) a).1) p
      = f_equal (fun z: ConePoint r b => (nth (@lam (fun a => Fibre (r a z.1)) z.2) a).1) q).
    now exact (homotopyPathExt
      (fun z: ConePoint r b => (nth (@lam (fun a => Fibre (r a z.1)) z.2) a).1)
      (fun z: ConePoint r b => (z.2 a).1)
      (fun z => f_equal (fun t => t.1) (@nth_lam (fun a => Fibre (r a z.1)) z.2 a)) p q (cells a)).
Defined.
End ConePathExt.

Lemma restrCellCohBase {p k} (dc3: DepsCohs3 p k)
  q (Hq: q <= k) r (Hr: r <= q) a b
  (d: mkFrame (mkDepsRestr (depsCohs :=
      (proj1DepsCohs2 (mkDepsCohs2 dc3)).(_depsCohs))).(1))
  (c: (mkPaintings (mkDepsRestr (depsCohs :=
      (proj1DepsCohs2 (mkDepsCohs2 dc3)).(_depsCohs));
      mkExtraDeps (proj1DepsCohs2 (mkDepsCohs2 dc3)).(_extraDepsCohs))).2 d):
  projT1_eq (restrCellCoh dc3 q Hq r Hr a b d c)
    = (mkDepsCohs2 dc3).(_depsCohs).(_cohs).2 q Hq r Hr a b d.
Proof. unfold restrCellCoh. now apply pairPathBase. Defined.

End Attach.

End BoundaryOn.
