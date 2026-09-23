(** Equality theory for groupoid-valued presheaves.

    Unlike the set-valued case, compatibility of the carrier equivalences
    with face maps does not determine the chosen exchange paths.  The
    relation below therefore also carries equality of [GFaceCoh] after the
    carrier and face fields have been transported.  No further field is
    needed: [GFaceCoh2] is an equality between paths in an [HGpd], and [GUIP]
    makes proofs of that equality unique. *)

Import Logic.EqNotations.

Set Warnings "-notation-overridden".
From Stdlib Require Import Logic.FunctionalExtensionality.
From Bonak Require Import SigT RewLemmas HSet LeSProp Notation Funext Univalence
  νGpd.HGpd νGpd.HGpdEq νGpd.Layer Presheaf.Gpd.Presentation.
From Bonak.Lib Require Import Equiv.

From Bonak.Equiv.Gpd Require Import PathAlgebra.

Set Primitive Projections.
From Bonak Require Import νGpd.Pasting.

Set Keyed Unification.

Module PresheafEquiv (A: LayerGpdSig).
Import A.

Definition FaceType (F0: nat -> HGpd): Type :=
  forall n q (Hq: q <= n) (ε: arity), F0 n.+1 -> F0 n.

Definition FaceCohType (F0: nat -> HGpd) (Face: FaceType F0): Type :=
  forall n q (Hq: q <= n) r (Hr: r <= q) (ε ω: arity) (X: F0 n.+2),
    Face n q Hq ε (Face n.+1 r (Hr ↕ (↑ Hq)) ω X) =
    Face n r (Hr ↕ Hq) ω (Face n.+1 q.+1 (⇑ Hq) ε X).

Definition rewFaceCoh
  {d1 d2: {F0: nat -> HGpd &T FaceType F0}} (e: d1 = d2)
  (c: FaceCohType d1.1 d1.2): FaceCohType d2.1 d2.2 :=
  match e with eq_refl => c end.

Lemma rew_face_app {F01 F02: nat -> HGpd} (e: F01 = F02)
  (h: forall n q (Hq: q <= n) (ε: arity), F01 n.+1 -> F01 n)
  n q (Hq: q <= n) (ε: arity) (Y: F02 n.+1):
  (rew [FaceType] e in h) n q Hq ε Y =
  rew [fun F0: nat -> HGpd => (F0 n).(GDom)] e in
    h n q Hq ε
      (rew [fun F0: nat -> HGpd => (F0 n.+1).(GDom)] (eq_sym e) in Y).
Proof.
  now destruct e.
Defined.

Lemma funExtBetaHGpd {F01 F02: nat -> HGpd} (H: forall n, F01 n = F02 n)
  (m: nat):
  f_equal (fun h: nat -> HGpd => h m)
    (functional_extensionality_dep_good F01 F02 H) = H m.
Proof.
  now exact (f_equal__functional_extensionality_dep_good H m).
Qed.

(** Functional extensionality out of a strict proposition, with its
    computation rule.

    [spropFunext] proves the same statement but is opaque, and the
    [GFaceCoh] transport below needs the pointwise action of the paths it
    builds.  The construction is the boxing argument of [Funext.v], written
    as a term: the boxed function space is an ordinary one, so the stdlib
    computation rule applies to it and transfers along [f_equal]. *)

Definition boxFun {S: SProp} {T: S -> Type} (w: forall s, T s) (b: sBox S):
  T (unbox b) :=
  match b as b0 return T (unbox b0) with sbox s => w s end.

Definition spropFunextD {S: SProp} {T: S -> Type} {u v: forall s, T s}
  (h: forall s, u s = v s): u = v :=
  f_equal (fun (w: forall b: sBox S, T (unbox b)) (s: S) => w (sbox s))
    (functional_extensionality_dep_good (boxFun u) (boxFun v)
      (fun b => match b as b0 return boxFun u b0 = boxFun v b0 with
                | sbox s => h s
                end)).

Lemma spropFunextDApp {S: SProp} {T: S -> Type} {u v: forall s, T s}
  (h: forall s, u s = v s) (s0: S):
  f_equal (fun k: forall s, T s => k s0) (spropFunextD h) = h s0.
Proof.
  unfold spropFunextD.
  refine (f_equal_compose _ (fun k: forall s: S, T s => k s0) _ • _).
  now exact (f_equal__functional_extensionality_dep_good _ (sbox s0)).
Defined.

(** Splitting the action of a path between dependent functions on one
    argument at a time, in both sorts of domain. *)

Lemma fEqualStep {A: Type} {B: A -> Type} {u v: forall a, B a} (p: u = v)
  (a: A) {C: Type} (k: B a -> C):
  f_equal (fun h: forall a, B a => k (h a)) p =
  f_equal k (f_equal (fun h: forall a, B a => h a) p).
Proof.
  now exact (eq_sym (f_equal_compose (fun h: forall a, B a => h a) k p)).
Defined.

Lemma fEqualStepS {S: SProp} {B: S -> Type} {u v: forall s, B s} (p: u = v)
  (s: S) {C: Type} (k: B s -> C):
  f_equal (fun h: forall s, B s => k (h s)) p =
  f_equal k (f_equal (fun h: forall s, B s => h s) p).
Proof.
  now exact (eq_sym (f_equal_compose (fun h: forall s, B s => h s) k p)).
Defined.

Lemma rewSymCancelMap {A: Type} {P: A -> Type} {x y: A} (e: x = y) (a: P x):
  rewSymCancelR e (rew [P] e in a) =
  f_equal (fun z => rew [P] e in z) (rewSymCancel e a).
Proof.
  now destruct e.
Defined.

(** Naturality of a homotopy, and the conjugation form of it. *)

Lemma pathNat {A B: Type} (F G: A -> B) (u: forall a, F a = G a)
  {x y: A} (c: x = y): u x • f_equal G c = f_equal F c • u y.
Proof.
  now exact (eq_sym (eq_trans_natural F G u c)).
Defined.

Lemma pathConj {A B: Type} (F G: A -> B) (u: forall a, F a = G a)
  {x y: A} (c: x = y): f_equal F c = u x • (f_equal G c • eq_sym (u y)).
Proof.
  now exact (path_change_natural F G u c).
Defined.

(** The carrier path and its pointwise components *)

Definition faceCarrierPath {psh1 psh2: νGpdPresentation arity}
  (E0: forall n, Equiv (psh1.(G0) n) (psh2.(G0) n)): psh1.(G0) = psh2.(G0) :=
  functional_extensionality_dep_good _ _ (fun n => hgpdEq (E0 n)).

Definition faceMap {F01 F02: nat -> HGpd} (e: F01 = F02) (n: nat):
  F01 n = F02 n := f_equal (fun F: nat -> HGpd => F n) e.

Lemma rewFaceMap {F01 F02: nat -> HGpd} (e: F01 = F02) (h: FaceType F01)
  n q (Hq: q <= n) (ε: arity) (Y: F02 n.+1):
  rew [fun F0: nat -> HGpd => (F0 n).(GDom)] e in
    h n q Hq ε (rew [fun F0: nat -> HGpd => (F0 n.+1).(GDom)] (eq_sym e) in Y)
  = rew [GDom] (faceMap e n) in
      h n q Hq ε (rew [GDom] (eq_sym (faceMap e n.+1)) in Y).
Proof.
  now destruct e.
Defined.

(** Transporting along the carrier path is applying the equivalence. *)

Definition faceTransp {psh1 psh2: νGpdPresentation arity}
  (E0: forall n, Equiv (psh1.(G0) n) (psh2.(G0) n)) (n: nat)
  (x: psh1.(G0) n):
  rew [GDom] (faceMap (faceCarrierPath E0) n) in x = E0 n x :=
  f_equal (fun p: psh1.(G0) n = psh2.(G0) n => rew [GDom] p in x)
    (funExtBetaHGpd (fun n => hgpdEq (E0 n)) n)
  • hgpdEqRew (E0 n) x.

(** The commuting square of [facePath], read on the source carrier: the
    given face square conjugated by the two transports. *)

Definition facePathSrc {psh1 psh2: νGpdPresentation arity}
  (E0: forall n, Equiv (psh1.(G0) n) (psh2.(G0) n))
  (EF: forall n q (Hq: q <= n) (ε: arity) (X: psh1.(G0) n.+1),
    E0 n (psh1.(GFace) n q Hq ε X) =
    psh2.(GFace) n q Hq ε (E0 n.+1 X))
  n q (Hq: q <= n) (ε: arity) (X: psh1.(G0) n.+1):
  rew [GDom] (faceMap (faceCarrierPath E0) n) in psh1.(GFace) n q Hq ε X
  = psh2.(GFace) n q Hq ε
      (rew [GDom] (faceMap (faceCarrierPath E0) n.+1) in X) :=
  faceTransp E0 n (psh1.(GFace) n q Hq ε X)
  • (EF n q Hq ε X
     • f_equal (psh2.(GFace) n q Hq ε) (eq_sym (faceTransp E0 n.+1 X))).

(** The pointwise content of [facePath]: the square above, read on the
    target carrier through the transport bookkeeping. *)

Definition facePathPt {psh1 psh2: νGpdPresentation arity}
  (E0: forall n, Equiv (psh1.(G0) n) (psh2.(G0) n))
  (EF: forall n q (Hq: q <= n) (ε: arity) (X: psh1.(G0) n.+1),
    E0 n (psh1.(GFace) n q Hq ε X) =
    psh2.(GFace) n q Hq ε (E0 n.+1 X))
  n q (Hq: q <= n) (ε: arity) (Y: psh2.(G0) n.+1):
  (rew [FaceType] (faceCarrierPath E0) in psh1.(GFace)) n q Hq ε Y
  = psh2.(GFace) n q Hq ε Y :=
  rew_face_app (faceCarrierPath E0) psh1.(GFace) n q Hq ε Y
  • (rewFaceMap (faceCarrierPath E0) psh1.(GFace) n q Hq ε Y
     • (facePathSrc E0 EF n q Hq ε
          (rew [GDom] (eq_sym (faceMap (faceCarrierPath E0) n.+1)) in Y)
        • f_equal (psh2.(GFace) n q Hq ε)
            (rewSymCancelR (faceMap (faceCarrierPath E0) n.+1) Y))).

(** Convert levelwise carrier equivalences and commuting face squares into
    equality of the two first record fields. *)

Definition facePath {psh1 psh2: νGpdPresentation arity}
  (E0: forall n, Equiv (psh1.(G0) n) (psh2.(G0) n))
  (EF: forall n q (Hq: q <= n) (ε: arity) (X: psh1.(G0) n.+1),
    E0 n (psh1.(GFace) n q Hq ε X) =
    psh2.(GFace) n q Hq ε (E0 n.+1 X)):
  let e0 := functional_extensionality_dep_good _ _
    (fun n => hgpdEq (E0 n)) in
  rew [FaceType] e0 in psh1.(GFace) = psh2.(GFace).
Proof.
  cbn.
  apply functional_extensionality_dep_good; intro n.
  apply functional_extensionality_dep_good; intro q.
  apply spropFunextD; intro Hq.
  apply functional_extensionality_dep_good; intro ε.
  apply functional_extensionality_dep_good; intro Y.
  now exact (facePathPt E0 EF n q Hq ε Y).
Defined.

(** [facePath] is the funext of its pointwise content, so its action on a
    point is that content. *)

Lemma facePathApp {psh1 psh2: νGpdPresentation arity}
  (E0: forall n, Equiv (psh1.(G0) n) (psh2.(G0) n))
  (EF: forall n q (Hq: q <= n) (ε: arity) (X: psh1.(G0) n.+1),
    E0 n (psh1.(GFace) n q Hq ε X) =
    psh2.(GFace) n q Hq ε (E0 n.+1 X))
  n q (Hq: q <= n) (ε: arity) (Y: psh2.(G0) n.+1):
  f_equal (fun h: FaceType psh2.(G0) => h n q Hq ε Y) (facePath E0 EF)
  = facePathPt E0 EF n q Hq ε Y.
Proof.
  unfold facePath.
  etransitivity. { now exact (fEqualStep _ n
    (fun k: forall q (Hq: q <= n) (ε: arity),
       psh2.(G0) n.+1 -> psh2.(G0) n => k q Hq ε Y)). }
  rewrite f_equal__functional_extensionality_dep_good.
  etransitivity. { now exact (fEqualStep _ q
    (fun k: forall (Hq: q <= n) (ε: arity),
       psh2.(G0) n.+1 -> psh2.(G0) n => k Hq ε Y)). }
  rewrite f_equal__functional_extensionality_dep_good.
  etransitivity. { now exact (fEqualStepS _ Hq
    (fun k: forall (ε: arity), psh2.(G0) n.+1 -> psh2.(G0) n => k ε Y)). }
  rewrite spropFunextDApp.
  etransitivity. { now exact (fEqualStep _ ε
    (fun k: psh2.(G0) n.+1 -> psh2.(G0) n => k Y)). }
  rewrite f_equal__functional_extensionality_dep_good.
  now exact (f_equal__functional_extensionality_dep_good _ Y).
Defined.

Definition faceDataPath {psh1 psh2: νGpdPresentation arity}
  (E0: forall n, Equiv (psh1.(G0) n) (psh2.(G0) n))
  (EF: forall n q (Hq: q <= n) (ε: arity) (X: psh1.(G0) n.+1),
    E0 n (psh1.(GFace) n q Hq ε X) =
    psh2.(GFace) n q Hq ε (E0 n.+1 X)):
  ((psh1.(G0); psh1.(GFace)): {F0: nat -> HGpd &T FaceType F0}) =
  (psh2.(G0); psh2.(GFace)) :=
  eq_existT_curried
    (functional_extensionality_dep_good _ _ (fun n => hgpdEq (E0 n)))
    (facePath E0 EF).

Record PresheafEquiv (psh1 psh2: νGpdPresentation arity) := {
  F0Equiv n: Equiv (psh1.(G0) n) (psh2.(G0) n);
  FaceEquiv n q (Hq: q <= n) (ε: arity) (X: psh1.(G0) n.+1):
    F0Equiv n (psh1.(GFace) n q Hq ε X) =
    psh2.(GFace) n q Hq ε (F0Equiv n.+1 X);
  FaceCohEquiv:
    rewFaceCoh (faceDataPath F0Equiv FaceEquiv)
      (psh1.(GFaceCoh) : FaceCohType psh1.(G0) psh1.(GFace)) =
      (psh2.(GFaceCoh) : FaceCohType psh2.(G0) psh2.(GFace))
}.

(** Equality of the first three fields determines the record.  The final
    field is proof-irrelevant by [GUIP] at the appropriate carrier level. *)

Lemma presheafEqIntro (psh1 psh2: νGpdPresentation arity)
  (e0: psh1.(G0) = psh2.(G0))
  (e1: rew [FaceType] e0 in psh1.(GFace) = psh2.(GFace))
  (e2: rewFaceCoh
        (eq_existT_curried e0 e1 :
          ((psh1.(G0); psh1.(GFace)): {F0: nat -> HGpd &T FaceType F0}) =
          (psh2.(G0); psh2.(GFace)))
      (psh1.(GFaceCoh) : FaceCohType psh1.(G0) psh1.(GFace)) =
      (psh2.(GFaceCoh) : FaceCohType psh2.(G0) psh2.(GFace))):
  psh1 = psh2.
Proof.
  destruct psh1 as [F01 Face1 Coh1 Coh21],
    psh2 as [F02 Face2 Coh2 Coh22]; cbn in e0, e1, e2.
  destruct e0; cbn in e1; destruct e1; cbn in e2; destruct e2.
  apply (f_equal (fun C => {| G0 := F01; GFace := Face1;
    GFaceCoh := Coh1; GFaceCoh2 := C |})).
  apply functional_extensionality_dep_good; intro n.
  apply functional_extensionality_dep_good; intro q.
  apply spropFunext; intro Hq.
  apply functional_extensionality_dep_good; intro r.
  apply spropFunext; intro Hr.
  apply functional_extensionality_dep_good; intro s.
  apply spropFunext; intro Hs.
  apply functional_extensionality_dep_good; intro ε.
  apply functional_extensionality_dep_good; intro ω.
  apply functional_extensionality_dep_good; intro θ.
  apply functional_extensionality_dep_good; intro X.
  now apply (F01 n).(GUIP).
Qed.

Lemma presheafEquivEq {psh1 psh2: νGpdPresentation arity}
  (E: PresheafEquiv psh1 psh2): psh1 = psh2.
Proof.
  apply (presheafEqIntro psh1 psh2
    (functional_extensionality_dep_good _ _
      (fun n => hgpdEq (F0Equiv _ _ E n)))
    (facePath (F0Equiv _ _ E) (FaceEquiv _ _ E))).
  now exact (FaceCohEquiv _ _ E).
Qed.

(** Transporting [GFaceCoh] along a path between carrier-and-face data

    The transport is determined by the path's pointwise action on the
    carriers and on the face maps.  [faceSq] names the latter: the square
    identifying the transported face of a cell with the face of the
    transported cell. *)

Definition faceSq {F01 F02: nat -> HGpd} {Face1: FaceType F01}
  {Face2: FaceType F02} (e0: F01 = F02)
  (e1: rew [FaceType] e0 in Face1 = Face2)
  n q (Hq: q <= n) (ε: arity) (X: F01 n.+1):
  rew [GDom] (faceMap e0 n) in Face1 n q Hq ε X
  = Face2 n q Hq ε (rew [GDom] (faceMap e0 n.+1) in X).
Proof.
  destruct e0; cbn in e1; destruct e1. now reflexivity.
Defined.

Lemma faceSqApp {F01 F02: nat -> HGpd} {Face1: FaceType F01}
  {Face2: FaceType F02} (e0: F01 = F02)
  (e1: rew [FaceType] e0 in Face1 = Face2)
  n q (Hq: q <= n) (ε: arity) (X: F01 n.+1):
  faceSq e0 e1 n q Hq ε X
  = eq_sym (rew_face_app e0 Face1 n q Hq ε (rew [GDom] (faceMap e0 n.+1) in X)
      • (rewFaceMap e0 Face1 n q Hq ε (rew [GDom] (faceMap e0 n.+1) in X)
         • f_equal (fun z => rew [GDom] (faceMap e0 n) in Face1 n q Hq ε z)
             (rewSymCancel (faceMap e0 n.+1) X)))
    • f_equal (fun h: FaceType F02 =>
        h n q Hq ε (rew [GDom] (faceMap e0 n.+1) in X)) e1.
Proof.
  destruct e0; cbn in e1; destruct e1. now reflexivity.
Defined.

Lemma rewFaceCohIntro {F01 F02: nat -> HGpd} {Face1: FaceType F01}
  {Face2: FaceType F02} (e0: F01 = F02)
  (e1: rew [FaceType] e0 in Face1 = Face2)
  (C1: FaceCohType F01 Face1) (C2: FaceCohType F02 Face2)
  (H: forall n q (Hq: q <= n) r (Hr: r <= q) (ε ω: arity) (X: F01 n.+2),
    f_equal (fun x: F01 n => rew [GDom] (faceMap e0 n) in x)
      (C1 n q Hq r Hr ε ω X)
    • (faceSq e0 e1 n r (Hr ↕ Hq) ω (Face1 n.+1 q.+1 (⇑ Hq) ε X)
       • f_equal (Face2 n r (Hr ↕ Hq) ω)
           (faceSq e0 e1 n.+1 q.+1 (⇑ Hq) ε X))
    = (faceSq e0 e1 n q Hq ε (Face1 n.+1 r (Hr ↕ (↑ Hq)) ω X)
       • f_equal (Face2 n q Hq ε)
           (faceSq e0 e1 n.+1 r (Hr ↕ (↑ Hq)) ω X))
      • C2 n q Hq r Hr ε ω (rew [GDom] (faceMap e0 n.+2) in X)):
  rewFaceCoh (eq_existT_curried e0 e1) C1 = C2.
Proof.
  destruct e0; cbn in e1; destruct e1; cbn.
  apply functional_extensionality_dep_good; intro n.
  apply functional_extensionality_dep_good; intro q.
  apply spropFunextD; intro Hq.
  apply functional_extensionality_dep_good; intro r.
  apply spropFunextD; intro Hr.
  apply functional_extensionality_dep_good; intro ε.
  apply functional_extensionality_dep_good; intro ω.
  apply functional_extensionality_dep_good; intro X.
  specialize (H n q Hq r Hr ε ω X); cbn in H.
  rewrite f_equal_id, eq_trans_refl_l in H.
  now exact H.
Defined.

(** The square [facePath] provides is the given one, conjugated by the
    transports along the carrier path. *)

Lemma faceSqFacePath {psh1 psh2: νGpdPresentation arity}
  (E0: forall n, Equiv (psh1.(G0) n) (psh2.(G0) n))
  (EF: forall n q (Hq: q <= n) (ε: arity) (X: psh1.(G0) n.+1),
    E0 n (psh1.(GFace) n q Hq ε X) =
    psh2.(GFace) n q Hq ε (E0 n.+1 X))
  n q (Hq: q <= n) (ε: arity) (X: psh1.(G0) n.+1):
  faceSq (faceCarrierPath E0) (facePath E0 EF) n q Hq ε X
  = facePathSrc E0 EF n q Hq ε X.
Proof.
  rewrite faceSqApp, facePathApp.
  unfold facePathPt.
  rewrite 2 eq_trans_sym_cancel_common.
  rewrite rewSymCancelMap.
  rewrite (f_equal_compose
    (fun z: psh1.(G0) n.+1 =>
       rew [GDom] (faceMap (faceCarrierPath E0) n.+1) in z)
    (psh2.(GFace) n q Hq ε)).
  rewrite (pathNat _ _ (facePathSrc E0 EF n q Hq ε)
    (rewSymCancel (faceMap (faceCarrierPath E0) n.+1) X)).
  now apply eq_trans_sym_cancel_l.
Defined.

(** The path algebra of the [GFaceCoh] clause: with the four squares written
    as conjugates, every transport correction cancels and what is left is
    the compatibility of the exchange laws with the carrier equivalences. *)

Lemma faceCohConj {U V W: Type} (fq fr: V -> U) (gq gr: W -> V)
  {pa Pa pb Pb: U} {pW1 PW1 pW2 PW2: V} {pX PX: W}
  (α: pa = Pa) (β: pb = Pb) (γ: pW1 = PW1) (δ: pW2 = PW2) (μ: pX = PX)
  (e1: Pa = fq PW2) (e2: Pb = fr PW1) (e3: PW1 = gq PX) (e4: PW2 = gr PX)
  (K: Pa = Pb) (c2: forall z: W, fq (gr z) = fr (gq z))
  (H: K • (e2 • f_equal fr e3) = (e1 • f_equal fq e4) • c2 PX):
  (α • (K • eq_sym β))
  • ((β • (e2 • f_equal fr (eq_sym γ)))
     • f_equal fr (γ • (e3 • f_equal gq (eq_sym μ))))
  = ((α • (e1 • f_equal fq (eq_sym δ)))
     • f_equal fq (δ • (e4 • f_equal gr (eq_sym μ))))
    • c2 pX.
Proof.
  rewrite <- (eq_sym_map_distr fr γ), <- (eq_sym_map_distr fq δ),
    <- (eq_sym_map_distr gq μ), <- (eq_sym_map_distr gr μ).
  change (path_change α K β •
    (path_change β e2 (f_equal fr γ) • f_equal fr (path_change γ e3 (f_equal gq μ))) =
    (path_change α e1 (f_equal fq δ) • f_equal fq (path_change δ e4 (f_equal gr μ)))
      • c2 pX).
  rewrite 2 path_change_map, 3 path_change_comp.
  unfold path_change.
  rewrite H.
  pose proof (path_prefix_solve (f_equal_naturality gr gq fq fr c2 μ)) as N.
  rewrite N.
  rewrite <- 6 eq_trans_assoc.
  now rewrite eq_trans_sym_inv_r, eq_trans_refl_r, <- eq_trans_assoc.
Defined.

(** Compatibility of carrier equivalences and face squares with the
    exchange laws identifies the transported [GFaceCoh] field along
    [faceDataPath E0 EF]. *)

Lemma faceCohEquivIntro {psh1 psh2: νGpdPresentation arity}
  (E0: forall n, Equiv (psh1.(G0) n) (psh2.(G0) n))
  (EF: forall n q (Hq: q <= n) (ε: arity) (X: psh1.(G0) n.+1),
    E0 n (psh1.(GFace) n q Hq ε X) =
    psh2.(GFace) n q Hq ε (E0 n.+1 X))
  (H: forall n q (Hq: q <= n) r (Hr: r <= q) (ε ω: arity)
    (X: psh1.(G0) n.+2),
    f_equal (E0 n) (psh1.(GFaceCoh) n q Hq r Hr ε ω X)
    • (EF n r (Hr ↕ Hq) ω (psh1.(GFace) n.+1 q.+1 (⇑ Hq) ε X)
       • f_equal (psh2.(GFace) n r (Hr ↕ Hq) ω)
           (EF n.+1 q.+1 (⇑ Hq) ε X))
    = (EF n q Hq ε (psh1.(GFace) n.+1 r (Hr ↕ (↑ Hq)) ω X)
       • f_equal (psh2.(GFace) n q Hq ε) (EF n.+1 r (Hr ↕ (↑ Hq)) ω X))
      • psh2.(GFaceCoh) n q Hq r Hr ε ω (E0 n.+2 X)):
  rewFaceCoh (faceDataPath E0 EF) psh1.(GFaceCoh) = psh2.(GFaceCoh).
Proof.
  unfold faceDataPath.
  apply (rewFaceCohIntro (faceCarrierPath E0) (facePath E0 EF)).
  intros n q Hq r Hr ε ω X.
  rewrite 4 faceSqFacePath.
  unfold facePathSrc.
  rewrite (pathConj
    (fun x: psh1.(G0) n => rew [GDom] (faceMap (faceCarrierPath E0) n) in x)
    (E0 n) (faceTransp E0 n) (psh1.(GFaceCoh) n q Hq r Hr ε ω X)).
  now exact (faceCohConj
    (psh2.(GFace) n q Hq ε) (psh2.(GFace) n r (Hr ↕ Hq) ω)
    (psh2.(GFace) n.+1 q.+1 (⇑ Hq) ε) (psh2.(GFace) n.+1 r (Hr ↕ (↑ Hq)) ω)
    (faceTransp E0 n (psh1.(GFace) n q Hq ε
       (psh1.(GFace) n.+1 r (Hr ↕ (↑ Hq)) ω X)))
    (faceTransp E0 n (psh1.(GFace) n r (Hr ↕ Hq) ω
       (psh1.(GFace) n.+1 q.+1 (⇑ Hq) ε X)))
    (faceTransp E0 n.+1 (psh1.(GFace) n.+1 q.+1 (⇑ Hq) ε X))
    (faceTransp E0 n.+1 (psh1.(GFace) n.+1 r (Hr ↕ (↑ Hq)) ω X))
    (faceTransp E0 n.+2 X)
    (EF n q Hq ε (psh1.(GFace) n.+1 r (Hr ↕ (↑ Hq)) ω X))
    (EF n r (Hr ↕ Hq) ω (psh1.(GFace) n.+1 q.+1 (⇑ Hq) ε X))
    (EF n.+1 q.+1 (⇑ Hq) ε X)
    (EF n.+1 r (Hr ↕ (↑ Hq)) ω X)
    (f_equal (E0 n) (psh1.(GFaceCoh) n q Hq r Hr ε ω X))
    (psh2.(GFaceCoh) n q Hq r Hr ε ω)
    (H n q Hq r Hr ε ω X)).
Defined.

End PresheafEquiv.

Module PresheafEquivSimplicial := PresheafEquiv SimplicialGpdLayer.
Module PresheafEquivCubical := PresheafEquiv CubicalGpdLayer.
