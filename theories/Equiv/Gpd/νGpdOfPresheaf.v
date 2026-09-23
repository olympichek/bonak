(** The forward direction of the correspondence between the fibred
    presentation ([νGpdPresentation]) and the indexed construction ([νGpd]):
    [f: νGpdPresentation arity -> νGpds].

    The definitions are organized by dependency stage. Each [Psh*] record
    augments the corresponding construction record with presheaf frame maps,
    painting values, or coherence data. The stored carrier level [m] is an
    explicit parameter; SProp bounds relate construction stages to [m], and
    proof irrelevance removes dependence on the bound witnesses. *)

Import Logic.EqNotations.

Set Warnings "-notation-overridden".
From Bonak Require Import SigT RewLemmas HSet LeSProp Notation νGpd.HGpd νGpd.Layer
  νGpd.Lemmas νGpd.Pasting νGpd Presheaf.Gpd.Presentation Equiv.Gpd.PathAlgebra.
From Bonak.Equiv.Gpd Require Import Face PresheafEquiv.

From Bonak Require Import Limit.

From Bonak.Lib Require Import NatLemmas.

Set Primitive Projections.
Set Keyed Unification.

Module νGpdOfPresheaf (A: LayerGpdSig).
Import A.

Include Bonak.Equiv.Gpd.PathAlgebra.

Module Export Face := Bonak.Equiv.Gpd.Face.Face A.
Module Export PshEq := Bonak.Equiv.Gpd.PresheafEquiv.PresheafEquiv A.

Section Construction.
Variable psh: νGpdPresentation arity.

(** νGpdPresentation-side lists over the staged dependency construction *)

Fixpoint mkPshFrameTypes (m: nat) {p k}: mkFrameTypes p k -> Type :=
  match p with
  | 0 => fun _ => unit
  | S p => fun frames =>
      { _: mkPshFrameTypes m frames.1 &T psh.(G0) m -> frames.2 }
  end.

Fixpoint mkPshPaintingTypes (m: nat) {p k}:
  forall {frames: mkFrameTypes p k}, mkPshFrameTypes m frames ->
  mkPaintingTypes p k frames -> Type :=
  match p with
  | 0 => fun _ _ _ => unit
  | S p => fun frames pshFrames paintings =>
      { _: mkPshPaintingTypes m pshFrames.1 paintings.1 &T
        forall d: psh.(G0) m, paintings.2 (pshFrames.2 d) }
  end.

(** The presheaf-side block

    The types of the restr coherences at stages <= p (stating that the
    presheaf-frame maps commute with the face maps and the construction's
    restrictions), together with the next-level presheaf-frame maps they
    determine. The two definitions are mutually dependent, so
    [mkPshRestrTypesAndFrames] constructs them together. *)

Class PshRestrBlock (m: nat) {p k} {frames: mkFrameTypes p k}
  (pshFrames: mkPshFrameTypes m frames) (block: RestrFrameTypeBlock p k) := {
  PshRestrTypesDef: block.(RestrFrameTypesDef) -> Type;
  PshFramesDef: forall {R} (Q: PshRestrTypesDef R),
    mkPshFrameTypes m.+1 (block.(FrameDef) R);
}.

Definition mkPshRestrTypesStep {m p k} {frames: mkFrameTypes p.+1 k}
  (pshFrames: mkPshFrameTypes m frames)
  {prev: RestrFrameTypeBlock p k.+1}
  (prevPsh: PshRestrBlock m pshFrames.1 prev)
  (R: mkRestrFrameTypesStep frames prev): Type :=
  { Q: prevPsh.(PshRestrTypesDef) R.1 &T
    forall q (Hq: q <= k) (Hqp: q + p <= m) (ε: arity) (d: psh.(G0) m.+1),
      pshFrames.2 (psh.(GFace) m (q + p) Hqp ε d) =
      R.2 q Hq ε ((prevPsh.(PshFramesDef) Q).2 d) }.

(** The presheaf layer: the level-m painting at the ε-face, transported
    along the diagonal restr coherence *)

Definition mkPshLayer {m p k} {frames: mkFrameTypes p.+1 k}
  {pshFrames: mkPshFrameTypes m frames}
  {paintings: mkPaintingTypes p.+1 k frames}
  (pshPaintings: mkPshPaintingTypes m pshFrames paintings)
  {prev: RestrFrameTypeBlock p k.+1}
  {prevPsh: PshRestrBlock m pshFrames.1 prev}
  {R: mkRestrFrameTypesStep frames prev}
  (Q: mkPshRestrTypesStep pshFrames prevPsh R)
  (Hp: p <= m) (d: psh.(G0) m.+1):
  mkLayer (painting := paintings.2) R.2
    ((prevPsh.(PshFramesDef) Q.1).2 d) :=
  lam (fun ε =>
    rew [paintings.2] Q.2 0 leR_O Hp ε d in
    pshPaintings.2 (psh.(GFace) m p Hp ε d)).

Fixpoint mkPshRestrTypesAndFrames (m: nat) {p k}:
  forall (Hp: p <= m.+1)
    {frames: mkFrameTypes p k} (pshFrames: mkPshFrameTypes m frames)
    {paintings: mkPaintingTypes p k frames}
    (pshPaintings: mkPshPaintingTypes m pshFrames paintings),
  PshRestrBlock m pshFrames (mkRestrFrameTypesAndFrames paintings) :=
  match p return forall (Hp: p <= m.+1)
    (frames: mkFrameTypes p k) (pshFrames: mkPshFrameTypes m frames)
    (paintings: mkPaintingTypes p k frames)
    (pshPaintings: mkPshPaintingTypes m pshFrames paintings),
    PshRestrBlock m pshFrames (mkRestrFrameTypesAndFrames paintings) with
  | 0 => fun Hp frames pshFrames paintings pshPaintings =>
    Build_PshRestrBlock m 0 k frames pshFrames
      (mkRestrFrameTypesAndFrames paintings)
      (fun _ => unit)
      (fun _ _ => (tt; fun _ => tt))
  | S p => fun Hp frames pshFrames paintings pshPaintings =>
    let prevPsh :=
      mkPshRestrTypesAndFrames m (↓ Hp) pshFrames.1 pshPaintings.1 in
    Build_PshRestrBlock m p.+1 k frames pshFrames
      (mkRestrFrameTypesAndFrames paintings)
      (fun R => mkPshRestrTypesStep pshFrames prevPsh R)
      (fun R Q =>
         (prevPsh.(PshFramesDef) Q.1;
          fun d => ((prevPsh.(PshFramesDef) Q.1).2 d;
                    mkPshLayer pshPaintings Q (⇓ Hp) d)))
  end.

(** νGpdPresentation data for [DepsRestr] *)

Class PshDepsRestr (m: nat) (p k: nat) := {
  _pdeps: DepsRestr p k;
  _pshBound: p <= m.+1;
  _pshFrames: mkPshFrameTypes m _pdeps.(_frames);
  _pshPaintings: mkPshPaintingTypes m _pshFrames _pdeps.(_paintings);
  _pshRestrs: (mkPshRestrTypesAndFrames m _pshBound _pshFrames
    _pshPaintings).(PshRestrTypesDef) _pdeps.(_restrFrames);
}.

#[local]
Instance proj1PshDepsRestr {m p k} (P: PshDepsRestr m p.+1 k):
  PshDepsRestr m p k.+1 :=
{|
  _pdeps := P.(_pdeps).(1);
  _pshBound := ↓ P.(_pshBound);
  _pshFrames := P.(_pshFrames).1;
  _pshPaintings := P.(_pshPaintings).1;
  _pshRestrs := P.(_pshRestrs).1;
|}.

Definition mkPshFrames {m p k} (P: PshDepsRestr m p k):
  mkPshFrameTypes m.+1 (mkFrames P.(_pdeps)) :=
  (mkPshRestrTypesAndFrames m P.(_pshBound) P.(_pshFrames)
    P.(_pshPaintings)).(PshFramesDef) P.(_pshRestrs).

Definition mkPshFrame {m p k} (P: PshDepsRestr m p k):
  psh.(G0) m.+1 -> mkFrame P.(_pdeps) := (mkPshFrames P).2.

Lemma nth_mkPshFrame {m p k} (P: PshDepsRestr m p.+1 k)
  (d: psh.(G0) m.+1) (ε: arity):
  nth (mkPshFrame P d).2 ε =
  rew [P.(_pdeps).(_paintings).2]
      P.(_pshRestrs).2 0 leR_O (⇓ P.(_pshBound)) ε d in
    P.(_pshPaintings).2
      (psh.(GFace) m p (⇓ P.(_pshBound)) ε d).
Proof.
  unfold mkPshFrame, mkPshFrames.
  cbn [mkPshRestrTypesAndFrames PshFramesDef].
  unfold mkPshLayer.
  now apply (nth_lam
    (B := fun ε0 =>
      P.(_pdeps).(_paintings).2
        (P.(_pdeps).(_restrFrames).2 0 leR_O ε0
          (((mkPshRestrTypesAndFrames m (↓ P.(_pshBound))
            P.(_pshFrames).1 P.(_pshPaintings).1)
            .(PshFramesDef) P.(_pshRestrs).1).2 d)))).
Defined.

(** The candidate filler *)

Definition mkPshFiller {m p} (P: PshDepsRestr m p 0):
  mkFrame P.(_pdeps) -> HGpd :=
  fun D => {d': psh.(G0) m.+1 & gpaths D (mkPshFrame P d')}.

(** νGpdPresentation data for [DepsRestrExtension]

    The top constructor uses the candidate filler definitionally. *)

Inductive PshDepsExtension (m: nat):
  forall {p k} (P: PshDepsRestr m p k),
  DepsRestrExtension p k P.(_pdeps) -> Type :=
| TopPshDep {p} {P: PshDepsRestr m p 0}:
    PshDepsExtension m P (TopRestrDep (mkPshFiller P))
| AddPshDep {p k} (P: PshDepsRestr m p.+1 k)
    {X: DepsRestrExtension p.+1 k P.(_pdeps)}:
    PshDepsExtension m P X ->
    PshDepsExtension m (proj1PshDepsRestr P) (AddRestrDep P.(_pdeps) X).

Arguments TopPshDep {m p P}.
Arguments AddPshDep {m p k} P {X} _.

(** The presheaf painting corresponding to [mkPainting]

    At the top it is [(d; eq_refl)] — the cell
    [d] itself fills its own frame; below, it pairs the layers of the
    presheaf frame one level up. *)

Fixpoint mkPshPainting {m p k} {P: PshDepsRestr m p k}
  {X: DepsRestrExtension p k P.(_pdeps)}
  (PX: PshDepsExtension m P X) (d: psh.(G0) m.+1):
  mkPainting X (mkPshFrame P d) :=
  match PX with
  | TopPshDep => (d; eq_refl)
  | AddPshDep P' PX' => ((mkPshFrame P' d).2; mkPshPainting PX' d)
  end.

Fixpoint mkPshPaintingsPrefix {m p k}:
  forall {P: PshDepsRestr m p k} {X: DepsRestrExtension p k P.(_pdeps)}
  (PX: PshDepsExtension m P X),
  mkPshPaintingTypes m.+1 (mkPshFrames P).1 (mkPaintingsPrefix X) :=
  match p with
  | 0 => fun _ _ _ => tt
  | S p => fun P X PX =>
      (mkPshPaintingsPrefix (AddPshDep P PX); mkPshPainting (AddPshDep P PX))
  end.

Definition mkPshPaintings {m p k} {P: PshDepsRestr m p k}
  {X: DepsRestrExtension p k P.(_pdeps)} (PX: PshDepsExtension m P X):
  mkPshPaintingTypes m.+1 (mkPshFrames P) (mkPaintings X) :=
  (mkPshPaintingsPrefix PX; mkPshPainting PX).

(** νGpdPresentation coherence data for [DepsCohs]

    The remaining presheaf-side data: the coherences stating that the
    presheaf paintings commute with the construction's restr paintings,
    packaged with the construction data they are stated against. From
    these we rebuild everything one level up: the next-level restr
    coherences ([mkPshRestrFrames]) and the next-level restr-painting
    coherences ([mkPshRestrPainting]). *)

(** The face dimension is a [nat] index only; rewriting it under the SProp
    bound needs an equational form. *)

Lemma pshFaceDimIrr {n q q'} (e: q = q') {Hq: q <= n} {Hq': q' <= n}
  (ε: arity) (X: psh.(G0) n.+1):
  psh.(GFace) n q Hq ε X = psh.(GFace) n q' Hq' ε X.
Proof.
  now destruct e.
Defined.

Lemma pshFaceDimIrr_sym {n q q'} (e: q = q')
  {Hq: q <= n} {Hq': q' <= n} (ε: arity) (X: psh.(G0) n.+1):
  eq_sym (pshFaceDimIrr e (Hq := Hq) (Hq' := Hq') ε X) =
  pshFaceDimIrr (eq_sym e) (Hq := Hq') (Hq' := Hq) ε X.
Proof.
  now destruct e.
Defined.

(** A bounded pair packages the two face indices. Paths changing one
    coordinate preserve all bound witnesses by strict proof irrelevance. *)
Record FacePairIndex (n: nat) := facePairIndex {
  pairQ: nat; pairR: nat;
  pairHQ: pairQ <= n; pairHR: pairR <= pairQ
}.

Local Arguments facePairIndex {n} _ _ _ _.
Local Arguments pairQ {n} _.
Local Arguments pairR {n} _.
Local Arguments pairHQ {n} _.
Local Arguments pairHR {n} _.

Local Definition facePairQ {n q q' r} (e: q = q')
  (Hq: q <= n) (Hq': q' <= n) (Hr: r <= q):
  facePairIndex q r Hq Hr = facePairIndex q' r Hq' (leR_eq_r e Hr).
Proof. now destruct e. Defined.

Local Definition facePairR {n q r r'} (e: r = r')
  (Hq: q <= n) (Hr: r <= q) (Hr': r' <= q):
  facePairIndex q r Hq Hr = facePairIndex q r' Hq Hr'.
Proof. now destruct e. Defined.

Local Definition facePairLeft {n} (ε ω: arity) (X: psh.(G0) n.+2)
  (i: FacePairIndex n) :=
  psh.(GFace) n i.(pairQ) i.(pairHQ) ε
    (psh.(GFace) n.+1 i.(pairR) (i.(pairHR) ↕ ↑ i.(pairHQ)) ω X).

Local Definition facePairRight {n} (ε ω: arity) (X: psh.(G0) n.+2)
  (i: FacePairIndex n) :=
  psh.(GFace) n i.(pairR) (i.(pairHR) ↕ i.(pairHQ)) ω
    (psh.(GFace) n.+1 i.(pairQ).+1 (⇑ i.(pairHQ)) ε X).

Local Definition facePairCell {n} (ε ω: arity) (X: psh.(G0) n.+2)
  (i: FacePairIndex n): facePairLeft ε ω X i = facePairRight ε ω X i :=
  psh.(GFaceCoh) n i.(pairQ) i.(pairHQ) i.(pairR) i.(pairHR) ε ω X.

Local Lemma facePairLeftQ {n q q' r} (e: q = q')
  (Hq: q <= n) (Hq': q' <= n) (Hr: r <= q)
  (ε ω: arity) (X: psh.(G0) n.+2):
  f_equal (facePairLeft ε ω X) (facePairQ e Hq Hq' Hr) =
  pshFaceDimIrr e ε (psh.(GFace) n.+1 r (Hr ↕ ↑ Hq) ω X).
Proof. now destruct e. Defined.

Local Lemma facePairRightQ {n q q' r} (e: q = q')
  (Hq: q <= n) (Hq': q' <= n) (Hr: r <= q)
  (ε ω: arity) (X: psh.(G0) n.+2):
  f_equal (facePairRight ε ω X) (facePairQ e Hq Hq' Hr) =
  f_equal (psh.(GFace) n r (Hr ↕ Hq) ω)
    (pshFaceDimIrr (f_equal S e) (Hq := ⇑ Hq) (Hq' := ⇑ Hq') ε X).
Proof. now destruct e. Defined.

Local Lemma facePairLeftR {n q r r'} (e: r = r')
  (Hq: q <= n) (Hr: r <= q) (Hr': r' <= q)
  (ε ω: arity) (X: psh.(G0) n.+2):
  f_equal (facePairLeft ε ω X) (facePairR e Hq Hr Hr') =
  f_equal (psh.(GFace) n q Hq ε)
    (pshFaceDimIrr e (Hq := Hr ↕ ↑ Hq) (Hq' := Hr' ↕ ↑ Hq) ω X).
Proof. now destruct e. Defined.

Local Lemma facePairRightR {n q r r'} (e: r = r')
  (Hq: q <= n) (Hr: r <= q) (Hr': r' <= q)
  (ε ω: arity) (X: psh.(G0) n.+2):
  f_equal (facePairRight ε ω X) (facePairR e Hq Hr Hr') =
  pshFaceDimIrr e (Hq := Hr ↕ Hq) (Hq' := Hr' ↕ Hq) ω
    (psh.(GFace) n.+1 q.+1 (⇑ Hq) ε X).
Proof. now destruct e. Defined.

(** Naturality of [GFaceCoh] along a path of bounded index pairs. The
    right boundary is pasted in the same coordinate order as the left one,
    then the naturality of the inner face comparison exchanges that order. *)
Lemma pshFaceCohDimIrr {n q q' r r'} (eqQ: q = q') (eqR: r = r')
  {Hq: q <= n} {Hq': q' <= n} {Hr: r <= q} {Hr': r' <= q'}
  (ε ω: arity) (X: psh.(G0) n.+2):
  psh.(GFaceCoh) n q Hq r Hr ε ω X
  • (pshFaceDimIrr eqR
       (Hq := Hr ↕ Hq) (Hq' := Hr' ↕ Hq') ω
       (psh.(GFace) n.+1 q.+1 (⇑ Hq) ε X)
    • f_equal (psh.(GFace) n r' (Hr' ↕ Hq') ω)
        (pshFaceDimIrr (f_equal S eqQ)
          (Hq := ⇑ Hq) (Hq' := ⇑ Hq') ε X)) =
  (pshFaceDimIrr eqQ (Hq := Hq) (Hq' := Hq') ε
       (psh.(GFace) n.+1 r (Hr ↕ (↑ Hq)) ω X)
   • f_equal (psh.(GFace) n q' Hq' ε)
       (pshFaceDimIrr eqR
         (Hq := Hr ↕ (↑ Hq)) (Hq' := Hr' ↕ (↑ Hq')) ω X))
  • psh.(GFaceCoh) n q' Hq' r' Hr' ε ω X.
Proof.
  pose proof (eq_trans_natural (facePairLeft ε ω X) (facePairRight ε ω X)
    (facePairCell ε ω X)
    (facePairQ eqQ Hq Hq' Hr • facePairR eqR Hq' (leR_eq_r eqQ Hr) Hr')) as H.
  rewrite (eq_trans_map_distr (facePairLeft ε ω X)),
    (eq_trans_map_distr (facePairRight ε ω X)) in H.
  rewrite (facePairLeftQ eqQ Hq Hq' Hr ε ω X),
    (facePairLeftR eqR Hq' (leR_eq_r eqQ Hr) Hr' ε ω X),
    (facePairRightQ eqQ Hq Hq' Hr ε ω X),
    (facePairRightR eqR Hq' (leR_eq_r eqQ Hr) Hr' ε ω X) in H.
  cbn [facePairCell pairQ pairR pairHQ pairHR] in H.
  rewrite (eq_trans_natural
    (psh.(GFace) n r (Hr ↕ Hq) ω) (psh.(GFace) n r' (Hr' ↕ Hq') ω)
    (fun x => pshFaceDimIrr eqR (Hq := Hr ↕ Hq) (Hq' := Hr' ↕ Hq') ω x)
    (pshFaceDimIrr (f_equal S eqQ) (Hq := ⇑ Hq) (Hq' := ⇑ Hq') ε X)) in H.
  now exact (eq_sym H).
Defined.

Lemma pshFaceCohDimIrr_map {n q q' r r'} (eqQ: q = q') (eqR: r = r')
  {Hq: q <= n} {Hq': q' <= n} {Hr: r <= q} {Hr': r' <= q'}
  (ε ω: arity) (X: psh.(G0) n.+2) {Y: Type}
  (F: psh.(G0) n -> Y):
  f_equal F (psh.(GFaceCoh) n q Hq r Hr ε ω X)
  • (f_equal F
       (pshFaceDimIrr eqR
         (Hq := Hr ↕ Hq) (Hq' := Hr' ↕ Hq') ω
         (psh.(GFace) n.+1 q.+1 (⇑ Hq) ε X))
    • f_equal F
        (f_equal (psh.(GFace) n r' (Hr' ↕ Hq') ω)
          (pshFaceDimIrr (f_equal S eqQ)
            (Hq := ⇑ Hq) (Hq' := ⇑ Hq') ε X))) =
  f_equal F
    (pshFaceDimIrr eqQ (Hq := Hq) (Hq' := Hq') ε
      (psh.(GFace) n.+1 r (Hr ↕ (↑ Hq)) ω X))
  • (f_equal F
       (f_equal (psh.(GFace) n q' Hq' ε)
         (pshFaceDimIrr eqR
           (Hq := Hr ↕ (↑ Hq)) (Hq' := Hr' ↕ (↑ Hq')) ω X))
    • f_equal F (psh.(GFaceCoh) n q' Hq' r' Hr' ε ω X)).
Proof.
  pose proof (f_equal (fun p => f_equal F p)
    (pshFaceCohDimIrr eqQ eqR (Hq := Hq) (Hq' := Hq') (Hr := Hr) (Hr' := Hr')
      ε ω X)) as H.
  cbn beta in H.
  rewrite 4 (eq_trans_map_distr F) in H.
  now rewrite <- eq_trans_assoc in H.
Defined.

(** The presheaf exchange hexagon in the form the fibre of a restriction-frame
    coherence needs: its three erasures are [q0 >= r0 >= p0] where the two
    outer ones are the shifted dimensions the construction indexes by, so
    every edge but [GFaceCoh2]'s own is conjugated by a dimension-irrelevance
    path. Two naturality squares and the bounded-index comparison square
    paste these corrections onto [psh.(GFaceCoh2)]. *)

Lemma pshFaceCoh2Paste {m} {q0 r0 p0: nat}
  (HQ: q0 <= m) (HR: r0 <= q0) (HS: p0 <= r0)
  {qq rr: nat} (e1: q0.+1 = qq) (e2: r0.+1 = rr) (e3: q0.+2 = qq.+1)
  (Hqq: qq <= m.+1) (Hrr: rr <= qq) (Hrr1: rr <= m.+1)
  (ε ω ζ: arity) (d: psh.(G0) m.+3):
  f_equal (psh.(GFace) m q0 HQ ε)
    (psh.(GFaceCoh) m.+1 r0 (HR ↕ ↑ HQ) p0 HS ω ζ d
     • eq_sym (f_equal (psh.(GFace) m.+1 p0 (HS ↕ (HR ↕ ↑ HQ)) ζ)
         (pshFaceDimIrr (eq_sym e2) (Hq := ↑ Hrr1) (Hq' := ⇑ (HR ↕ ↑ HQ)) ω d)))
  • ((psh.(GFaceCoh) m q0 HQ p0 (HS ↕ HR) ε ζ (psh.(GFace) m.+2 rr (↑ Hrr1) ω d)
      • eq_sym (f_equal (psh.(GFace) m p0 (HS ↕ (HR ↕ HQ)) ζ)
          (pshFaceDimIrr (eq_sym e1) (Hq := Hqq) (Hq' := ⇑ HQ) ε
             (psh.(GFace) m.+2 rr (↑ Hrr1) ω d))))
     • f_equal (psh.(GFace) m p0 (HS ↕ (HR ↕ HQ)) ζ)
         (psh.(GFaceCoh) m.+1 qq Hqq rr Hrr ε ω d))
  = psh.(GFaceCoh) m q0 HQ r0 HR ε ω
      (psh.(GFace) m.+2 p0 (↑ (↑ (HS ↕ (HR ↕ HQ)))) ζ d)
    • (f_equal (psh.(GFace) m r0 (HR ↕ HQ) ω)
         (psh.(GFaceCoh) m.+1 q0.+1 (⇑ HQ) p0 (↑ (HS ↕ HR)) ε ζ d
          • eq_sym (f_equal (psh.(GFace) m.+1 p0 (HS ↕ (HR ↕ ↑ HQ)) ζ)
              (pshFaceDimIrr (eq_sym e3) (Hq := ⇑ Hqq) (Hq' := ⇑ (⇑ HQ)) ε d)))
       • (psh.(GFaceCoh) m r0 (HR ↕ HQ) p0 HS ω ζ
            (psh.(GFace) m.+2 qq.+1 (⇑ Hqq) ε d)
          • eq_sym (f_equal (psh.(GFace) m p0 (HS ↕ (HR ↕ HQ)) ζ)
              (pshFaceDimIrr (eq_sym e2) (Hq := Hrr1) (Hq' := ⇑ (HR ↕ HQ)) ω
                 (psh.(GFace) m.+2 qq.+1 (⇑ Hqq) ε d))))).
Proof.
  rewrite (natUIP (eq_sym e3) (f_equal S (eq_sym e1))).
  pose (aR := pshFaceDimIrr (eq_sym e2)
    (Hq := ↑ Hrr1) (Hq' := ⇑ (HR ↕ ↑ HQ)) ω d).
  pose (aQ2 := pshFaceDimIrr (f_equal S (eq_sym e1))
    (Hq := ⇑ Hqq) (Hq' := ⇑ (⇑ HQ)) ε d).
  pose proof (f_equal_naturality
    (psh.(GFace) m.+1 p0 (HS ↕ (HR ↕ ↑ HQ)) ζ)
    (psh.(GFace) m.+1 q0.+1 (⇑ HQ) ε)
    (psh.(GFace) m q0 HQ ε) (psh.(GFace) m p0 (HS ↕ (HR ↕ HQ)) ζ)
    (psh.(GFaceCoh) m q0 HQ p0 (HS ↕ HR) ε ζ) aR) as HB.
  pose proof (f_equal_naturality
    (psh.(GFace) m.+1 p0 (HS ↕ (HR ↕ ↑ HQ)) ζ)
    (psh.(GFace) m.+1 r0.+1 (⇑ (HR ↕ HQ)) ω)
    (psh.(GFace) m r0 (HR ↕ HQ) ω) (psh.(GFace) m p0 (HS ↕ (HR ↕ HQ)) ζ)
    (psh.(GFaceCoh) m r0 (HR ↕ HQ) p0 HS ω ζ) aQ2) as HF.
  pose proof (pshFaceCohDimIrr_map (eq_sym e1) (eq_sym e2)
    (Hq := Hqq) (Hq' := ⇑ HQ) (Hr := Hrr) (Hr' := ⇑ HR) ε ω d
    (psh.(GFace) m p0 (HS ↕ (HR ↕ HQ)) ζ)) as HC.
  rewrite (eq_trans_map_distr (psh.(GFace) m q0 HQ ε)),
    (eq_trans_map_distr (psh.(GFace) m r0 (HR ↕ HQ) ω)).
  rewrite <- 2 eq_sym_map_distr.
  now exact (hex_paste_side_cells _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HB HF (HC • eq_trans_assoc _ _ _)
    (psh.(GFaceCoh2) m q0 HQ r0 HR p0 HS ε ω ζ d)).
Defined.

(** Componentwise form of the dependent part of a path obtained by
    applying a map into a frame sigma type. *)
Lemma nth_dpath_f_equal_dep_sigT {A T: Type} {Bd: T -> arity -> HGpd}
  (f: A -> T) (g: forall a, Layer (Bd (f a)))
  {x y: A} (e: x = y) (zeta: arity):
  nth_dpath (Bd := Bd) (f_equal_dep_sigT f g e) zeta =
  f_equal_dep_sigT f (fun a => nth (g a) zeta) e.
Proof.
  destruct e.
  now reflexivity.
Defined.

(** The restr-painting coherence: the top presheaf painting at a face is,
    up to the restr coherence of the frames, the restr painting of the
    presheaf painting one level up (the data corresponding to
    [mkRestrPaintingType]). *)

Definition mkPshRestrPaintingType {m p k} (P: PshDepsRestr m p.+1 k)
  {X: DepsRestrExtension p.+1 k P.(_pdeps)} (PX: PshDepsExtension m P X)
  (restrPaintings: mkRestrPaintingTypes X): Type :=
  forall q (Hq: q <= k) (Hqp: q + p <= m) (ε: arity) (d: psh.(G0) m.+1),
  rew [P.(_pdeps).(_paintings).2] P.(_pshRestrs).2 q Hq Hqp ε d in
    P.(_pshPaintings).2 (psh.(GFace) m (q + p) Hqp ε d) =
  restrPaintings.2 q Hq ε (mkPshFrame (proj1PshDepsRestr P) d)
    (mkPshPainting (AddPshDep P PX) d).

Fixpoint mkPshRestrPaintingTypes {m p k}:
  forall (P: PshDepsRestr m p k) {X: DepsRestrExtension p k P.(_pdeps)}
    (PX: PshDepsExtension m P X)
    (restrPaintings: mkRestrPaintingTypes X), Type :=
  match p return forall (P: PshDepsRestr m p k)
    (X: DepsRestrExtension p k P.(_pdeps)) (PX: PshDepsExtension m P X)
    (restrPaintings: mkRestrPaintingTypes X), Type with
  | 0 => fun _ _ _ _ => unit
  | S p => fun P X PX restrPaintings =>
      { _: mkPshRestrPaintingTypes (proj1PshDepsRestr P) (AddPshDep P PX)
             restrPaintings.1 &T
        mkPshRestrPaintingType P PX restrPaintings }
  end.

(** The presheaf-equipped [DepsCohs] *)

Class PshDepsCohs (m p k: nat) := {
  _pshDeps: PshDepsRestr m p k;
  _pExtraDeps: DepsRestrExtension p k _pshDeps.(_pdeps);
  _pshExtraDeps: PshDepsExtension m _pshDeps _pExtraDeps;
  _pRestrPaintings: mkRestrPaintingTypes _pExtraDeps;
  _pshRestrPaintings: mkPshRestrPaintingTypes _pshDeps _pshExtraDeps
    _pRestrPaintings;
  _pCohs: mkCohFrameTypes _pRestrPaintings;
}.

Definition pshDepsCohs {m p k} (PC: PshDepsCohs m p k): DepsCohs p k := {|
  _deps := PC.(_pshDeps).(_pdeps);
  _extraDeps := PC.(_pExtraDeps);
  _restrPaintings := PC.(_pRestrPaintings);
  _cohs := PC.(_pCohs);
|}.

#[local]
Instance proj1PshDepsCohs {m p k} (PC: PshDepsCohs m p.+1 k):
  PshDepsCohs m p k.+1 := {|
  _pshDeps := proj1PshDepsRestr PC.(_pshDeps);
  _pExtraDeps := (PC.(_pshDeps).(_pdeps); PC.(_pExtraDeps))%extradepsrestr;
  _pshExtraDeps := AddPshDep PC.(_pshDeps) PC.(_pshExtraDeps);
  _pRestrPaintings := PC.(_pRestrPaintings).1;
  _pshRestrPaintings := PC.(_pshRestrPaintings).1;
  _pCohs := PC.(_pCohs).1;
|}.

(** The next-level restr coherences to be built (the [_pshRestrs] field of
    the next-level [PshDepsRestr]), and the next-level frame maps *)

Definition mkPshRestrFramesType {m p k} (PC: PshDepsCohs m p k): Type :=
  (mkPshRestrTypesAndFrames m.+1 (⇑ PC.(_pshDeps).(_pshBound))
    (mkPshFrames PC.(_pshDeps))
    (mkPshPaintings PC.(_pshExtraDeps))).(PshRestrTypesDef)
  (mkRestrFrames (depsCohs := pshDepsCohs PC)).

Definition mkPshFramesNext {m p k} (PC: PshDepsCohs m p k)
  (Q: mkPshRestrFramesType PC):
  mkPshFrameTypes m.+2 (mkFrames (mkDepsRestr (depsCohs := pshDepsCohs PC))) :=
  (mkPshRestrTypesAndFrames m.+1 (⇑ PC.(_pshDeps).(_pshBound))
    (mkPshFrames PC.(_pshDeps))
    (mkPshPaintings PC.(_pshExtraDeps))).(PshFramesDef) Q.

(** The 2-dimensional frame coherence needed to restrict a presheaf layer.

    For set-valued presheaves this equation follows from UIP.  At the
    groupoid level it is data: it compares the image of the presheaf exchange
    path with the exchange path already stored in the indexed prefix.  It is
    the local form in which [GFaceCoh2] is consumed by the construction. *)

Definition mkPshRestrLayerCohType {m p k}
  (PC: PshDepsCohs m p.+1 k)
  (Q: mkPshRestrFramesType (proj1PshDepsCohs PC)): Type :=
  forall q (Hq: q <= k) r (Hr: r <= q) (Hqp: q.+1 + p <= m.+1)
    (ε ω: arity) (d: psh.(G0) m.+2),
  f_equal PC.(_pshDeps).(_pshFrames).2
    (psh.(GFaceCoh) m (q + p) (⇓ Hqp) (r + p)
      (leR_add_mono_r Hr p) ε ω d)
  • (PC.(_pshDeps).(_pshRestrs).2 r (Hr ↕ Hq)
       (leR_add_mono_r Hr p ↕ (⇓ Hqp)) ω
       (psh.(GFace) m.+1 (q.+1 + p) Hqp ε d)
  • f_equal (PC.(_pshDeps).(_pdeps).(_restrFrames).2 r (Hr ↕ Hq) ω)
      (Q.2 q.+1 (⇑ Hq) Hqp ε d)) =
  PC.(_pshDeps).(_pshRestrs).2 q Hq (⇓ Hqp) ε
    (psh.(GFace) m.+1 (r + p)
      (↑ (leR_add_mono_r Hr p ↕ (⇓ Hqp))) ω d)
  • (f_equal (PC.(_pshDeps).(_pdeps).(_restrFrames).2 q Hq ε)
      (Q.2 r (↑ (Hr ↕ Hq))
        (↑ (leR_add_mono_r Hr p ↕ (⇓ Hqp))) ω d)
  • PC.(_pCohs).2 q Hq r Hr ε ω
      ((mkPshFramesNext (proj1PshDepsCohs PC) Q).2 d).1).

(** The two endpoint corrections of the layer comparison, named so that every
    presentation of that comparison is built from the same terms.

    Both chains below — the one over [Q.2 q.+1 …] and the one over the
    composite base of the frame step — need these corrections.  If each left
    them as its own [unshelve refine] hole, the two would be different
    [eq_ind_r] terms of the same type, and the [HGpd] structure does not identify arbitrary
    paths between the same points; sharing them is what makes the two chains comparable.
    [mkPshRestrLayerChainL] therefore carries the dimension-irrelevance path
    [e] as a parameter and is proved by destructing it; at [e := eq_refl] its
    statement is definitionally the uncorrected one. *)

Lemma mkPshRestrLayerChainL {m p k} (PC: PshDepsCohs m p.+1 k)
  q {qq} (e: q.+1 + p = qq) (Hqq: qq <= m.+1) (Hqp: q.+1 + p <= m.+1)
  (ε: arity) (d: psh.(G0) m.+2) (ω: arity):
  nth (mkPshLayer PC.(_pshDeps).(_pshPaintings) PC.(_pshDeps).(_pshRestrs)
        (⇓ PC.(_pshDeps).(_pshBound)) (psh.(GFace) m.+1 qq Hqq ε d)) ω
  = rew [fun x : PC.(_pshDeps).(_pdeps).(_frames).2 =>
         PC.(_pshDeps).(_pdeps).(_paintings).2 x]
      PC.(_pshDeps).(_pshRestrs).2 0 leR_O (⇓ PC.(_pshDeps).(_pshBound)) ω
        (psh.(GFace) m.+1 qq Hqq ε d) in
    rew [fun mm : psh.(G0) m =>
         PC.(_pshDeps).(_pdeps).(_paintings).2
           (PC.(_pshDeps).(_pshFrames).2 mm)]
      (psh.(GFaceCoh) m (q + p) (⇓ Hqp) p (leR_add_l q) ε ω d
       • eq_sym (f_equal (psh.(GFace) m p (⇓ PC.(_pshDeps).(_pshBound)) ω)
           (pshFaceDimIrr (eq_sym e) (Hq := Hqq) (Hq' := Hqp) ε d))) in
    PC.(_pshDeps).(_pshPaintings).2
      (psh.(GFace) m (q + p) (⇓ Hqp) ε
        (psh.(GFace) m.+1 p (leR_add_l q ↕ ↑ (⇓ Hqp)) ω d)).
Proof.
  now exact (nth_mkPshFrame PC.(_pshDeps) (psh.(GFace) m.+1 qq Hqq ε d) ω
    • f_equal (fun x => rew [fun x0 : PC.(_pshDeps).(_pdeps).(_frames).2 =>
                             PC.(_pshDeps).(_pdeps).(_paintings).2 x0]
                 PC.(_pshDeps).(_pshRestrs).2 0 leR_O
                   (⇓ PC.(_pshDeps).(_pshBound)) ω
                   (psh.(GFace) m.+1 qq Hqq ε d) in x)
        (eq_sym (f_equal_dep
           (fun mm : psh.(G0) m =>
              PC.(_pshDeps).(_pdeps).(_paintings).2
                (PC.(_pshDeps).(_pshFrames).2 mm))
           PC.(_pshDeps).(_pshPaintings).2
           (psh.(GFaceCoh) m (q + p) (⇓ Hqp) p (leR_add_l q) ε ω d
            • eq_sym (f_equal
                (psh.(GFace) m p (⇓ PC.(_pshDeps).(_pshBound)) ω)
                (pshFaceDimIrr (eq_sym e) (Hq := Hqq) (Hq' := Hqp) ε d)))))).
Defined.

(** The next-level presheaf-equipped [DepsRestr] determined by a stage and a
    choice of restriction-frame paths, without going through the coherence
    data that determines the latter.  It names the object whose frames the
    frame step's target lives in, so that [nth_mkPshFrame] can be used at that
    level. *)

Definition pshDepsRestrNext {m p k} (PC: PshDepsCohs m p k)
  (Q: mkPshRestrFramesType PC): PshDepsRestr m.+1 p.+1 k := {|
  _pdeps := mkDepsRestr (depsCohs := pshDepsCohs PC);
  _pshBound := ⇑ PC.(_pshDeps).(_pshBound);
  _pshFrames := mkPshFrames PC.(_pshDeps);
  _pshPaintings := mkPshPaintings PC.(_pshExtraDeps);
  _pshRestrs := Q;
|}.

Lemma mkPshRestrLayerChainRmap {m p k} (PC: PshDepsCohs m p.+1 k)
  (Q: mkPshRestrFramesType (proj1PshDepsCohs PC))
  q (Hq: q <= k) (ε: arity) (d: psh.(G0) m.+2) (ω: arity):
  nth (mkRestrLayer PC.(_pRestrPaintings).2 PC.(_pCohs).2 q Hq ε
        ((mkPshFramesNext (proj1PshDepsCohs PC) Q).2 d).1
        ((mkPshFramesNext (proj1PshDepsCohs PC) Q).2 d).2) ω
  = rew [fun x : PC.(_pshDeps).(_pdeps).(_frames).2 =>
         PC.(_pshDeps).(_pdeps).(_paintings).2 x]
      PC.(_pCohs).2 q Hq 0 leR_O ε ω
        ((mkPshFramesNext (proj1PshDepsCohs PC) Q).2 d).1 in
    PC.(_pRestrPaintings).2 q Hq ε
      (mkRestrFrames.2 0 leR_O ω
        (((mkPshRestrTypesAndFrames m.+1
             (↓ (⇑ (proj1PshDepsCohs PC).(_pshDeps).(_pshBound)))
             (mkPshFrames (proj1PshDepsCohs PC).(_pshDeps)).1
             (mkPshPaintings (proj1PshDepsCohs PC).(_pshExtraDeps)).1)
          .(PshFramesDef) Q.1).2 d))
      (nth ((mkPshFramesNext (proj1PshDepsCohs PC) Q).2 d).2 ω).
Proof.
  unfold mkRestrLayer. now exact (nth_lmap _ _ ω).
Defined.

(** The stored coherence [HC] at [r = 0] read over the composite base that
    also carries the dimension-irrelevance path.

    [HC] pins every slot of a [rew_cohLayer_hex] core: its [C2] is the bare
    [GFaceCoh], its [C1] sits at the [q.+1 + p] indexing and its [E1] is
    [Q.2 q.+1 …] alone.  A core over the composite base therefore cannot reuse
    [HC] directly; this is [HC] pasted with the naturality square of the
    dimension-irrelevance path, obtained by abstracting that path and
    destructing it. *)

Lemma mkPshRestrLayerFrameSquare {m p k} (PC: PshDepsCohs m p.+1 k)
  (Q: mkPshRestrFramesType (proj1PshDepsCohs PC))
  (HC: mkPshRestrLayerCohType PC Q)
  q (Hq: q <= k) {qq} (e: q.+1 + p = qq)
  (Hqq: qq <= m.+1) (Hqp: q.+1 + p <= m.+1)
  (ε: arity) (d: psh.(G0) m.+2) (ζ: arity):
  f_equal PC.(_pshDeps).(_pshFrames).2
    (psh.(GFaceCoh) m (q + p) (⇓ Hqp) p (leR_add_l q) ε ζ d
     • eq_sym (f_equal (psh.(GFace) m p (⇓ PC.(_pshDeps).(_pshBound)) ζ)
         (pshFaceDimIrr (eq_sym e) (Hq := Hqq) (Hq' := Hqp) ε d)))
  • (PC.(_pshDeps).(_pshRestrs).2 0 leR_O (⇓ PC.(_pshDeps).(_pshBound)) ζ
       (psh.(GFace) m.+1 qq Hqq ε d)
     • f_equal (PC.(_pshDeps).(_pdeps).(_restrFrames).2 0 leR_O ζ)
         (f_equal (fun a => (mkPshFrame PC.(_pshDeps) a).1)
            (pshFaceDimIrr (eq_sym e) (Hq := Hqq) (Hq' := Hqp) ε d)
          • Q.2 q.+1 (⇑ Hq) Hqp ε d))
  = PC.(_pshDeps).(_pshRestrs).2 q Hq (⇓ Hqp) ε
      (psh.(GFace) m.+1 (0 + p)
        (↑ (leR_add_mono_r leR_O p ↕ ⇓ Hqp)) ζ d)
    • (f_equal (PC.(_pshDeps).(_pdeps).(_restrFrames).2 q Hq ε)
        (Q.2 0 (↑ (leR_O ↕ Hq))
          (↑ (leR_add_mono_r leR_O p ↕ ⇓ Hqp)) ζ d)
       • PC.(_pCohs).2 q Hq 0 leR_O ε ζ
           ((mkPshFramesNext (proj1PshDepsCohs PC) Q).2 d).1).
Proof.
  destruct e.
  cbn [pshFaceDimIrr f_equal eq_sym eq_trans].
  rewrite eq_trans_refl_l.
  now exact (HC q Hq 0 leR_O Hqp ε ζ d).
Defined.

(** The [ω]-component of the layer comparison.  The proof term is deliberately
    kept in the shape [correction • (core • correction)], with the core a
    [rew_cohLayer_hex] instance.  Coherences one level up consume this normal
    form: they need the core to be visible and treat the two endpoint
    corrections as opaque conjugation data.

    The core's target-side fibre map is the restriction painting
    [_pRestrPaintings.2 q Hq ε] rather than the identity, so that its
    painting premise is the stored comparison [_pshRestrPaintings.2] and its
    2-dimensional premise the stored coherence [HC] at [r = 0].  This is
    forced: a fused hexagon one level up shares that fibre map between the
    edge built here and the edge coming from [mkCohLayer], and the latter
    pins it to [_pRestrPaintings.2].  It also explains why
    [_pshRestrPaintings] is stored at all — with the identity there instead,
    that comparison would have to be hidden inside an endpoint correction.

    The comparison is stated over the transported layer component rather than
    over the layer itself, so that it is already the composite [nth_dpath]
    returns: [mkPshRestrLayerPoint] below prefixes it with the [nth_rew] that
    [nth_dpath] then cancels, exactly as [lmap2_chain] does for
    [nth_dpath_lmap2_chain]. *)

(** The layer comparison's five-factor chain, generic in its **base path** [b]
    and in the 2-dimensional premise [Hsq] stated over that [b].

    Both presentations of the frame step instantiate this: the plain one at
    [b := Q.2 q.+1 …] with [Hsq := HC …], the merged one at
    [b := f_equal Fr1 (pshFaceDimIrr …) • Q.2 q.+1 …] with [Hsq] the
    corresponding square.  Keeping [b] and [Hsq] in argument position is what
    makes the two comparable: the difference between the two instantiations is
    then a difference between arguments, where [eq_trans_refl_l] can act, rather
    than one buried inside a transport. *)

Lemma mkPshRestrLayerChainB {m p k} (PC: PshDepsCohs m p.+1 k)
  (Q: mkPshRestrFramesType (proj1PshDepsCohs PC))
  q (Hq: q <= k) {qq} (e: q.+1 + p = qq) (Hqq: qq <= m.+1)
  (Hqp: q.+1 + p <= m.+1) (ε: arity)
  (d: psh.(G0) m.+2) (ζ: arity)
  (b: (mkPshFrame PC.(_pshDeps) (psh.(GFace) m.+1 qq Hqq ε d)).1
      = mkRestrFrames.2 q.+1 (⇑ Hq) ε
          (((mkPshRestrTypesAndFrames m.+1
               (↓ (⇑ (proj1PshDepsCohs PC).(_pshDeps).(_pshBound)))
               (mkPshFrames (proj1PshDepsCohs PC).(_pshDeps)).1
               (mkPshPaintings (proj1PshDepsCohs PC).(_pshExtraDeps)).1)
            .(PshFramesDef) Q.1).2 d))
  (Hsq: f_equal PC.(_pshDeps).(_pshFrames).2
     (psh.(GFaceCoh) m (q + p) (⇓ Hqp) p (leR_add_l q) ε ζ d
      • eq_sym (f_equal (psh.(GFace) m p (⇓ PC.(_pshDeps).(_pshBound)) ζ)
          (pshFaceDimIrr (eq_sym e) (Hq := Hqq) (Hq' := Hqp) ε d)))
   • (PC.(_pshDeps).(_pshRestrs).2 0 leR_O
        (⇓ PC.(_pshDeps).(_pshBound)) ζ (psh.(GFace) m.+1 qq Hqq ε d)
      • f_equal (PC.(_pshDeps).(_pdeps).(_restrFrames).2 0 leR_O ζ) b)
   = PC.(_pshDeps).(_pshRestrs).2 q Hq (⇓ Hqp) ε
       (psh.(GFace) m.+1 (0 + p)
         (↑ (leR_add_mono_r leR_O p ↕ ⇓ Hqp)) ζ d)
     • (f_equal (PC.(_pshDeps).(_pdeps).(_restrFrames).2 q Hq ε)
         (Q.2 0 (↑ (leR_O ↕ Hq))
           (↑ (leR_add_mono_r leR_O p ↕ ⇓ Hqp)) ζ d)
        • PC.(_pCohs).2 q Hq 0 leR_O ε ζ
            ((mkPshFramesNext (proj1PshDepsCohs PC) Q).2 d).1)):
  rew [fun a => PC.(_pshDeps).(_pdeps).(_paintings).2
        (PC.(_pshDeps).(_pdeps).(_restrFrames).2 0 leR_O ζ a)]
      b in
    nth (mkPshLayer PC.(_pshDeps).(_pshPaintings) PC.(_pshDeps).(_pshRestrs)
      (⇓ PC.(_pshDeps).(_pshBound))
      (psh.(GFace) m.+1 qq Hqq ε d)) ζ
  = nth (mkRestrLayer PC.(_pRestrPaintings).2 PC.(_pCohs).2 q Hq ε
      ((mkPshFramesNext (proj1PshDepsCohs PC) Q).2 d).1
      ((mkPshFramesNext (proj1PshDepsCohs PC) Q).2 d).2) ζ.
Proof.
  unshelve refine (f_equal (fun x => rew [fun a =>
      PC.(_pshDeps).(_pdeps).(_paintings).2
        (PC.(_pshDeps).(_pdeps).(_restrFrames).2 0 leR_O ζ a)]
      b in x) _
    • (eq_refl • ((rew_cohLayer_hex
    (P := fun x => PC.(_pshDeps).(_pdeps).(_paintings).2 x)
    (rf0 := fun x => PC.(_pshDeps).(_pdeps).(_restrFrames).2 0 leR_O ζ x)
    (rfF := fun x => PC.(_pshDeps).(_pshFrames).2 x)
    (rfG := fun x => PC.(_pshDeps).(_pdeps).(_restrFrames).2 q Hq ε x)
    (S2 := fun mm => PC.(_pshDeps).(_pdeps).(_paintings).2
      (PC.(_pshDeps).(_pshFrames).2 mm))
    (S3 := fun nn =>
      (mkPaintings (PC.(_pshDeps).(_pdeps); PC.(_pExtraDeps))).2 nn)
    (F := fun _ a => a)
    (G := PC.(_pRestrPaintings).2 q Hq ε)
    (E1 := b)
    (C2 := psh.(GFaceCoh) m (q + p) (⇓ Hqp) p
             (leR_add_l q) ε ζ d
           • eq_sym (f_equal
               (psh.(GFace) m p (⇓ PC.(_pshDeps).(_pshBound)) ζ)
               (pshFaceDimIrr (eq_sym e) (Hq := Hqq) (Hq' := Hqp) ε d)))
    (D2 := Q.2 0 leR_O
      (⇓ (⇑ (proj1PshDepsCohs PC).(_pshDeps).(_pshBound))) ζ d)
    (C1 := PC.(_pshDeps).(_pshRestrs).2 0 leR_O
      (⇓ PC.(_pshDeps).(_pshBound)) ζ
      (psh.(GFace) m.+1 qq Hqq ε d))
    (D1 := PC.(_pCohs).2 q Hq 0 leR_O ε ζ
      ((mkPshFramesNext (proj1PshDepsCohs PC) Q).2 d).1)
    (K := PC.(_pshDeps).(_pshRestrs).2 q Hq (⇓ Hqp) ε
      (psh.(GFace) m.+1 p
        (⇓ (⇑ (proj1PshDepsCohs PC).(_pshDeps).(_pshBound))) ζ d))
    (aL := PC.(_pshDeps).(_pshPaintings).2
      (psh.(GFace) m (q + p) (⇓ Hqp) ε
        (psh.(GFace) m.+1 p
          (leR_add_l q ↕ ↑ (⇓ Hqp)) ζ d)))
    (PC.(_pshRestrPaintings).2 q Hq (⇓ Hqp) ε
      (psh.(GFace) m.+1 p
        (⇓ (⇑ (proj1PshDepsCohs PC).(_pshDeps).(_pshBound))) ζ d))
    Hsq)
  • (eq_sym (f_equal (fun x : (mkPaintings
         (PC.(_pshDeps).(_pdeps); PC.(_pExtraDeps))).2
         (mkRestrFrames.2 0 leR_O ζ
           (((mkPshRestrTypesAndFrames m.+1
                (↓ (⇑ (proj1PshDepsCohs PC).(_pshDeps).(_pshBound)))
                (mkPshFrames (proj1PshDepsCohs PC).(_pshDeps)).1
                (mkPshPaintings (proj1PshDepsCohs PC).(_pshExtraDeps)).1)
             .(PshFramesDef) Q.1).2 d)) =>
       rew [fun x0 : PC.(_pshDeps).(_pdeps).(_frames).2 =>
            PC.(_pshDeps).(_pdeps).(_paintings).2 x0]
         PC.(_pCohs).2 q Hq 0 leR_O ε ζ
           ((mkPshFramesNext (proj1PshDepsCohs PC) Q).2 d).1 in
       PC.(_pRestrPaintings).2 q Hq ε _ x)
       (nth_mkPshFrame (pshDepsRestrNext (proj1PshDepsCohs PC) Q) d ζ))
     • eq_sym (mkPshRestrLayerChainRmap PC Q q Hq ε d ζ))))).
  now exact (mkPshRestrLayerChainL PC q e Hqq Hqp ε d ζ).
Defined.

(** The same five-factor chain with its core in the section presentation of
    [rew_cohLayer_hex_sec], i.e. with [unit] as the level-2 family and the
    presheaf painting as the core's source fibre map.  A fused layer coherence
    shares its level-2 family between the presheaf edge and the two
    restriction edges; the stored restriction-painting coherences force that
    family to be [unit], so the chains sitting in the level-1 slots must be
    read this way, while the ones in the top-level slots keep the presentation
    above. *)

Lemma mkPshRestrLayerChainBsec {m p k} (PC: PshDepsCohs m p.+1 k)
  (Q: mkPshRestrFramesType (proj1PshDepsCohs PC))
  q (Hq: q <= k) {qq} (e: q.+1 + p = qq) (Hqq: qq <= m.+1)
  (Hqp: q.+1 + p <= m.+1) (ε: arity)
  (d: psh.(G0) m.+2) (ζ: arity)
  (b: (mkPshFrame PC.(_pshDeps) (psh.(GFace) m.+1 qq Hqq ε d)).1
      = mkRestrFrames.2 q.+1 (⇑ Hq) ε
          (((mkPshRestrTypesAndFrames m.+1
               (↓ (⇑ (proj1PshDepsCohs PC).(_pshDeps).(_pshBound)))
               (mkPshFrames (proj1PshDepsCohs PC).(_pshDeps)).1
               (mkPshPaintings (proj1PshDepsCohs PC).(_pshExtraDeps)).1)
            .(PshFramesDef) Q.1).2 d))
  (Hsq: f_equal PC.(_pshDeps).(_pshFrames).2
     (psh.(GFaceCoh) m (q + p) (⇓ Hqp) p (leR_add_l q) ε ζ d
      • eq_sym (f_equal (psh.(GFace) m p (⇓ PC.(_pshDeps).(_pshBound)) ζ)
          (pshFaceDimIrr (eq_sym e) (Hq := Hqq) (Hq' := Hqp) ε d)))
   • (PC.(_pshDeps).(_pshRestrs).2 0 leR_O
        (⇓ PC.(_pshDeps).(_pshBound)) ζ (psh.(GFace) m.+1 qq Hqq ε d)
      • f_equal (PC.(_pshDeps).(_pdeps).(_restrFrames).2 0 leR_O ζ) b)
   = PC.(_pshDeps).(_pshRestrs).2 q Hq (⇓ Hqp) ε
       (psh.(GFace) m.+1 (0 + p)
         (↑ (leR_add_mono_r leR_O p ↕ ⇓ Hqp)) ζ d)
     • (f_equal (PC.(_pshDeps).(_pdeps).(_restrFrames).2 q Hq ε)
         (Q.2 0 (↑ (leR_O ↕ Hq))
           (↑ (leR_add_mono_r leR_O p ↕ ⇓ Hqp)) ζ d)
        • PC.(_pCohs).2 q Hq 0 leR_O ε ζ
            ((mkPshFramesNext (proj1PshDepsCohs PC) Q).2 d).1)):
  rew [fun a => PC.(_pshDeps).(_pdeps).(_paintings).2
        (PC.(_pshDeps).(_pdeps).(_restrFrames).2 0 leR_O ζ a)]
      b in
    nth (mkPshLayer PC.(_pshDeps).(_pshPaintings) PC.(_pshDeps).(_pshRestrs)
      (⇓ PC.(_pshDeps).(_pshBound))
      (psh.(GFace) m.+1 qq Hqq ε d)) ζ
  = nth (mkRestrLayer PC.(_pRestrPaintings).2 PC.(_pCohs).2 q Hq ε
      ((mkPshFramesNext (proj1PshDepsCohs PC) Q).2 d).1
      ((mkPshFramesNext (proj1PshDepsCohs PC) Q).2 d).2) ζ.
Proof.
  unshelve refine (f_equal (fun x => rew [fun a =>
      PC.(_pshDeps).(_pdeps).(_paintings).2
        (PC.(_pshDeps).(_pdeps).(_restrFrames).2 0 leR_O ζ a)]
      b in x) _
    • (eq_refl • ((rew_cohLayer_hex
    (P := fun x => PC.(_pshDeps).(_pdeps).(_paintings).2 x)
    (rf0 := fun x => PC.(_pshDeps).(_pdeps).(_restrFrames).2 0 leR_O ζ x)
    (rfF := fun x => PC.(_pshDeps).(_pshFrames).2 x)
    (rfG := fun x => PC.(_pshDeps).(_pdeps).(_restrFrames).2 q Hq ε x)
    (S2 := fun _: psh.(G0) m => unit)
    (S3 := fun nn =>
      (mkPaintings (PC.(_pshDeps).(_pdeps); PC.(_pExtraDeps))).2 nn)
    (F := fun (z: psh.(G0) m) (_: unit) =>
      PC.(_pshDeps).(_pshPaintings).2 z)
    (G := PC.(_pRestrPaintings).2 q Hq ε)
    (E1 := b)
    (C2 := psh.(GFaceCoh) m (q + p) (⇓ Hqp) p
             (leR_add_l q) ε ζ d
           • eq_sym (f_equal
               (psh.(GFace) m p (⇓ PC.(_pshDeps).(_pshBound)) ζ)
               (pshFaceDimIrr (eq_sym e) (Hq := Hqq) (Hq' := Hqp) ε d)))
    (D2 := Q.2 0 leR_O
      (⇓ (⇑ (proj1PshDepsCohs PC).(_pshDeps).(_pshBound))) ζ d)
    (C1 := PC.(_pshDeps).(_pshRestrs).2 0 leR_O
      (⇓ PC.(_pshDeps).(_pshBound)) ζ
      (psh.(GFace) m.+1 qq Hqq ε d))
    (D1 := PC.(_pCohs).2 q Hq 0 leR_O ε ζ
      ((mkPshFramesNext (proj1PshDepsCohs PC) Q).2 d).1)
    (K := PC.(_pshDeps).(_pshRestrs).2 q Hq (⇓ Hqp) ε
      (psh.(GFace) m.+1 p
        (⇓ (⇑ (proj1PshDepsCohs PC).(_pshDeps).(_pshBound))) ζ d))
    (aL := tt)
    (PC.(_pshRestrPaintings).2 q Hq (⇓ Hqp) ε
      (psh.(GFace) m.+1 p
        (⇓ (⇑ (proj1PshDepsCohs PC).(_pshDeps).(_pshBound))) ζ d))
    Hsq)
  • (eq_sym (f_equal (fun x : (mkPaintings
         (PC.(_pshDeps).(_pdeps); PC.(_pExtraDeps))).2
         (mkRestrFrames.2 0 leR_O ζ
           (((mkPshRestrTypesAndFrames m.+1
                (↓ (⇑ (proj1PshDepsCohs PC).(_pshDeps).(_pshBound)))
                (mkPshFrames (proj1PshDepsCohs PC).(_pshDeps)).1
                (mkPshPaintings (proj1PshDepsCohs PC).(_pshExtraDeps)).1)
             .(PshFramesDef) Q.1).2 d)) =>
       rew [fun x0 : PC.(_pshDeps).(_pdeps).(_frames).2 =>
            PC.(_pshDeps).(_pdeps).(_paintings).2 x0]
         PC.(_pCohs).2 q Hq 0 leR_O ε ζ
           ((mkPshFramesNext (proj1PshDepsCohs PC) Q).2 d).1 in
       PC.(_pRestrPaintings).2 q Hq ε _ x)
       (nth_mkPshFrame (pshDepsRestrNext (proj1PshDepsCohs PC) Q) d ζ))
     • eq_sym (mkPshRestrLayerChainRmap PC Q q Hq ε d ζ))))).
  now exact (nth_mkPshFrame PC.(_pshDeps) (psh.(GFace) m.+1 qq Hqq ε d) ζ).
Defined.

(** The two presentations agree.  Both endpoint corrections are shared —
    [nth_mkPshFrame] and [mkPshRestrLayerChainR] — so once
    [rew_cohLayer_hex_sec] has moved the section's action out of the core, the
    two chains differ by a path and its inverse. *)

Lemma mkPshRestrLayerChainB_sec {m p k} (PC: PshDepsCohs m p.+1 k)
  (Q: mkPshRestrFramesType (proj1PshDepsCohs PC))
  q (Hq: q <= k) {qq} (e: q.+1 + p = qq) (Hqq: qq <= m.+1)
  (Hqp: q.+1 + p <= m.+1) (ε: arity) (d: psh.(G0) m.+2) (ζ: arity) b Hsq:
  mkPshRestrLayerChainB PC Q q Hq e Hqq Hqp ε d ζ b Hsq
  = mkPshRestrLayerChainBsec PC Q q Hq e Hqq Hqp ε d ζ b Hsq.
Proof.
  unfold mkPshRestrLayerChainB, mkPshRestrLayerChainBsec,
    mkPshRestrLayerChainL.
  rewrite (rew_cohLayer_hex_sec
    (P := fun x => PC.(_pshDeps).(_pdeps).(_paintings).2 x)
    (rf0 := fun x => PC.(_pshDeps).(_pdeps).(_restrFrames).2 0 leR_O ζ x)
    (rfF := fun x => PC.(_pshDeps).(_pshFrames).2 x)
    (rfG := fun x => PC.(_pshDeps).(_pdeps).(_restrFrames).2 q Hq ε x)
    PC.(_pshDeps).(_pshPaintings).2 (PC.(_pRestrPaintings).2 q Hq ε)
    b
    (psh.(GFaceCoh) m (q + p) (⇓ Hqp) p (leR_add_l q) ε ζ d
     • eq_sym (f_equal (psh.(GFace) m p (⇓ PC.(_pshDeps).(_pshBound)) ζ)
         (pshFaceDimIrr (eq_sym e) (Hq := Hqq) (Hq' := Hqp) ε d)))
    (Q.2 0 leR_O (⇓ (⇑ (proj1PshDepsCohs PC).(_pshDeps).(_pshBound))) ζ d)
    (PC.(_pshDeps).(_pshRestrs).2 0 leR_O (⇓ PC.(_pshDeps).(_pshBound)) ζ
       (psh.(GFace) m.+1 qq Hqq ε d))
    (PC.(_pCohs).2 q Hq 0 leR_O ε ζ
       ((mkPshFramesNext (proj1PshDepsCohs PC) Q).2 d).1)
    (PC.(_pshDeps).(_pshRestrs).2 q Hq (⇓ Hqp) ε
       (psh.(GFace) m.+1 p
         (⇓ (⇑ (proj1PshDepsCohs PC).(_pshDeps).(_pshBound))) ζ d))).
  rewrite eq_trans_map_distr.
  now apply (cancel_fequal_sym
    (fun x : PC.(_pshDeps).(_pdeps).(_paintings).2
         (PC.(_pshDeps).(_pdeps).(_restrFrames).2 0 leR_O ζ
            (mkPshFrame PC.(_pshDeps) (psh.(GFace) m.+1 qq Hqq ε d)).1) =>
       rew [fun a => PC.(_pshDeps).(_pdeps).(_paintings).2
              (PC.(_pshDeps).(_pdeps).(_restrFrames).2 0 leR_O ζ a)] b in x)
    (fun x : PC.(_pshDeps).(_pdeps).(_paintings).2
         (PC.(_pshDeps).(_pshFrames).2
            (psh.(GFace) m p (⇓ PC.(_pshDeps).(_pshBound)) ζ
               (psh.(GFace) m.+1 qq Hqq ε d))) =>
       rew [fun x0 : PC.(_pshDeps).(_pdeps).(_frames).2 =>
            PC.(_pshDeps).(_pdeps).(_paintings).2 x0]
         PC.(_pshDeps).(_pshRestrs).2 0 leR_O
           (⇓ PC.(_pshDeps).(_pshBound)) ζ (psh.(GFace) m.+1 qq Hqq ε d) in x)
    (f_equal_dep
      (fun mm : psh.(G0) m => PC.(_pshDeps).(_pdeps).(_paintings).2
         (PC.(_pshDeps).(_pshFrames).2 mm))
      PC.(_pshDeps).(_pshPaintings).2
      (psh.(GFaceCoh) m (q + p) (⇓ Hqp) p (leR_add_l q) ε ζ d
       • eq_sym (f_equal (psh.(GFace) m p (⇓ PC.(_pshDeps).(_pshBound)) ζ)
           (pshFaceDimIrr (eq_sym e) (Hq := Hqq) (Hq' := Hqp) ε d))))).
Defined.

(** The same five-factor chain with its left-hand correction split into its
    two halves: the [nth_mkPshFrame] comparison and the presheaf painting's
    action on the core's [C2].  A fused layer coherence keeps those two in
    consecutive slots, because the second is shared with the presheaf edge —
    it is that edge's own endpoint conjugation. *)

Lemma mkPshRestrLayerChainBsplit {m p k} (PC: PshDepsCohs m p.+1 k)
  (Q: mkPshRestrFramesType (proj1PshDepsCohs PC))
  q (Hq: q <= k) {qq} (e: q.+1 + p = qq) (Hqq: qq <= m.+1)
  (Hqp: q.+1 + p <= m.+1) (ε: arity)
  (d: psh.(G0) m.+2) (ζ: arity)
  (b: (mkPshFrame PC.(_pshDeps) (psh.(GFace) m.+1 qq Hqq ε d)).1
      = mkRestrFrames.2 q.+1 (⇑ Hq) ε
          (((mkPshRestrTypesAndFrames m.+1
               (↓ (⇑ (proj1PshDepsCohs PC).(_pshDeps).(_pshBound)))
               (mkPshFrames (proj1PshDepsCohs PC).(_pshDeps)).1
               (mkPshPaintings (proj1PshDepsCohs PC).(_pshExtraDeps)).1)
            .(PshFramesDef) Q.1).2 d))
  (Hsq: f_equal PC.(_pshDeps).(_pshFrames).2
     (psh.(GFaceCoh) m (q + p) (⇓ Hqp) p (leR_add_l q) ε ζ d
      • eq_sym (f_equal (psh.(GFace) m p (⇓ PC.(_pshDeps).(_pshBound)) ζ)
          (pshFaceDimIrr (eq_sym e) (Hq := Hqq) (Hq' := Hqp) ε d)))
   • (PC.(_pshDeps).(_pshRestrs).2 0 leR_O
        (⇓ PC.(_pshDeps).(_pshBound)) ζ (psh.(GFace) m.+1 qq Hqq ε d)
      • f_equal (PC.(_pshDeps).(_pdeps).(_restrFrames).2 0 leR_O ζ) b)
   = PC.(_pshDeps).(_pshRestrs).2 q Hq (⇓ Hqp) ε
       (psh.(GFace) m.+1 (0 + p)
         (↑ (leR_add_mono_r leR_O p ↕ ⇓ Hqp)) ζ d)
     • (f_equal (PC.(_pshDeps).(_pdeps).(_restrFrames).2 q Hq ε)
         (Q.2 0 (↑ (leR_O ↕ Hq))
           (↑ (leR_add_mono_r leR_O p ↕ ⇓ Hqp)) ζ d)
        • PC.(_pCohs).2 q Hq 0 leR_O ε ζ
            ((mkPshFramesNext (proj1PshDepsCohs PC) Q).2 d).1)):
  rew [fun a => PC.(_pshDeps).(_pdeps).(_paintings).2
        (PC.(_pshDeps).(_pdeps).(_restrFrames).2 0 leR_O ζ a)]
      b in
    nth (mkPshLayer PC.(_pshDeps).(_pshPaintings) PC.(_pshDeps).(_pshRestrs)
      (⇓ PC.(_pshDeps).(_pshBound))
      (psh.(GFace) m.+1 qq Hqq ε d)) ζ
  = nth (mkRestrLayer PC.(_pRestrPaintings).2 PC.(_pCohs).2 q Hq ε
      ((mkPshFramesNext (proj1PshDepsCohs PC) Q).2 d).1
      ((mkPshFramesNext (proj1PshDepsCohs PC) Q).2 d).2) ζ.
Proof.
  unshelve refine (f_equal (fun x => rew [fun a =>
      PC.(_pshDeps).(_pdeps).(_paintings).2
        (PC.(_pshDeps).(_pdeps).(_restrFrames).2 0 leR_O ζ a)]
      b in x)
      (nth_mkPshFrame PC.(_pshDeps) (psh.(GFace) m.+1 qq Hqq ε d) ζ)
    • (f_equal (fun x => rew [fun a =>
           PC.(_pshDeps).(_pdeps).(_paintings).2
             (PC.(_pshDeps).(_pdeps).(_restrFrames).2 0 leR_O ζ a)] b in
         rew [fun x0 : PC.(_pshDeps).(_pdeps).(_frames).2 =>
              PC.(_pshDeps).(_pdeps).(_paintings).2 x0]
           PC.(_pshDeps).(_pshRestrs).2 0 leR_O
             (⇓ PC.(_pshDeps).(_pshBound)) ζ
             (psh.(GFace) m.+1 qq Hqq ε d) in x)
        (eq_sym (f_equal_dep
           (fun mm : psh.(G0) m =>
              PC.(_pshDeps).(_pdeps).(_paintings).2
                (PC.(_pshDeps).(_pshFrames).2 mm))
           PC.(_pshDeps).(_pshPaintings).2
           (psh.(GFaceCoh) m (q + p) (⇓ Hqp) p (leR_add_l q) ε ζ d
            • eq_sym (f_equal
                (psh.(GFace) m p (⇓ PC.(_pshDeps).(_pshBound)) ζ)
                (pshFaceDimIrr (eq_sym e) (Hq := Hqq) (Hq' := Hqp) ε d)))))
    • ((rew_cohLayer_hex
    (P := fun x => PC.(_pshDeps).(_pdeps).(_paintings).2 x)
    (rf0 := fun x => PC.(_pshDeps).(_pdeps).(_restrFrames).2 0 leR_O ζ x)
    (rfF := fun x => PC.(_pshDeps).(_pshFrames).2 x)
    (rfG := fun x => PC.(_pshDeps).(_pdeps).(_restrFrames).2 q Hq ε x)
    (S2 := fun mm => PC.(_pshDeps).(_pdeps).(_paintings).2
      (PC.(_pshDeps).(_pshFrames).2 mm))
    (S3 := fun nn =>
      (mkPaintings (PC.(_pshDeps).(_pdeps); PC.(_pExtraDeps))).2 nn)
    (F := fun _ a => a)
    (G := PC.(_pRestrPaintings).2 q Hq ε)
    (E1 := b)
    (C2 := psh.(GFaceCoh) m (q + p) (⇓ Hqp) p
             (leR_add_l q) ε ζ d
           • eq_sym (f_equal
               (psh.(GFace) m p (⇓ PC.(_pshDeps).(_pshBound)) ζ)
               (pshFaceDimIrr (eq_sym e) (Hq := Hqq) (Hq' := Hqp) ε d)))
    (D2 := Q.2 0 leR_O
      (⇓ (⇑ (proj1PshDepsCohs PC).(_pshDeps).(_pshBound))) ζ d)
    (C1 := PC.(_pshDeps).(_pshRestrs).2 0 leR_O
      (⇓ PC.(_pshDeps).(_pshBound)) ζ
      (psh.(GFace) m.+1 qq Hqq ε d))
    (D1 := PC.(_pCohs).2 q Hq 0 leR_O ε ζ
      ((mkPshFramesNext (proj1PshDepsCohs PC) Q).2 d).1)
    (K := PC.(_pshDeps).(_pshRestrs).2 q Hq (⇓ Hqp) ε
      (psh.(GFace) m.+1 p
        (⇓ (⇑ (proj1PshDepsCohs PC).(_pshDeps).(_pshBound))) ζ d))
    (aL := PC.(_pshDeps).(_pshPaintings).2
      (psh.(GFace) m (q + p) (⇓ Hqp) ε
        (psh.(GFace) m.+1 p
          (leR_add_l q ↕ ↑ (⇓ Hqp)) ζ d)))
    (PC.(_pshRestrPaintings).2 q Hq (⇓ Hqp) ε
      (psh.(GFace) m.+1 p
        (⇓ (⇑ (proj1PshDepsCohs PC).(_pshDeps).(_pshBound))) ζ d))
    Hsq)
  • (eq_sym (f_equal (fun x : (mkPaintings
         (PC.(_pshDeps).(_pdeps); PC.(_pExtraDeps))).2
         (mkRestrFrames.2 0 leR_O ζ
           (((mkPshRestrTypesAndFrames m.+1
                (↓ (⇑ (proj1PshDepsCohs PC).(_pshDeps).(_pshBound)))
                (mkPshFrames (proj1PshDepsCohs PC).(_pshDeps)).1
                (mkPshPaintings (proj1PshDepsCohs PC).(_pshExtraDeps)).1)
             .(PshFramesDef) Q.1).2 d)) =>
       rew [fun x0 : PC.(_pshDeps).(_pdeps).(_frames).2 =>
            PC.(_pshDeps).(_pdeps).(_paintings).2 x0]
         PC.(_pCohs).2 q Hq 0 leR_O ε ζ
           ((mkPshFramesNext (proj1PshDepsCohs PC) Q).2 d).1 in
       PC.(_pRestrPaintings).2 q Hq ε _ x)
       (nth_mkPshFrame (pshDepsRestrNext (proj1PshDepsCohs PC) Q) d ζ))
     • eq_sym (mkPshRestrLayerChainRmap PC Q q Hq ε d ζ))))).
Defined.

(** The split presentation agrees with the plain one: the two halves are the
    two factors of [mkPshRestrLayerChainL], so this is one distribution of
    [f_equal] over a composite and one re-association. *)

Lemma mkPshRestrLayerChainB_split {m p k} (PC: PshDepsCohs m p.+1 k)
  (Q: mkPshRestrFramesType (proj1PshDepsCohs PC))
  q (Hq: q <= k) {qq} (e: q.+1 + p = qq) (Hqq: qq <= m.+1)
  (Hqp: q.+1 + p <= m.+1) (ε: arity) (d: psh.(G0) m.+2) (ζ: arity) b Hsq:
  mkPshRestrLayerChainB PC Q q Hq e Hqq Hqp ε d ζ b Hsq
  = mkPshRestrLayerChainBsplit PC Q q Hq e Hqq Hqp ε d ζ b Hsq.
Proof.
  unfold mkPshRestrLayerChainB, mkPshRestrLayerChainBsplit,
    mkPshRestrLayerChainL.
  now apply (split_fequal_assoc
    (fun x : PC.(_pshDeps).(_pdeps).(_paintings).2
         (PC.(_pshDeps).(_pdeps).(_restrFrames).2 0 leR_O ζ
            (mkPshFrame PC.(_pshDeps) (psh.(GFace) m.+1 qq Hqq ε d)).1) =>
       rew [fun a => PC.(_pshDeps).(_pdeps).(_paintings).2
              (PC.(_pshDeps).(_pdeps).(_restrFrames).2 0 leR_O ζ a)] b in x)
    (fun x : PC.(_pshDeps).(_pdeps).(_paintings).2
         (PC.(_pshDeps).(_pshFrames).2
            (psh.(GFace) m p (⇓ PC.(_pshDeps).(_pshBound)) ζ
               (psh.(GFace) m.+1 qq Hqq ε d))) =>
       rew [fun x0 : PC.(_pshDeps).(_pdeps).(_frames).2 =>
            PC.(_pshDeps).(_pdeps).(_paintings).2 x0]
         PC.(_pshDeps).(_pshRestrs).2 0 leR_O
           (⇓ PC.(_pshDeps).(_pshBound)) ζ (psh.(GFace) m.+1 qq Hqq ε d) in x)
    (nth_mkPshFrame PC.(_pshDeps) (psh.(GFace) m.+1 qq Hqq ε d) ζ)
    (eq_sym (f_equal_dep
      (fun mm : psh.(G0) m => PC.(_pshDeps).(_pdeps).(_paintings).2
         (PC.(_pshDeps).(_pshFrames).2 mm))
      PC.(_pshDeps).(_pshPaintings).2
      (psh.(GFaceCoh) m (q + p) (⇓ Hqp) p (leR_add_l q) ε ζ d
       • eq_sym (f_equal (psh.(GFace) m p (⇓ PC.(_pshDeps).(_pshBound)) ζ)
           (pshFaceDimIrr (eq_sym e) (Hq := Hqq) (Hq' := Hqp) ε d)))))).
Defined.

Lemma mkPshRestrLayerChain {m p k} (PC: PshDepsCohs m p.+1 k)
  (Q: mkPshRestrFramesType (proj1PshDepsCohs PC))
  (HC: mkPshRestrLayerCohType PC Q)
  q (Hq: q <= k) (Hqp: q.+1 + p <= m.+1) (ε: arity)
  (d: psh.(G0) m.+2) (ω: arity):
  rew [fun a => PC.(_pshDeps).(_pdeps).(_paintings).2
        (PC.(_pshDeps).(_pdeps).(_restrFrames).2 0 leR_O ω a)]
      (Q.2 q.+1 (⇑ Hq) Hqp ε d) in
    nth (mkPshLayer PC.(_pshDeps).(_pshPaintings) PC.(_pshDeps).(_pshRestrs)
      (⇓ PC.(_pshDeps).(_pshBound))
      (psh.(GFace) m.+1 (q.+1 + p) Hqp ε d)) ω
  = nth
      (mkRestrLayer PC.(_pRestrPaintings).2 PC.(_pCohs).2 q Hq ε
        ((mkPshFramesNext (proj1PshDepsCohs PC) Q).2 d).1
        ((mkPshFramesNext (proj1PshDepsCohs PC) Q).2 d).2) ω.
Proof.
  now exact (mkPshRestrLayerChainB PC Q q Hq eq_refl Hqp Hqp ε d ω
    (Q.2 q.+1 (⇑ Hq) Hqp ε d) (HC q Hq 0 leR_O Hqp ε ω d)).
Defined.

(** The component chain over the composite base of a restriction-frame step. *)

Lemma mkPshRestrLayerMergedChain {m p k} (PC: PshDepsCohs m p.+1 k)
  (Q: mkPshRestrFramesType (proj1PshDepsCohs PC))
  (HC: mkPshRestrLayerCohType PC Q)
  q (Hq: q <= k) (Hqp: q + p.+1 <= m.+1) (ε: arity)
  (d: psh.(G0) m.+2) (ζ: arity):
  rew [fun a => PC.(_pshDeps).(_pdeps).(_paintings).2
        (PC.(_pshDeps).(_pdeps).(_restrFrames).2 0 leR_O ζ a)]
      (f_equal (fun a => (mkPshFrame PC.(_pshDeps) a).1)
         (pshFaceDimIrr (eq_sym (plus_n_Sm q p))
           (Hq' := leR_add_shift Hqp) ε d)
       • Q.2 q.+1 (⇑ Hq) (leR_add_shift Hqp) ε d) in
    nth (mkPshLayer PC.(_pshDeps).(_pshPaintings) PC.(_pshDeps).(_pshRestrs)
      (⇓ PC.(_pshDeps).(_pshBound))
      (psh.(GFace) m.+1 (q + p.+1) Hqp ε d)) ζ
  = nth (mkRestrLayer PC.(_pRestrPaintings).2 PC.(_pCohs).2 q Hq ε
      ((mkPshFramesNext (proj1PshDepsCohs PC) Q).2 d).1
      ((mkPshFramesNext (proj1PshDepsCohs PC) Q).2 d).2) ζ.
Proof.
  now exact (mkPshRestrLayerChainB PC Q q Hq (plus_n_Sm q p) Hqp
    (leR_add_shift Hqp) ε d ζ
    (f_equal (fun a => (mkPshFrame PC.(_pshDeps) a).1)
       (pshFaceDimIrr (eq_sym (plus_n_Sm q p))
         (Hq' := leR_add_shift Hqp) ε d)
     • Q.2 q.+1 (⇑ Hq) (leR_add_shift Hqp) ε d)
    (mkPshRestrLayerFrameSquare PC Q HC q Hq (plus_n_Sm q p) Hqp
      (leR_add_shift Hqp) ε d ζ)).
Defined.

Lemma mkPshRestrLayer {m p k} (PC: PshDepsCohs m p.+1 k)
  (Q: mkPshRestrFramesType (proj1PshDepsCohs PC))
  (HC: mkPshRestrLayerCohType PC Q)
  q (Hq: q <= k) (Hqp: q.+1 + p <= m.+1) (ε: arity)
  (d: psh.(G0) m.+2):
  rew [mkLayer PC.(_pshDeps).(_pdeps).(_restrFrames).2]
      (Q.2 q.+1 (⇑ Hq) Hqp ε d) in
    mkPshLayer PC.(_pshDeps).(_pshPaintings) PC.(_pshDeps).(_pshRestrs)
      (⇓ PC.(_pshDeps).(_pshBound))
      (psh.(GFace) m.+1 (q.+1 + p) Hqp ε d)
  = mkRestrLayer PC.(_pRestrPaintings).2 PC.(_pCohs).2 q Hq ε
      ((mkPshFramesNext (proj1PshDepsCohs PC) Q).2 d).1
      ((mkPshFramesNext (proj1PshDepsCohs PC) Q).2 d).2.
Proof.
  now exact (layer_dpath_intro (mkPshRestrLayerChain PC Q HC q Hq Hqp ε d)).
Defined.

Lemma nth_dpath_mkPshRestrLayer {m p k} (PC: PshDepsCohs m p.+1 k)
  (Q: mkPshRestrFramesType (proj1PshDepsCohs PC))
  (HC: mkPshRestrLayerCohType PC Q)
  q (Hq: q <= k) (Hqp: q.+1 + p <= m.+1) (ε: arity)
  (d: psh.(G0) m.+2) (omega: arity):
  nth_dpath (Bd := fun a zeta =>
      PC.(_pshDeps).(_pdeps).(_paintings).2
        (PC.(_pshDeps).(_pdeps).(_restrFrames).2 0 leR_O zeta a))
    (mkPshRestrLayer PC Q HC q Hq Hqp ε d) omega =
  mkPshRestrLayerChain PC Q HC q Hq Hqp ε d omega.
Proof.
  now exact (nth_dpath_intro (mkPshRestrLayerChain PC Q HC q Hq Hqp ε d) omega).
Defined.

(** The ordinary layer path has two component presentations: split
    endpoint corrections and a core read through the section. *)

Lemma nth_dpath_mkPshRestrLayerSplit {m p k} (PC: PshDepsCohs m p.+1 k)
  (Q: mkPshRestrFramesType (proj1PshDepsCohs PC))
  (HC: mkPshRestrLayerCohType PC Q)
  q (Hq: q <= k) (Hqp: q.+1 + p <= m.+1) (ε: arity)
  (d: psh.(G0) m.+2) (ζ: arity):
  nth_dpath (Bd := fun a zeta =>
      PC.(_pshDeps).(_pdeps).(_paintings).2
        (PC.(_pshDeps).(_pdeps).(_restrFrames).2 0 leR_O zeta a))
    (mkPshRestrLayer PC Q HC q Hq Hqp ε d) ζ
  = mkPshRestrLayerChainBsplit PC Q q Hq eq_refl Hqp Hqp ε d ζ
      (Q.2 q.+1 (⇑ Hq) Hqp ε d) (HC q Hq 0 leR_O Hqp ε ζ d).
Proof.
  etransitivity.
  - now exact (nth_dpath_mkPshRestrLayer PC Q HC q Hq Hqp ε d ζ).
  - now exact (mkPshRestrLayerChainB_split PC Q q Hq eq_refl Hqp Hqp ε d ζ
      (Q.2 q.+1 (⇑ Hq) Hqp ε d) (HC q Hq 0 leR_O Hqp ε ζ d)).
Defined.

Lemma nth_dpath_mkPshRestrLayerSec {m p k} (PC: PshDepsCohs m p.+1 k)
  (Q: mkPshRestrFramesType (proj1PshDepsCohs PC))
  (HC: mkPshRestrLayerCohType PC Q)
  q (Hq: q <= k) (Hqp: q.+1 + p <= m.+1) (ε: arity)
  (d: psh.(G0) m.+2) (ζ: arity):
  nth_dpath (Bd := fun a zeta =>
      PC.(_pshDeps).(_pdeps).(_paintings).2
        (PC.(_pshDeps).(_pdeps).(_restrFrames).2 0 leR_O zeta a))
    (mkPshRestrLayer PC Q HC q Hq Hqp ε d) ζ
  = mkPshRestrLayerChainBsec PC Q q Hq eq_refl Hqp Hqp ε d ζ
      (Q.2 q.+1 (⇑ Hq) Hqp ε d) (HC q Hq 0 leR_O Hqp ε ζ d).
Proof.
  etransitivity.
  - now exact (nth_dpath_mkPshRestrLayer PC Q HC q Hq Hqp ε d ζ).
  - now exact (mkPshRestrLayerChainB_sec PC Q q Hq eq_refl Hqp Hqp ε d ζ
      (Q.2 q.+1 (⇑ Hq) Hqp ε d) (HC q Hq 0 leR_O Hqp ε ζ d)).
Defined.

(** The layer path over the composite base is constructed from the chosen
    component chains. Its component law is the evaluation rule of the
    dependent layer-path constructor. *)

Definition mkPshRestrLayerMerged {m p k} (PC: PshDepsCohs m p.+1 k)
  (Q: mkPshRestrFramesType (proj1PshDepsCohs PC))
  (HC: mkPshRestrLayerCohType PC Q)
  q (Hq: q <= k) (Hqp: q + p.+1 <= m.+1) (ε: arity)
  (d: psh.(G0) m.+2):
  rew [mkLayer PC.(_pshDeps).(_pdeps).(_restrFrames).2]
      (f_equal (fun a => (mkPshFrame PC.(_pshDeps) a).1)
         (pshFaceDimIrr (eq_sym (plus_n_Sm q p))
           (Hq' := leR_add_shift Hqp) ε d)
       • Q.2 q.+1 (⇑ Hq) (leR_add_shift Hqp) ε d) in
    mkPshLayer PC.(_pshDeps).(_pshPaintings) PC.(_pshDeps).(_pshRestrs)
      (⇓ PC.(_pshDeps).(_pshBound))
      (psh.(GFace) m.+1 (q + p.+1) Hqp ε d)
  = mkRestrLayer PC.(_pRestrPaintings).2 PC.(_pCohs).2 q Hq ε
      ((mkPshFramesNext (proj1PshDepsCohs PC) Q).2 d).1
      ((mkPshFramesNext (proj1PshDepsCohs PC) Q).2 d).2 :=
  layer_dpath_intro (mkPshRestrLayerMergedChain PC Q HC q Hq Hqp ε d).

(** Numerical reindexing of the ordinary layer comparison has the chosen
    corrected component chain. At an identity numerical path, the corrected
    square is exactly the transport of the stored square along the left-unit
    comparison. *)

Lemma nth_dpath_mkPshRestrLayerMergedGen {m p k} (PC: PshDepsCohs m p.+1 k)
  (Q: mkPshRestrFramesType (proj1PshDepsCohs PC))
  (HC: mkPshRestrLayerCohType PC Q)
  q (Hq: q <= k) {qq} (e: q.+1 + p = qq) (Hqq: qq <= m.+1)
  (Hqp: q.+1 + p <= m.+1) (ε: arity) (d: psh.(G0) m.+2) (ζ: arity):
  nth_dpath (T := ((mkRestrFrameTypesAndFrames
      PC.(_pshDeps).(_pdeps).(_paintings).1)
    .(FrameDef) PC.(_pshDeps).(_pdeps).(_restrFrames).1).2)
    (Bd := fun a zeta =>
      PC.(_pshDeps).(_pdeps).(_paintings).2
        (PC.(_pshDeps).(_pdeps).(_restrFrames).2 0 leR_O zeta a))
    (f_equal_dep_sigT (fun a => (mkPshFrame PC.(_pshDeps) a).1)
       (fun a => (mkPshFrame PC.(_pshDeps) a).2)
       (pshFaceDimIrr (eq_sym e) (Hq := Hqq) (Hq' := Hqp) ε d)
     ⊙ mkPshRestrLayer PC Q HC q Hq Hqp ε d) ζ
  = mkPshRestrLayerChainB PC Q q Hq e Hqq Hqp ε d ζ
      (f_equal (fun a => (mkPshFrame PC.(_pshDeps) a).1)
         (pshFaceDimIrr (eq_sym e) (Hq := Hqq) (Hq' := Hqp) ε d)
       • Q.2 q.+1 (⇑ Hq) Hqp ε d)
      (mkPshRestrLayerFrameSquare PC Q HC q Hq e Hqq Hqp ε d ζ).
Proof.
  destruct e.
  rewrite nth_dpath_trans.
  rewrite nth_dpath_mkPshRestrLayer.
  unfold mkPshRestrLayerChain.
  cbn [pshFaceDimIrr f_equal_dep_sigT f_equal eq_sym nth_dpath nth_rew ap_nth
       eq_trans].
  etransitivity.
  - refine (sigT_trans_eq_refl_l
      (A := ((mkRestrFrameTypesAndFrames
                PC.(_pshDeps).(_pdeps).(_paintings).1)
             .(FrameDef) PC.(_pshDeps).(_pdeps).(_restrFrames).1).2)
      (P := fun a => GDom (PC.(_pshDeps).(_pdeps).(_paintings).2
              (PC.(_pshDeps).(_pdeps).(_restrFrames).2 0 leR_O ζ a)))
      _ _).
  - unshelve eapply (dep_arg_irr (fun b Hsq =>
      mkPshRestrLayerChainB PC Q q Hq eq_refl Hqq Hqp ε d ζ b Hsq)
      (eq_sym (eq_trans_refl_l (Q.2 q.+1 (⇑ Hq) Hqp ε d)))).
    now reflexivity.
Defined.

Lemma nth_dpath_mkPshRestrLayerMerged {m p k} (PC: PshDepsCohs m p.+1 k)
  (Q: mkPshRestrFramesType (proj1PshDepsCohs PC))
  (HC: mkPshRestrLayerCohType PC Q)
  q (Hq: q <= k) (Hqp: q + p.+1 <= m.+1) (ε: arity)
  (d: psh.(G0) m.+2) (ζ: arity):
  nth_dpath (Bd := fun a zeta =>
      PC.(_pshDeps).(_pdeps).(_paintings).2
        (PC.(_pshDeps).(_pdeps).(_restrFrames).2 0 leR_O zeta a))
    (mkPshRestrLayerMerged PC Q HC q Hq Hqp ε d) ζ
  = mkPshRestrLayerMergedChain PC Q HC q Hq Hqp ε d ζ.
Proof.
  now exact (nth_dpath_intro
    (mkPshRestrLayerMergedChain PC Q HC q Hq Hqp ε d) ζ).
Defined.

(** Numerical source reindexing of the selected componentwise layer path.
    Its component calculation uses the same corrected square as the layer
    constructor. *)
Lemma mkPshRestrLayerMerged_comp {m p k} (PC: PshDepsCohs m p.+1 k)
  (Q: mkPshRestrFramesType (proj1PshDepsCohs PC))
  (HC: mkPshRestrLayerCohType PC Q)
  q (Hq: q <= k) (Hqp: q + p.+1 <= m.+1) (ε: arity)
  (d: psh.(G0) m.+2):
  mkPshRestrLayerMerged PC Q HC q Hq Hqp ε d =
  f_equal_dep_sigT (fun a => (mkPshFrame PC.(_pshDeps) a).1)
    (fun a => (mkPshFrame PC.(_pshDeps) a).2)
    (pshFaceDimIrr (eq_sym (plus_n_Sm q p))
      (Hq' := leR_add_shift Hqp) ε d)
  ⊙ mkPshRestrLayer PC Q HC q Hq (leR_add_shift Hqp) ε d.
Proof.
  refine (layer_dpath2_eq
    (Bd := fun a ζ => PC.(_pshDeps).(_pdeps).(_paintings).2
      (PC.(_pshDeps).(_pdeps).(_restrFrames).2 0 leR_O ζ a))
    (κ := eq_refl) (mkPshRestrLayerMerged PC Q HC q Hq Hqp ε d) _ _).
  intro ζ.
  rewrite nth_dpath_mkPshRestrLayerMerged.
  now exact (eq_sym (nth_dpath_mkPshRestrLayerMergedGen PC Q HC q Hq
    (plus_n_Sm q p) Hqp (leR_add_shift Hqp) ε d ζ)).
Defined.









(** The frame path is the dependent pair of its composite prefix path
    and the layer path constructed from the selected components. *)

Lemma mkPshRestrFrameStep {m p k} (PC: PshDepsCohs m p.+1 k)
  (Q: mkPshRestrFramesType (proj1PshDepsCohs PC))
  (HC: mkPshRestrLayerCohType PC Q)
  q (Hq: q <= k) (Hqp: q + p.+1 <= m.+1) (ε: arity)
  (d: psh.(G0) m.+2):
  mkPshFrame PC.(_pshDeps)
    (psh.(GFace) m.+1 (q + p.+1) Hqp ε d) =
  (mkRestrFrames (depsCohs := pshDepsCohs PC)).2 q Hq ε
    ((mkPshFramesNext (proj1PshDepsCohs PC) Q).2 d).
Proof.
  now exact (eq_existT_curried
    (f_equal (fun a => (mkPshFrame PC.(_pshDeps) a).1)
       (pshFaceDimIrr (eq_sym (plus_n_Sm q p))
         (Hq' := leR_add_shift Hqp) ε d)
     • Q.2 q.+1 (⇑ Hq) (leR_add_shift Hqp) ε d)
    (mkPshRestrLayerMerged PC Q HC q Hq Hqp ε d)).
Defined.

(** The dependent-pair presentation of the frame step is its defining
    computation rule. *)

Lemma mkPshRestrFrameStep_merged {m p k} (PC: PshDepsCohs m p.+1 k)
  (Q: mkPshRestrFramesType (proj1PshDepsCohs PC))
  (HC: mkPshRestrLayerCohType PC Q)
  q (Hq: q <= k) (Hqp: q + p.+1 <= m.+1) (ε: arity)
  (d: psh.(G0) m.+2):
  mkPshRestrFrameStep PC Q HC q Hq Hqp ε d =
  (= f_equal (fun a => (mkPshFrame PC.(_pshDeps) a).1)
       (pshFaceDimIrr (eq_sym (plus_n_Sm q p))
         (Hq' := leR_add_shift Hqp) ε d)
     • Q.2 q.+1 (⇑ Hq) (leR_add_shift Hqp) ε d;
     mkPshRestrLayerMerged PC Q HC q Hq Hqp ε d).
Proof. now reflexivity. Defined.

(** The frame step at its unshifted source dimension. This is the
    boundary equality shared by the restriction-painting constructor and
    its numerical reindexing law. *)
Local Lemma mkPshRestrFrameStep_shift {m p k} (PC: PshDepsCohs m p.+1 k)
  (Q: mkPshRestrFramesType (proj1PshDepsCohs PC))
  (HC: mkPshRestrLayerCohType PC Q)
  q (Hq: q <= k) (HZ: q.+1 + p <= m.+1) (ε: arity) (d: psh.(G0) m.+2):
  f_equal (mkPshFrame PC.(_pshDeps))
    (pshFaceDimIrr (plus_n_Sm q p)
      (Hq := HZ) (Hq' := leR_eq (plus_n_Sm q p) HZ) ε d)
  • mkPshRestrFrameStep PC Q HC q Hq (leR_eq (plus_n_Sm q p) HZ) ε d =
  eq_existT_curried (Q.2 q.+1 (⇑ Hq) HZ ε d)
    (mkPshRestrLayer PC Q HC q Hq HZ ε d).
Proof.
  unfold mkPshRestrFrameStep.
  now exact (section_pair_source_shift
    (fun a => (mkPshFrame PC.(_pshDeps) a).1)
    (fun a => (mkPshFrame PC.(_pshDeps) a).2)
    (pshFaceDimIrr (plus_n_Sm q p)
      (Hq := HZ) (Hq' := leR_eq (plus_n_Sm q p) HZ) ε d)
    (pshFaceDimIrr (eq_sym (plus_n_Sm q p))
      (Hq := leR_eq (plus_n_Sm q p) HZ) (Hq' := HZ) ε d)
    (eq_sym (pshFaceDimIrr_sym (plus_n_Sm q p)
      (Hq := HZ) (Hq' := leR_eq (plus_n_Sm q p) HZ) ε d))
    (Q.2 q.+1 (⇑ Hq) HZ ε d)
    (mkPshRestrLayer PC Q HC q Hq HZ ε d)
    (mkPshRestrLayerMerged PC Q HC q Hq
      (leR_eq (plus_n_Sm q p) HZ) ε d)
    (mkPshRestrLayerMerged_comp PC Q HC q Hq
      (leR_eq (plus_n_Sm q p) HZ) ε d)).
Defined.

(** Restriction-frame paths and their 2-dimensional coherence are built
    mutually.  At a positive stage, the coherence for the new top layer is
    stated over the frame paths already built for the preceding stages. *)

Class PshRestrCohBlock {m p k} (PC: PshDepsCohs m p k) := {
  PshRestrCohData: Type;
  PshRestrFramesDef: PshRestrCohData -> mkPshRestrFramesType PC;
}.

Fixpoint mkPshRestrFramesAndCohs {m p k}
  (PC: PshDepsCohs m p k): PshRestrCohBlock PC :=
  match p return forall PC: PshDepsCohs m p k, PshRestrCohBlock PC with
  | 0 => fun PC => {|
      PshRestrCohData := unit;
      PshRestrFramesDef _ :=
        (tt; fun q Hq Hqp ε d => eq_refl)
    |}
  | S p => fun PC =>
      let prev := mkPshRestrFramesAndCohs (proj1PshDepsCohs PC) in
      {|
        PshRestrCohData :=
          { C: prev.(PshRestrCohData) &T
            mkPshRestrLayerCohType PC (prev.(PshRestrFramesDef) C) };
        PshRestrFramesDef C :=
          (prev.(PshRestrFramesDef) C.1;
           mkPshRestrFrameStep PC (prev.(PshRestrFramesDef) C.1) C.2)
      |}
  end PC.

Definition mkPshRestrCohData {m p k} (PC: PshDepsCohs m p k): Type :=
  (mkPshRestrFramesAndCohs PC).(PshRestrCohData).

Definition mkPshRestrFrames {m p k} (PC: PshDepsCohs m p k)
  (C: mkPshRestrCohData PC): mkPshRestrFramesType PC :=
  (mkPshRestrFramesAndCohs PC).(PshRestrFramesDef) C.

Lemma mkPshRestrFrames_succ_path {m p k} (PC: PshDepsCohs m p.+1 k)
  (C: mkPshRestrCohData (proj1PshDepsCohs PC))
  (HC: mkPshRestrLayerCohType PC (mkPshRestrFrames _ C))
  q (Hq: q <= k) (Hqp: q + p.+1 <= m.+1) (ε: arity)
  (d: psh.(G0) m.+2):
  (mkPshRestrFrames PC (C; HC)).2 q Hq Hqp ε d =
  mkPshRestrFrameStep PC (mkPshRestrFrames _ C) HC q Hq Hqp ε d.
Proof.
  now reflexivity.
Defined.

(** A [PshDepsCohs2] is a presheaf-equipped coherence stage together with
    the recursively nested 2-cells that make its restriction-frame paths
    coherent. *)

Class PshDepsCohs2 (m p k: nat) := {
  _pshDepsCohs: PshDepsCohs m p k;
  _pExtraDepsCohs: DepsCohsExtension p k
    (pshDepsCohs _pshDepsCohs);
  _pCohPaintings: mkCohPaintingTypes _pExtraDepsCohs;
  _pCoh2Frames: mkCoh2FrameTypes _pCohPaintings;
  _pshRestrCohs: mkPshRestrCohData _pshDepsCohs;
}.

Definition pshDepsCohs2 {m p k} (PC2: PshDepsCohs2 m p k):
  DepsCohs2 p k := {|
  _depsCohs := pshDepsCohs PC2.(_pshDepsCohs);
  _extraDepsCohs := PC2.(_pExtraDepsCohs);
  _cohPaintings := PC2.(_pCohPaintings);
  _coh2Frames := PC2.(_pCoh2Frames);
|}.

#[local]
Instance proj1PshDepsCohs2 {m p k} (PC2: PshDepsCohs2 m p.+1 k):
  PshDepsCohs2 m p k.+1 := {|
  _pshDepsCohs := proj1PshDepsCohs PC2.(_pshDepsCohs);
  _pExtraDepsCohs :=
    (pshDepsCohs PC2.(_pshDepsCohs);
      PC2.(_pExtraDepsCohs))%extradepscohs;
  _pCohPaintings := PC2.(_pCohPaintings).1;
  _pCoh2Frames := PC2.(_pCoh2Frames).1;
  _pshRestrCohs := PC2.(_pshRestrCohs).1;
|}.

(** The next-level presheaf-equipped [DepsRestr].  The core constructor
    only needs the underlying presheaf-equipped coherence stage and its
    realized 2-dimensional frame data; keeping this helper separate avoids
    a circular record construction at tower positions. *)

Definition mkPshDepsRestrCore {m p k} (PC: PshDepsCohs m p k)
  (C: mkPshRestrCohData PC): PshDepsRestr m.+1 p.+1 k := {|
  _pdeps := mkDepsRestr (depsCohs := pshDepsCohs PC);
  _pshBound := ⇑ PC.(_pshDeps).(_pshBound);
  _pshFrames := mkPshFrames PC.(_pshDeps);
  _pshPaintings := mkPshPaintings PC.(_pshExtraDeps);
  _pshRestrs := mkPshRestrFrames PC C;
|}.

(** The next-level presheaf-equipped [DepsRestr]. *)

#[local]
Instance mkPshDepsRestr {m p k} (PC2: PshDepsCohs2 m p k):
  PshDepsRestr m.+1 p.+1 k :=
  mkPshDepsRestrCore PC2.(_pshDepsCohs) PC2.(_pshRestrCohs).

(** Presheaf data for [DepsCohsExtension]. *)

Inductive PshDepsCohsExtension (m: nat):
  forall {p k} (PC2: PshDepsCohs2 m p k),
  DepsCohsExtension p k (pshDepsCohs PC2.(_pshDepsCohs)) -> Type :=
| TopPshCohDep {p} {PC2: PshDepsCohs2 m p 0}:
    PshDepsCohsExtension m PC2
      (TopCohDep (mkPshFiller (mkPshDepsRestr PC2)))
| AddPshCohDep {p k} (PC2: PshDepsCohs2 m p.+1 k)
    {XC: DepsCohsExtension p.+1 k
      (pshDepsCohs PC2.(_pshDepsCohs))}:
    PshDepsCohsExtension m PC2 XC ->
    PshDepsCohsExtension m (proj1PshDepsCohs2 PC2)
      (AddCohDep (pshDepsCohs PC2.(_pshDepsCohs)) XC).

Arguments TopPshCohDep {m p PC2}.
Arguments AddPshCohDep {m p k} PC2 {XC} _.

Fixpoint mkPshExtraDeps {m p k} {PC2: PshDepsCohs2 m p k}
  {XC: DepsCohsExtension p k (pshDepsCohs PC2.(_pshDepsCohs))}
  (PCX: PshDepsCohsExtension m PC2 XC):
  PshDepsExtension m.+1 (mkPshDepsRestr PC2) (mkExtraDeps XC) :=
  match PCX with
  | TopPshCohDep => TopPshDep
  | AddPshCohDep PC2' PCX' =>
      AddPshDep (mkPshDepsRestr PC2') (mkPshExtraDeps PCX')
  end.

(** The next-level restriction-painting paths. *)

Fixpoint mkPshRestrPainting {m p k} {PC2: PshDepsCohs2 m p k}
  {XC: DepsCohsExtension p k (pshDepsCohs PC2.(_pshDepsCohs))}
  (PCX: PshDepsCohsExtension m PC2 XC) q {struct q}:
  forall (Hq: q <= k) (Hqp: q + p <= m.+1) (ε: arity)
    (d: psh.(G0) m.+2),
  rew [(mkDepsRestr
      (depsCohs := pshDepsCohs PC2.(_pshDepsCohs))).(_paintings).2]
      (mkPshRestrFrames PC2.(_pshDepsCohs) PC2.(_pshRestrCohs)).2
        q Hq Hqp ε d in
    mkPshPainting PC2.(_pshDepsCohs).(_pshExtraDeps)
      (psh.(GFace) m.+1 (q + p) Hqp ε d) =
  (mkRestrPaintings XC).2 q Hq ε
    (mkPshFrame (proj1PshDepsRestr (mkPshDepsRestr PC2)) d)
    (mkPshPainting
      (AddPshDep (mkPshDepsRestr PC2) (mkPshExtraDeps PCX)) d).
Proof.
  destruct q; intros.
  - now exact (eq_sym (nth_lam _ ε)).
  - destruct PCX as [| p' k' PC2' XC' PCX'].
    + now destruct (leR_O_contra Hq).
    + unshelve eapply (eq_existT_curried_dep
        (Q := mkPainting PC2'.(_pshDepsCohs).(_pExtraDeps))).
      * now exact (mkPshRestrLayer PC2'.(_pshDepsCohs)
          (mkPshRestrFrames
            (proj1PshDepsCohs PC2'.(_pshDepsCohs))
            PC2'.(_pshRestrCohs).1)
          PC2'.(_pshRestrCohs).2 q (⇓ Hq) Hqp ε d).
      * refine (path_reindex_source _
          (mkPshRestrPainting m p'.+1 k' PC2' XC' PCX'
             q (⇓ Hq) (leR_eq (plus_n_Sm q p') Hqp) ε d)).
        apply (rew_align_dep
          (P := fun x => mkPainting PC2'.(_pshDepsCohs).(_pExtraDeps) x)
          (f_equal (mkPshFrame PC2'.(_pshDepsCohs).(_pshDeps))
            (pshFaceDimIrr (plus_n_Sm q p') (Hq := Hqp)
              (Hq' := leR_eq (plus_n_Sm q p') Hqp) ε d))).
        { now exact (eq_trans
            (eq_sym (rew_map
              (fun a => mkPainting PC2'.(_pshDepsCohs).(_pExtraDeps) a)
              (mkPshFrame PC2'.(_pshDepsCohs).(_pshDeps))
              (pshFaceDimIrr (plus_n_Sm q p') (Hq := Hqp)
                (Hq' := leR_eq (plus_n_Sm q p') Hqp) ε d)
              (mkPshPainting PC2'.(_pshDepsCohs).(_pshExtraDeps)
                (psh.(GFace) m.+1 (q.+1 + p') Hqp ε d))))
            (f_equal_dep _
              (mkPshPainting PC2'.(_pshDepsCohs).(_pshExtraDeps))
              (pshFaceDimIrr (plus_n_Sm q p') (Hq := Hqp)
                (Hq' := leR_eq (plus_n_Sm q p') Hqp) ε d))). }
        now exact (eq_sym (mkPshRestrFrameStep_shift PC2'.(_pshDepsCohs)
          (mkPshRestrFrames (proj1PshDepsCohs PC2'.(_pshDepsCohs))
            PC2'.(_pshRestrCohs).1)
          PC2'.(_pshRestrCohs).2 q (⇓ Hq) Hqp ε d)).
Defined.

(** The list of next-level restriction-painting coherences. *)

Fixpoint mkPshRestrPaintingsPrefix {m p k}:
  forall {PC2: PshDepsCohs2 m p k}
    {XC: DepsCohsExtension p k (pshDepsCohs PC2.(_pshDepsCohs))}
    (PCX: PshDepsCohsExtension m PC2 XC),
  mkPshRestrPaintingTypes
    (proj1PshDepsRestr (mkPshDepsRestr PC2))
    (AddPshDep (mkPshDepsRestr PC2) (mkPshExtraDeps PCX))
    (mkRestrPaintingsPrefix XC) :=
  match p return forall (PC2: PshDepsCohs2 m p k)
    (XC: DepsCohsExtension p k (pshDepsCohs PC2.(_pshDepsCohs)))
    (PCX: PshDepsCohsExtension m PC2 XC),
    mkPshRestrPaintingTypes
      (proj1PshDepsRestr (mkPshDepsRestr PC2))
      (AddPshDep (mkPshDepsRestr PC2) (mkPshExtraDeps PCX))
      (mkRestrPaintingsPrefix XC) with
  | 0 => fun _ _ _ => tt
  | S p => fun PC2 XC PCX =>
      (mkPshRestrPaintingsPrefix (AddPshCohDep PC2 PCX);
       mkPshRestrPainting (AddPshCohDep PC2 PCX))
  end.

Definition mkPshRestrPaintings {m p k} {PC2: PshDepsCohs2 m p k}
  {XC: DepsCohsExtension p k (pshDepsCohs PC2.(_pshDepsCohs))}
  (PCX: PshDepsCohsExtension m PC2 XC):
  mkPshRestrPaintingTypes (mkPshDepsRestr PC2) (mkPshExtraDeps PCX)
    (mkRestrPaintings XC) :=
  (mkPshRestrPaintingsPrefix PCX; mkPshRestrPainting PCX).

(** The presheaf realization of the core [mkDepsCohs] step. *)

Definition mkPshDepsCohsNext {m p k} {PC2: PshDepsCohs2 m p k}
  (PCX: PshDepsCohsExtension m PC2 PC2.(_pExtraDepsCohs)):
  PshDepsCohs m.+1 p.+1 k := {|
  _pshDeps := mkPshDepsRestr PC2;
  _pExtraDeps := mkExtraDeps PC2.(_pExtraDepsCohs);
  _pshExtraDeps := mkPshExtraDeps PCX;
  _pRestrPaintings := mkRestrPaintings PC2.(_pExtraDepsCohs);
  _pshRestrPaintings := mkPshRestrPaintings PCX;
  _pCohs := mkCohFrames PC2.(_pCohPaintings) PC2.(_pCoh2Frames);
|}.

(** The presheaf side of a fused layer coherence carries no layer structure of
    its own: the presheaf painting is a global section, so the edge that
    [rew_coh2Layer_split] expects as a [rew_cohLayer_hex] transport chain is
    just that section's action on a path, conjugated by its actions on the two
    comparison paths.  [HH1] is the presheaf exchange coherence that identifies
    the two composites; in the intended instance it is [psh.(GFaceCoh2)].

    The two comparison paths start at [rur zs2] and [rusY zr2] rather than at
    bare points, and the level-2 data [S2A], [pIs], [pIr], [aL], [aR] is
    arbitrary: the fused coherence shares that data between the presheaf side
    and the two restriction directions, where [rur] and [rusY] are face maps
    and the comparisons are the stored presheaf restriction coherences at
    those faces.  The section ignores the level-2 argument, which is why the
    statement holds for any of it. *)

Lemma sec_action_as_cohLayer_hex {Y X2A: Type} {SY: Y -> Type}
  {S2A: X2A -> Type} {TUA: Type}
  (uf0: TUA -> Y) (sec: forall y, SY y)
  (rur rusY: X2A -> Y) {zs1 zs2 zr1 zr2: X2A}
  (pIs: zs1 = zs2) (pIr: zr1 = zr2)
  {aL: S2A zs1} {aR: S2A zr1}
  {u0 u1: TUA} (eU1: u0 = u1)
  (pV0: rur zs2 = uf0 u0) (pV1: rusY zr2 = uf0 u1) (K1: rur zs1 = rusY zr1)
  (HH1: f_equal rur pIs • (pV0 • f_equal uf0 eU1)
        = K1 • (f_equal rusY pIr • pV1)):
  f_equal_dep (fun t => SY (uf0 t)) (fun t => sec (uf0 t)) eU1
  = f_equal (fun x => rew [fun dd => SY (uf0 dd)] eU1 in x)
      (eq_sym (f_equal_dep SY sec pV0))
    • (f_equal (fun _: S2A zs2 =>
         rew [fun dd => SY (uf0 dd)] eU1 in rew [SY] pV0 in sec (rur zs2))
         (eq_refl: rew [S2A] pIs in aL = rew [S2A] pIs in aL)
       • (rew_cohLayer_hex (P := SY) (rf0 := uf0)
            (F := fun (z: X2A) (_: S2A z) => sec (rur z))
            (G := fun (z: X2A) (_: S2A z) => sec (rusY z))
            (E1 := eU1) (C2 := pIs) (D2 := pIr)
            (C1 := pV0) (D1 := pV1) (K := K1) (aL := aL) (aR := aR)
            (f_equal_dep SY sec K1) HH1
          • (eq_sym (f_equal (fun _: S2A zr2 => rew [SY] pV1 in sec (rusY zr2))
                       (eq_refl: rew [S2A] pIr in aR = rew [S2A] pIr in aR))
             • eq_sym (eq_sym (f_equal_dep SY sec pV1))))).
Proof.
  cbn [f_equal eq_sym].
  rewrite 2 eq_trans_refl_l, eq_sym_involutive.
  rewrite (rew_cohLayer_hex_section SY sec uf0 rur rusY eU1 pIs pIr
    pV0 pV1 K1 aL aR HH1).
  unfold dpath_change.
  rewrite <- eq_sym_map_distr, <- 2 eq_trans_assoc, eq_trans_sym_cancel_l.
  now rewrite eq_trans_sym_inv_l, eq_trans_refl_r.
Defined.

(** The painting-level counterpart of [mkPshRestrLayerCohType].

    [mkPshRestrLayerCohType] is a hexagon of frame paths; this is the same
    hexagon displayed over paintings.  Its six edges are the presheaf
    painting's action on the presheaf exchange path, the two stored
    presheaf restriction-painting coherences, the two restriction-painting
    images of the previous stage's [mkPshRestrPainting], and the stored
    coherence painting.  It is the datum the fused layer coherence consumes
    as its [Hcoh2Painting] premise, so it occupies the same place on the
    presheaf side as [mkCoh2PaintingType] does in the indexed tower. *)

Definition mkPshRestrPaintingCohType {m p k} (PC2: PshDepsCohs2 m p.+1 k)
  (PCX: PshDepsCohsExtension m PC2 PC2.(_pExtraDepsCohs)): Type :=
  let Pt := fun x =>
    GDom (PC2.(_pshDepsCohs).(_pshDeps).(_pdeps).(_paintings).2 x) in
  forall q (Hq: q <= k) r (Hr: r <= q) (Hqp: q.+1 + p <= m.+1)
    (ε ω: arity) (d: psh.(G0) m.+2),
  rew [fun π => rew [Pt] π in _ = _]
      (PC2.(_pshRestrCohs).2 q Hq r Hr Hqp ε ω d) in
  (sigT_map_eq (Q := Pt)
     (f := PC2.(_pshDepsCohs).(_pshDeps).(_pshFrames).2)
     (fun (_: psh.(G0) m) x => x)
     (f_equal_dep
        (fun y => GDom (PC2.(_pshDepsCohs).(_pshDeps).(_pdeps).(_paintings).2
           (PC2.(_pshDepsCohs).(_pshDeps).(_pshFrames).2 y)))
        PC2.(_pshDepsCohs).(_pshDeps).(_pshPaintings).2
        (psh.(GFaceCoh) m (q + p) (⇓ Hqp) (r + p)
           (leR_add_mono_r Hr p) ε ω d))
   ⊙[Pt] (PC2.(_pshDepsCohs).(_pshRestrPaintings).2 r (Hr ↕ Hq)
        (leR_add_mono_r Hr p ↕ (⇓ Hqp)) ω
        (psh.(GFace) m.+1 (q.+1 + p) Hqp ε d)
      ⊙[Pt] sigT_map_eq (Q := Pt)
          (PC2.(_pshDepsCohs).(_pRestrPaintings).2 r (Hr ↕ Hq) ω)
          (mkPshRestrPainting (AddPshCohDep PC2 PCX) q.+1 (⇑ Hq) Hqp ε d))) =
  PC2.(_pshDepsCohs).(_pshRestrPaintings).2 q Hq (⇓ Hqp) ε
    (psh.(GFace) m.+1 (r + p) (↑ (leR_add_mono_r Hr p ↕ (⇓ Hqp))) ω d)
  ⊙[Pt] (sigT_map_eq (Q := Pt)
       (PC2.(_pshDepsCohs).(_pRestrPaintings).2 q Hq ε)
       (mkPshRestrPainting (AddPshCohDep PC2 PCX) r (↑ (Hr ↕ Hq))
          (↑ (leR_add_mono_r Hr p ↕ (⇓ Hqp))) ω d)
     ⊙[Pt] PC2.(_pCohPaintings).2 q Hq r Hr ε ω
         ((mkPshFrames (proj1PshDepsRestr
             (proj1PshDepsRestr (mkPshDepsRestr PC2)))).2 d)
         (mkPshPainting
            (AddPshDep (proj1PshDepsRestr (mkPshDepsRestr PC2))
               (AddPshDep (mkPshDepsRestr PC2) (mkPshExtraDeps PCX))) d)).

(** The painting 2-coherences of all stages, nested as the frame ones are by
    [mkPshRestrCohData].  Stage [p.+1] adds one [mkPshRestrPaintingCohType]
    on top of the stages below, which are read off the truncated stage
    [proj1PshDepsCohs2 PC2]. *)

Fixpoint mkPshRestrPaintingCohData {m p k}:
  forall (PC2: PshDepsCohs2 m p k)
    (PCX: PshDepsCohsExtension m PC2 PC2.(_pExtraDepsCohs)), Type :=
  match p return forall (PC2: PshDepsCohs2 m p k)
    (PCX: PshDepsCohsExtension m PC2 PC2.(_pExtraDepsCohs)), Type with
  | 0 => fun _ _ => unit
  | S p => fun PC2 PCX =>
      { _: mkPshRestrPaintingCohData (proj1PshDepsCohs2 PC2)
             (AddPshCohDep PC2 PCX) &T
        mkPshRestrPaintingCohType PC2 PCX }
  end.

(** The stage of the ladder that carries the painting 2-coherences, one rung
    above [PshDepsCohs2].  It is the last rung: a coherence between two
    painting 2-coherences is a 3-cell of an [HGpd] and therefore free by
    [GUIP].

    The stage carries only the presheaf realization of its data.  The indexed
    level-2 extension and its 2-coherence paintings — [DepsCohs3]'s own fields
    on the indexed side — are arguments of [mkPshDepsCohs2Next] and indices of
    [PshDepsCohs3Extension] instead, because the recursion that builds the
    rung descends the stage tower by destructing that extension, which
    separates them from any field they might be stored in. *)

Class PshDepsCohs3 (m p k: nat) := {
  _pshDepsCohs2: PshDepsCohs2 m p k;
  _pshExtraDepsCohs: PshDepsCohsExtension m _pshDepsCohs2
    _pshDepsCohs2.(_pExtraDepsCohs);
  _pshRestrPaintingCohs: mkPshRestrPaintingCohData _pshDepsCohs2
    _pshExtraDepsCohs;
}.

#[local]
Instance proj1PshDepsCohs3 {m p k} (PC3: PshDepsCohs3 m p.+1 k):
  PshDepsCohs3 m p k.+1 := {|
  _pshDepsCohs2 := proj1PshDepsCohs2 PC3.(_pshDepsCohs2);
  _pshExtraDepsCohs :=
    AddPshCohDep PC3.(_pshDepsCohs2) PC3.(_pshExtraDepsCohs);
  _pshRestrPaintingCohs := PC3.(_pshRestrPaintingCohs).1;
|}.

(** The plain prefix and layer cells are constructed together. The stored
    frame cell is their selected inverse-index presentation; painting
    coherence recovers the same cells through those boundary comparisons. *)

Definition pshRestrAt {m p k} {frames: mkFrameTypes p.+1 k}
  {pshFrames: mkPshFrameTypes m frames}
  {prev: RestrFrameTypeBlock p k.+1}
  {prevPsh: PshRestrBlock m pshFrames.1 prev}
  {R: mkRestrFrameTypesStep frames prev}
  (Q: mkPshRestrTypesStep pshFrames prevPsh R)
  q (Hq: q <= k) {QQ} (e: q + p = QQ) (HQ: QQ <= m) (ε: arity)
  (d: psh.(G0) m.+1):
  pshFrames.2 (psh.(GFace) m QQ HQ ε d) =
  R.2 q Hq ε ((prevPsh.(PshFramesDef) Q.1).2 d) :=
  match e in _ = z return forall Hz: z <= m,
    pshFrames.2 (psh.(GFace) m z Hz ε d) =
    R.2 q Hq ε ((prevPsh.(PshFramesDef) Q.1).2 d)
  with
  | eq_refl => fun Hz => Q.2 q Hq Hz ε d
  end HQ.

Definition mkPshRestrLayerCohTypeAt {m p k}
  (PC: PshDepsCohs m p.+1 k)
  (Q: mkPshRestrFramesType (proj1PshDepsCohs PC))
  q (Hq: q <= k) r (Hr: r <= q) {QQ RR}
  (e1: q + p = QQ) (e2: r + p = RR)
  (HQ: QQ <= m) (HRQ: RR <= QQ)
  (ε ω: arity) (d: psh.(G0) m.+2): Type :=
  f_equal PC.(_pshDeps).(_pshFrames).2
    (psh.(GFaceCoh) m QQ HQ RR HRQ ε ω d)
  • (pshRestrAt PC.(_pshDeps).(_pshRestrs) r (Hr ↕ Hq) e2 (HRQ ↕ HQ) ω
       (psh.(GFace) m.+1 QQ.+1 (⇑ HQ) ε d)
  • f_equal (PC.(_pshDeps).(_pdeps).(_restrFrames).2 r (Hr ↕ Hq) ω)
      (pshRestrAt Q q.+1 (⇑ Hq) (f_equal S e1) (⇑ HQ) ε d)) =
  pshRestrAt PC.(_pshDeps).(_pshRestrs) q Hq e1 HQ ε
    (psh.(GFace) m.+1 RR (↑ (HRQ ↕ HQ)) ω d)
  • (f_equal (PC.(_pshDeps).(_pdeps).(_restrFrames).2 q Hq ε)
      (pshRestrAt Q r (↑ (Hr ↕ Hq)) e2 (↑ (HRQ ↕ HQ)) ω d)
  • PC.(_pCohs).2 q Hq r Hr ε ω
      ((mkPshFramesNext (proj1PshDepsCohs PC) Q).2 d).1).

(** The two numeric presentations of a frame coherence share inverse
    transport maps and their computation law. *)
Definition pshCohPointToAt {m p k} (PC: PshDepsCohs m p.+1 k)
  (Q: mkPshRestrFramesType (proj1PshDepsCohs PC))
  q (Hq: q <= k) r (Hr: r <= q) {QQ RR}
  (eqQ: q + p = QQ) (eqR: r + p = RR)
  (HQ0: q + p <= m) (HQ: QQ <= m) (HR: RR <= QQ)
  (ε ω: arity) (d: psh.(G0) m.+2)
  (K: mkPshRestrLayerCohTypeAt PC Q q Hq r Hr eq_refl eq_refl
    HQ0 (leR_add_mono_r Hr p) ε ω d):
  mkPshRestrLayerCohTypeAt PC Q q Hq r Hr eqQ eqR HQ HR ε ω d.
Proof. destruct eqQ, eqR. now exact K. Defined.

Definition pshCohPointFromAt {m p k} (PC: PshDepsCohs m p.+1 k)
  (Q: mkPshRestrFramesType (proj1PshDepsCohs PC))
  q (Hq: q <= k) r (Hr: r <= q) {QQ RR}
  (eqQ: q + p = QQ) (eqR: r + p = RR)
  (HQ0: q + p <= m) (HQ: QQ <= m) (HR: RR <= QQ)
  (ε ω: arity) (d: psh.(G0) m.+2)
  (K: mkPshRestrLayerCohTypeAt PC Q q Hq r Hr eqQ eqR HQ HR ε ω d):
  mkPshRestrLayerCohTypeAt PC Q q Hq r Hr eq_refl eq_refl
    HQ0 (leR_add_mono_r Hr p) ε ω d.
Proof. destruct eqQ, eqR. now exact K. Defined.

Lemma pshCohPoint_to_from {m p k} (PC: PshDepsCohs m p.+1 k)
  (Q: mkPshRestrFramesType (proj1PshDepsCohs PC))
  q (Hq: q <= k) r (Hr: r <= q) {QQ RR}
  (eqQ: q + p = QQ) (eqR: r + p = RR)
  (HQ0: q + p <= m) (HQ: QQ <= m) (HR: RR <= QQ)
  (ε ω: arity) (d: psh.(G0) m.+2)
  (K: mkPshRestrLayerCohTypeAt PC Q q Hq r Hr eqQ eqR HQ HR ε ω d):
  pshCohPointToAt PC Q q Hq r Hr eqQ eqR HQ0 HQ HR ε ω d
    (pshCohPointFromAt PC Q q Hq r Hr eqQ eqR HQ0 HQ HR ε ω d K) = K.
Proof. now destruct eqQ, eqR. Defined.







Definition pshRestrCohsAt {m p k}
  (PC: PshDepsCohs m p.+1 k)
  (Q: mkPshRestrFramesType (proj1PshDepsCohs PC))
  (HC: mkPshRestrLayerCohType PC Q)
  q (Hq: q <= k) r (Hr: r <= q) {QQ RR}
  (e1: q + p = QQ) (e2: r + p = RR)
  (HQ: QQ <= m) (HRQ: RR <= QQ)
  (ε ω: arity) (d: psh.(G0) m.+2):
  mkPshRestrLayerCohTypeAt PC Q q Hq r Hr e1 e2 HQ HRQ ε ω d.
Proof.
  now exact (pshCohPointToAt PC Q q Hq r Hr e1 e2
    (leR_eq (eq_sym e1) HQ) HQ HRQ ε ω d
    (HC q Hq r Hr (⇑ (leR_eq (eq_sym e1) HQ)) ε ω d)).
Defined.

Definition pshRestrAtSourceInv {m p k} (P: PshDepsRestr m p.+1 k)
  q (Hq: q <= k) {QQ} (e: q + p = QQ)
  (HQ: QQ <= m) (HQ0: q + p <= m) (ε: arity) (d: psh.(G0) m.+1):
  pshRestrAt P.(_pshRestrs) q Hq e HQ ε d =
  f_equal P.(_pshFrames).2
    (pshFaceDimIrr (eq_sym e) (Hq := HQ) (Hq' := HQ0) ε d)
  • pshRestrAt P.(_pshRestrs) q Hq eq_refl HQ0 ε d.
Proof.
  destruct e.
  now exact (eq_sym (eq_trans_refl_l
    (pshRestrAt P.(_pshRestrs) q Hq eq_refl HQ0 ε d))).
Defined.

(** Reindexing the inverse numeric path transports the selected frame
    boundary. No equality of frame cells is chosen independently. *)
Definition pshRestrAtSourceGen {m p k} (P: PshDepsRestr m p.+1 k)
  q (Hq: q <= k) {QQ} (e: q + p = QQ) {h: QQ = q + p} (a: eq_sym e = h)
  (HQ: QQ <= m) (HQ0: q + p <= m) (ε: arity) (d: psh.(G0) m.+1):
  pshRestrAt P.(_pshRestrs) q Hq e HQ ε d =
  f_equal P.(_pshFrames).2 (pshFaceDimIrr h (Hq := HQ) (Hq' := HQ0) ε d)
  • pshRestrAt P.(_pshRestrs) q Hq eq_refl HQ0 ε d.
Proof. destruct a. now exact (pshRestrAtSourceInv P q Hq e HQ HQ0 ε d). Defined.

Definition pshRestrAtSourceBase {m p k} (P: PshDepsRestr m p.+1 k)
  q (Hq: q <= k) {QQ} (e: q + p = QQ) (h: QQ = q + p)
  (HQ: QQ <= m) (HQ0: q + p <= m) (ε: arity) (d: psh.(G0) m.+1) :=
  pshRestrAtSourceGen P q Hq e (natUIP (eq_sym e) h) HQ HQ0 ε d.

Lemma pshRestrAt_stepG {m p k} (PC: PshDepsCohs m p.+1 k)
  (C: mkPshRestrCohData (proj1PshDepsCohs PC))
  (HC: mkPshRestrLayerCohType PC (mkPshRestrFrames (proj1PshDepsCohs PC) C))
  q (Hq: q <= k) {ZZ} (e: q + p.+1 = ZZ) (h: ZZ = q + p.+1)
  (HZ: ZZ <= m.+1) (Hqp: q + p.+1 <= m.+1) (ε: arity) (d: psh.(G0) m.+2):
  pshRestrAt (mkPshRestrFrames PC (C; HC)) q Hq e HZ ε d =
  f_equal (mkPshFrame PC.(_pshDeps))
    (pshFaceDimIrr h (Hq := HZ) (Hq' := Hqp) ε d)
  • mkPshRestrFrameStep PC (mkPshRestrFrames (proj1PshDepsCohs PC) C) HC
      q Hq Hqp ε d.
Proof.
  now exact (pshRestrAtSourceBase (mkPshDepsRestrCore PC (C; HC))
    q Hq e h HZ Hqp ε d).
Defined.

Lemma edgeA_base {AA B: Type} {P': B -> Type} (F: AA -> B)
  (s1: forall a, P' (F a)) {x y: AA} (e: x = y):
  f_equal (fun z: {a: AA &T P' (F a)} => (F z.1; z.2))
    (@eq_existT_curried AA (fun a => P' (F a)) x y (s1 x) (s1 y) e
       (f_equal_dep (fun a => P' (F a)) s1 e))
  = f_equal (fun a: AA => (F a; s1 a)) e.
Proof. now destruct e. Defined.

Section PlainSelectedPshHex.
Context {m p k} (PC2: PshDepsCohs2 m p.+1 k)
  (PCX: PshDepsCohsExtension m PC2 PC2.(_pExtraDepsCohs)).
Let PCps := PC2.(_pshDepsCohs).
Let PC1 := proj1PshDepsCohs (mkPshDepsCohsNext PCX).
Let PC0 := proj1PshDepsCohs PC1.
Context (C: mkPshRestrCohData PC1).
Let Qprev := (mkPshRestrFramesAndCohs PC0).(PshRestrFramesDef) C.1.
Let Qp := (mkPshRestrFramesAndCohs (proj1PshDepsCohs PCps))
  .(PshRestrFramesDef) PC2.(_pshRestrCohs).1.
Let Fr1 := fun a: psh.(G0) m.+1 => (mkPshFrame PCps.(_pshDeps) a).1.
Let Lay1 := fun a: psh.(G0) m.+1 => (mkPshFrame PCps.(_pshDeps) a).2.
Let Fr2p := fun a: psh.(G0) m.+2 => (mkPshFrame PC1.(_pshDeps) a).1.
Let RFp := PC1.(_pshDeps).(_pdeps).(_restrFrames).2.
Context (q: nat) (Hq: q <= k) (r: nat) (Hr: r <= q)
  (Hqp: q.+2 + p <= m.+2) (ε ω: arity) (d: psh.(G0) m.+3).
Let Hrqp := leR_add_mono_r (⇑ Hr) p ↕ ⇓ Hqp.
Let D2 := psh.(GFace) m.+2 (q.+2 + p) Hqp ε d.
Let D1 := psh.(GFace) m.+2 (r.+1 + p) (↑ Hrqp) ω d.
Let Dprev := (mkPshFramesNext PC0 Qprev).2 d.
Let Kface := psh.(GFaceCoh) m.+1 (q.+1 + p) (⇓ Hqp) (r.+1 + p)
  (leR_add_mono_r (⇑ Hr) p) ε ω d.
Let edge2 := Qp.2 r.+1 (⇑ (Hr ↕ Hq)) Hrqp ω D2.
Let edge3 := f_equal (RFp r.+1 (⇑ (Hr ↕ Hq)) ω)
  (Qprev.2 q.+2 (⇑ (⇑ Hq)) Hqp ε d).
Let edge1' := Qp.2 q.+1 (⇑ Hq) (⇓ Hqp) ε D1.
Let edge2' := f_equal (RFp q.+1 (⇑ Hq) ε)
  (Qprev.2 r.+1 (⇑ (↑ (Hr ↕ Hq))) (↑ Hrqp) ω d).
Let edge3' := PC1.(_pCohs).2 q.+1 (⇑ Hq) r.+1 (⇑ Hr) ε ω Dprev.1.
Let layer2 := mkPshRestrLayer PCps Qp PC2.(_pshRestrCohs).2 r
  (Hr ↕ Hq) Hrqp ω D2.
Let layer3 := sigT_map_eq
  (P := fun a => GDom (mkLayer PC1.(_pshDeps).(_pdeps).(_restrFrames).2 a))
  (Q := fun a => GDom (mkLayer PCps.(_pshDeps).(_pdeps).(_restrFrames).2 a))
  (f := RFp r.+1 (⇑ (Hr ↕ Hq)) ω)
  (mkRestrLayer PCps.(_pRestrPaintings).2 PCps.(_pCohs).2 r (Hr ↕ Hq) ω)
  (mkPshRestrLayer PC1 Qprev C.2 q.+1 (⇑ Hq) Hqp ε d).
Let layer1' := mkPshRestrLayer PCps Qp PC2.(_pshRestrCohs).2
  q Hq (⇓ Hqp) ε D1.
Let layer2' := sigT_map_eq
  (P := fun a => GDom (mkLayer PC1.(_pshDeps).(_pdeps).(_restrFrames).2 a))
  (Q := fun a => GDom (mkLayer PCps.(_pshDeps).(_pdeps).(_restrFrames).2 a))
  (f := RFp q.+1 (⇑ Hq) ε)
  (mkRestrLayer PCps.(_pRestrPaintings).2 PCps.(_pCohs).2 q Hq ε)
  (mkPshRestrLayer PC1 Qprev C.2 r (↑ (Hr ↕ Hq)) (↑ Hrqp) ω d).
Let layer3' := mkCohLayer PC2.(_pCohPaintings).2 PC2.(_pCoh2Frames).2
  q Hq r Hr ε ω Dprev.1 Dprev.2.

Definition PshPlainStepHexParts: Type :=
  section_hex_parts Fr1 Lay1 Kface edge2 layer2 edge3 layer3
    edge1' layer1' edge2' layer2' edge3' layer3'.

Definition mkPshPlainStepHexParts (HP: mkPshRestrPaintingCohData PC2 PCX):
  PshPlainStepHexParts.
Proof.
  unfold PshPlainStepHexParts, section_hex_parts.
  unfold Kface, edge2, edge3, edge1', edge2', edge3', layer2, layer3,
    layer1', layer2', layer3', Dprev, Hrqp.
  refine ((C.2 q.+1 (⇑ Hq) r.+1 (⇑ Hr) Hqp ε ω d); _).
        unshelve eapply (layer_dpath2_eq (Bd := fun a zeta =>
          PCps.(_pshDeps).(_pdeps).(_paintings).2
            (PCps.(_pshDeps).(_pdeps).(_restrFrames).2 0 leR_O zeta a))).
        intro zeta.
        rewrite 2 nth_dpath_trans.
        rewrite (nth_dpath_mkPshRestrLayerSplit PCps Qp
          PC2.(_pshRestrCohs).2 r (⇓ ((⇑ Hr) ↕ (⇑ Hq)))
          (leR_add_mono_r (⇑ Hr) p ↕ ⇓ Hqp) ω D2 zeta).
        rewrite 2 nth_dpath_trans.
        rewrite (nth_dpath_mkPshRestrLayerSplit PCps Qp
          PC2.(_pshRestrCohs).2 q (⇓ (⇑ Hq)) (⇓ Hqp) ε D1 zeta).
        unfold mkCohLayer.
        lazymatch goal with
        | |- context [ @lmap2_rew_eq ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 ?a8 ?a9 ?a10
                         ?a11 ?a12 ?a13 ?a14 ?a15 ?a16 ] =>
          rewrite (@nth_dpath_lmap2_chain a1 a2 a3 a4 a5 a6 a7 a8 a9 a10
                     a11 a12 a13 a14 a15 a16 zeta)
        end.
        rewrite (nth_dpath_map_chain
          (Bd := fun a zeta0 => PC1.(_pshDeps).(_pdeps).(_paintings).2
             (PC1.(_pshDeps).(_pdeps).(_restrFrames).2 0 leR_O zeta0 a))
          (Bd' := fun a zeta0 => PCps.(_pshDeps).(_pdeps).(_paintings).2
             (PCps.(_pshDeps).(_pdeps).(_restrFrames).2 0 leR_O zeta0 a))
          (f := PC1.(_pshDeps).(_pdeps).(_restrFrames).2 r.+1 ((⇑ Hr) ↕ (⇑ Hq)) ω)
          (G := fun a zeta0 c =>
             rew [fun x => PCps.(_pshDeps).(_pdeps).(_paintings).2 x]
               PCps.(_pCohs).2 r (⇓ ((⇑ Hr) ↕ (⇑ Hq))) 0 leR_O ω zeta0 a in
             PCps.(_pRestrPaintings).2 r (⇓ ((⇑ Hr) ↕ (⇑ Hq))) ω
               (PC1.(_pshDeps).(_pdeps).(_restrFrames).2 0 leR_O zeta0 a) c)
          (mkPshRestrLayer PC1 Qprev C.2
             q.+1 (⇓ (⇑ (⇑ Hq))) Hqp ε d) zeta).
        rewrite (nth_dpath_map_chain
          (Bd := fun a zeta0 => PC1.(_pshDeps).(_pdeps).(_paintings).2
             (PC1.(_pshDeps).(_pdeps).(_restrFrames).2 0 leR_O zeta0 a))
          (Bd' := fun a zeta0 => PCps.(_pshDeps).(_pdeps).(_paintings).2
             (PCps.(_pshDeps).(_pdeps).(_restrFrames).2 0 leR_O zeta0 a))
          (f := PC1.(_pshDeps).(_pdeps).(_restrFrames).2 q.+1 (⇑ Hq) ε)
          (G := fun a zeta0 c =>
             rew [fun x => PCps.(_pshDeps).(_pdeps).(_paintings).2 x]
               PCps.(_pCohs).2 q (⇓ (⇑ Hq)) 0 leR_O ε zeta0 a in
             PCps.(_pRestrPaintings).2 q (⇓ (⇑ Hq)) ε
               (PC1.(_pshDeps).(_pdeps).(_restrFrames).2 0 leR_O zeta0 a) c)
          (mkPshRestrLayer PC1 Qprev C.2
             r (⇓ (↑ ((⇑ Hr) ↕ (⇑ Hq)))) (↑ (leR_add_mono_r (⇑ Hr) p ↕ ⇓ Hqp)) ω d) zeta).
        rewrite (nth_dpath_mkPshRestrLayerSec PC1 Qprev
          C.2 q.+1 (⇓ (⇑ (⇑ Hq))) Hqp ε d zeta).
        rewrite (nth_dpath_mkPshRestrLayerSec PC1 Qprev
          C.2 r (⇓ (↑ ((⇑ Hr) ↕ (⇑ Hq))))
          (↑ (leR_add_mono_r (⇑ Hr) p ↕ ⇓ Hqp)) ω d zeta).
        rewrite (nth_dpath_f_equal_dep_sigT
          (Bd := fun a (zeta0: arity) =>
             PCps.(_pshDeps).(_pdeps).(_paintings).2
               (PCps.(_pshDeps).(_pdeps).(_restrFrames).2 0 leR_O zeta0 a))
          (fun y => (mkPshFrame PCps.(_pshDeps) y).1)
          (fun y => (mkPshFrame PCps.(_pshDeps) y).2)
          (psh.(GFaceCoh) m.+1 (q.+1 + p) (⇓ Hqp) (r.+1 + p)
             (leR_add_mono_r (⇑ Hr) p) ε ω d) zeta).
        pose (bnd := ⇓ PCps.(_pshDeps).(_pshBound)).
        pose (HQ := ⇓ (⇓ Hqp)).
        pose (HR := leR_add_mono_r (⇓ (⇑ Hr)) p).
        pose (HS := leR_add_l (p := p) r).
        rewrite (f_equal_dep_sigT_change_section Fr1 _ _
          (fun a => nth_mkPshFrame PCps.(_pshDeps) a zeta)
          (psh.(GFaceCoh) m.+1 (q.+1 + p) (⇓ Hqp) (r.+1 + p)
             (leR_add_mono_r (⇑ Hr) p) ε ω d)).
        rewrite (f_equal_dep_sigT_apply
          (P := fun b: psh.(G0) m => PCps.(_pshDeps).(_pdeps).(_paintings).2
                  (PCps.(_pshDeps).(_pshFrames).2 b))
          (Q := fun c => PCps.(_pshDeps).(_pdeps).(_paintings).2
                  (PCps.(_pshDeps).(_pdeps).(_restrFrames).2 0 leR_O zeta c))
          (fun a => psh.(GFace) m p bnd zeta a) Fr1
          (fun a x => rew [fun x0 => PCps.(_pshDeps).(_pdeps).(_paintings).2 x0]
              PCps.(_pshDeps).(_pshRestrs).2 0 leR_O bnd zeta a in x)
          (fun a => PCps.(_pshDeps).(_pshPaintings).2
              (psh.(GFace) m p bnd zeta a))
          (psh.(GFaceCoh) m.+1 (q.+1 + p) (⇓ Hqp) (r.+1 + p)
             (leR_add_mono_r (⇑ Hr) p) ε ω d)).
        rewrite (sec_action_as_cohLayer_hex
          (S2A := fun _: psh.(G0) m.+1 => unit) (aL := tt) (aR := tt)
          (fun a => psh.(GFace) m p bnd zeta a)
          PCps.(_pshDeps).(_pshPaintings).2
          (psh.(GFace) m (q+p) HQ ε) (psh.(GFace) m (r+p) (HR ↕ HQ) ω)
          _ _
          (psh.(GFaceCoh) m.+1 (q.+1 + p) (⇓ Hqp) (r.+1 + p)
             (leR_add_mono_r (⇑ Hr) p) ε ω d)
          _ _ _
          (pshFaceCoh2Paste HQ HR HS eq_refl eq_refl eq_refl (⇓ Hqp)
             (leR_add_mono_r (⇑ Hr) p) (leR_add_mono_r (⇑ Hr) p ↕ ⇓ Hqp) ε ω zeta d)).
        pose (RFn := PC1.(_pshDeps).(_pdeps).(_restrFrames).2).
        unfold mkPshRestrLayerChainBsplit, mkPshRestrLayerChainBsec.
        unshelve eapply (rew_coh2Layer_split
          (S0 := fun x => PCps.(_pshDeps).(_pdeps).(_paintings).2 x)
          (rf0 := fun x =>
             PCps.(_pshDeps).(_pdeps).(_restrFrames).2 0 leR_O zeta x)
          (fA := Fr1)
          (SY := fun y => PCps.(_pshDeps).(_pdeps).(_paintings).2
                   (PCps.(_pshDeps).(_pshFrames).2 y))
          (uf0 := fun a => psh.(GFace) m p bnd zeta a)
          (rfq := fun y => PCps.(_pshDeps).(_pshFrames).2 y)
          (Fq := fun _ x => x)
          (gq := fun a => PCps.(_pshDeps).(_pshRestrs).2 0 leR_O bnd zeta a)
          (fB := RFn r.+1 ((⇑ Hr) ↕ (⇑ Hq)) ω)
          (fC := RFn q.+1 (⇑ Hq) ε)
          (ufB := fun a => RFn 0 leR_O zeta a)
          (ufC := fun a => RFn 0 leR_O zeta a)
          (rfs := fun y =>
             PCps.(_pshDeps).(_pdeps).(_restrFrames).2 r (⇓ ((⇑ Hr) ↕ (⇑ Hq))) ω y)
          (rfr := fun y =>
             PCps.(_pshDeps).(_pdeps).(_restrFrames).2 q (⇓ (⇑ Hq)) ε y)
          (Fs := PCps.(_pRestrPaintings).2 r (⇓ ((⇑ Hr) ↕ (⇑ Hq))) ω)
          (Fr := PCps.(_pRestrPaintings).2 q (⇓ (⇑ Hq)) ε)
          (gs := fun a => PCps.(_pCohs).2 r (⇓ ((⇑ Hr) ↕ (⇑ Hq))) 0 leR_O ω zeta a)
          (gr := fun a => PCps.(_pCohs).2 q (⇓ (⇑ Hq)) 0 leR_O ε zeta a)
          (X2A := psh.(G0) m.+1) (S2A := fun _ => unit)
          (rur := psh.(GFace) m (q+p) HQ ε)
          (rusY := psh.(GFace) m (r+p) (HR ↕ HQ) ω)
          (Rr := fun z (_: unit) =>
             PCps.(_pshDeps).(_pshPaintings).2 (psh.(GFace) m (q+p) HQ ε z))
          (RsY := fun z (_: unit) =>
             PCps.(_pshDeps).(_pshPaintings).2
               (psh.(GFace) m (r+p) (HR ↕ HQ) ω z))
          (ruq1 := Fr1)
          (Rq1 := fun z (_: unit) => PC1.(_pshDeps).(_pshPaintings).2 z)
          (KA2 := fun z => PCps.(_pshDeps).(_pshRestrs).2 r (⇓ ((⇑ Hr) ↕ (⇑ Hq)))
                    (HR ↕ HQ) ω z)
          (KA4 := fun z => PCps.(_pshDeps).(_pshRestrs).2 q (⇓ (⇑ Hq)) HQ ε z)
          (HKA2 := fun z (_: unit) =>
             PCps.(_pshRestrPaintings).2 r (⇓ ((⇑ Hr) ↕ (⇑ Hq))) (HR ↕ HQ) ω z)
          (HKA4 := fun z (_: unit) =>
             PCps.(_pshRestrPaintings).2 q (⇓ (⇑ Hq)) HQ ε z)
          (A0 := unit) (a := tt)
          (X2C := mkFrame PC1.(_pshDeps).(_pdeps).(1))
          (S2C := fun dd => (mkPaintings
             (PC1.(_pshDeps).(_pdeps); PC1.(_pExtraDeps))).2 dd)
          (* u0 u1 u2 u3 u4 u5 *)  _ _ _ _ _ _
          (* eU1 eU2 eU3 *)        _ _ _
          (* e2 e4 e6 *)           _ _ _
          (* zs1 zs2 zr1 zr2 zq1 zq2 *) _ _ _ _ _ _
          (* pIs pIr pIq *)        _ _ _
          (* FIs FIr FIq *) (fun _: unit => tt) (fun _: unit => tt)
                            (fun _: unit => _)
          (* pV0 pV1 pV2 pV3 pV4 pV5 *) _ _ _ _ _ _
          (* K1 K3 K5 *) _ _ _
          (* HK1 HK3 HK5 *) _ _ _
          (* HH1 *) (pshFaceCoh2Paste HQ HR HS eq_refl eq_refl eq_refl
             (⇓ Hqp) (leR_add_mono_r (⇑ Hr) p)
             (leR_add_mono_r (⇑ Hr) p ↕ ⇓ Hqp) ε ω zeta d)
          (* HH3 HH5 *) _ _
          (* HH2 HH4 HH6 *) _ _ _
          (* aP kP aQ kQ *) _ eq_refl _ eq_refl).
        + now exact (PC2.(_pshRestrCohs).2 q (⇓ (⇑ Hq)) r (⇓ (⇑ Hr)) (⇓ Hqp) ε ω
            (psh.(GFace) m.+2 p (↑ (↑ (HS ↕ (HR ↕ HQ)))) zeta d)).
        + now exact (HP.2 q (⇓ (⇑ Hq)) r (⇓ (⇑ Hr)) (⇓ Hqp) ε ω
            (psh.(GFace) m.+2 p (↑ (↑ (HS ↕ (HR ↕ HQ)))) zeta d)).
        + now apply (PCps.(_pshDeps).(_pdeps).(_frames).2).(GUIP).
Defined.

Definition mkPshPlainStepSplitLayer (HP: mkPshRestrPaintingCohData PC2 PCX) :=
  section_hex_layer_map_first Fr1 Lay1 Kface edge2 layer2 edge3 layer3
    edge1' layer1' edge2' layer2' edge3' layer3'
    (mkPshPlainStepHexParts HP).1 (mkPshPlainStepHexParts HP).2.

Definition mkPshPlainStepSplitHex (HP: mkPshRestrPaintingCohData PC2 PCX) :=
  eq_existT_curried_hex
    (P1 := fun a: psh.(G0) m.+1 =>
      GDom (mkLayer PCps.(_pshDeps).(_pdeps).(_restrFrames).2 (Fr1 a)))
    (P2 := fun a => GDom (mkLayer PC1.(_pshDeps).(_pdeps).(_restrFrames).2 a))
    (P3 := fun a => GDom (mkLayer PC1.(_pshDeps).(_pdeps).(_restrFrames).2 a))
    (Q := fun a => GDom (mkLayer PCps.(_pshDeps).(_pdeps).(_restrFrames).2 a))
    Fr1 (fun _ u => u)
    (RFp q.+1 (⇑ Hq) ε)
    (mkRestrLayer PCps.(_pRestrPaintings).2 PCps.(_pCohs).2 q Hq ε)
    (RFp r.+1 (⇑ (Hr ↕ Hq)) ω)
    (mkRestrLayer PCps.(_pRestrPaintings).2 PCps.(_pCohs).2 r (Hr ↕ Hq) ω)
    (K1 := Kface)
    (W1 := f_equal_dep
      (fun a: psh.(G0) m.+1 =>
        GDom (mkLayer PCps.(_pshDeps).(_pdeps).(_restrFrames).2 (Fr1 a)))
      Lay1 Kface)
    (K2 := Qprev.2 r.+1 (⇑ (↑ (Hr ↕ Hq))) (↑ Hrqp) ω d)
    (W2 := mkPshRestrLayer PC1 Qprev C.2 r (↑ (Hr ↕ Hq)) (↑ Hrqp) ω d)
    (K3 := Qprev.2 q.+2 (⇑ (⇑ Hq)) Hqp ε d)
    (W3 := mkPshRestrLayer PC1 Qprev C.2 q.+1 (⇑ Hq) Hqp ε d)
    (H2 := edge2) (U2 := layer2) (H1' := edge1') (U1' := layer1')
    (H3' := edge3') (U3' := layer3')
    (mkPshPlainStepHexParts HP).1 (mkPshPlainStepSplitLayer HP).

(** The inverse-index cell is selected from the exact boundary witnesses
    already used by restriction-painting alignment. *)
Definition mkPshPlainStepInverseIndex (HP: mkPshRestrPaintingCohData PC2 PCX):
  mkPshRestrLayerCohTypeAt (mkPshDepsCohsNext PCX) (mkPshRestrFrames PC1 C)
    q Hq r Hr (eq_sym (plus_n_Sm q p)) (eq_sym (plus_n_Sm r p))
    (⇓ Hqp) (leR_add_mono_r (⇑ Hr) p) ε ω d.
Proof.
  pose (HaA := edgeA_base
    (P' := fun x => GDom (mkLayer PCps.(_pshDeps).(_pdeps).(_restrFrames).2 x))
    Fr1 Lay1 Kface).
  pose (HaB := path_compare_target
    (eq_sym (mkPshRestrFrameStep_shift PCps Qp PC2.(_pshRestrCohs).2
      r (Hr ↕ Hq) Hrqp ω D2))
    (pshRestrAt_stepG PCps PC2.(_pshRestrCohs).1 PC2.(_pshRestrCohs).2
      r (Hr ↕ Hq) (eq_sym (plus_n_Sm r p)) (plus_n_Sm r p) Hrqp
      (leR_eq (plus_n_Sm r p) Hrqp) ω D2)).
  pose (HaC := path_compare_target
    (eq_sym (mkPshRestrFrameStep_shift PC1 Qprev C.2 q.+1 (⇑ Hq) Hqp ε d))
    (pshRestrAt_stepG PC1 C.1 C.2 q.+1 (⇑ Hq)
      (f_equal S (eq_sym (plus_n_Sm q p))) (plus_n_Sm q.+1 p) Hqp
      (leR_eq (plus_n_Sm q.+1 p) Hqp) ε d)).
  pose (HaD := path_compare_target
    (eq_sym (mkPshRestrFrameStep_shift PCps Qp PC2.(_pshRestrCohs).2
      q Hq (⇓ Hqp) ε D1))
    (pshRestrAt_stepG PCps PC2.(_pshRestrCohs).1 PC2.(_pshRestrCohs).2
      q Hq (eq_sym (plus_n_Sm q p)) (plus_n_Sm q p) (⇓ Hqp)
      (leR_eq (plus_n_Sm q p) (⇓ Hqp)) ε D1)).
  pose (HaE := path_compare_target
    (eq_sym (mkPshRestrFrameStep_shift PC1 Qprev C.2
      r (↑ (Hr ↕ Hq)) (↑ Hrqp) ω d))
    (pshRestrAt_stepG PC1 C.1 C.2 r (↑ (Hr ↕ Hq))
      (eq_sym (plus_n_Sm r p)) (plus_n_Sm r p) (↑ Hrqp)
      (leR_eq (plus_n_Sm r p) (↑ Hrqp)) ω d)).
  pose (totalR := (mkRestrFrames (depsCohs := pshDepsCohs PCps)).2 r (Hr ↕ Hq) ω).
  pose (totalQ := (mkRestrFrames (depsCohs := pshDepsCohs PCps)).2 q Hq ε).
  now exact (hex_reindex_inverse_cell HaA HaB
    (f_equal (fun path => f_equal totalR path) HaC) HaD
    (f_equal (fun path => f_equal totalQ path) HaE) eq_refl (mkPshPlainStepSplitHex HP)).
Defined.

End PlainSelectedPshHex.


Definition mkPshOwnerFrameHex {m p k} (PC2: PshDepsCohs2 m p.+1 k)
  (PCX: PshDepsCohsExtension m PC2 PC2.(_pExtraDepsCohs))
  (C: mkPshRestrCohData (proj1PshDepsCohs (mkPshDepsCohsNext PCX)))
  (HP: mkPshRestrPaintingCohData PC2 PCX):
  mkPshRestrLayerCohType (mkPshDepsCohsNext PCX)
    (mkPshRestrFrames (proj1PshDepsCohs (mkPshDepsCohsNext PCX)) C) :=
  fun q Hq r Hr Hqp ε ω d =>
    pshCohPointFromAt (mkPshDepsCohsNext PCX)
      (mkPshRestrFrames (proj1PshDepsCohs (mkPshDepsCohsNext PCX)) C)
      q Hq r Hr (eq_sym (plus_n_Sm q p)) (eq_sym (plus_n_Sm r p))
      (⇓ Hqp) (leR_add_shift (⇓ Hqp)) (leR_add_mono_r (⇑ Hr) p) ε ω d
      (mkPshPlainStepInverseIndex PC2 PCX C q Hq r Hr (leR_add_shift Hqp) ε ω d HP).

Lemma mkPshOwnerFrameHex_toAt {m p k} (PC2: PshDepsCohs2 m p.+1 k)
  (PCX: PshDepsCohsExtension m PC2 PC2.(_pExtraDepsCohs))
  (C: mkPshRestrCohData (proj1PshDepsCohs (mkPshDepsCohsNext PCX)))
  (HP: mkPshRestrPaintingCohData PC2 PCX)
  q (Hq: q <= k) r (Hr: r <= q) (Hqp: q.+2 + p <= m.+2)
  (ε ω: arity) (d: psh.(G0) m.+3):
  pshRestrCohsAt (mkPshDepsCohsNext PCX)
    (mkPshRestrFrames (proj1PshDepsCohs (mkPshDepsCohsNext PCX)) C)
    (mkPshOwnerFrameHex PC2 PCX C HP) q Hq r Hr
    (eq_sym (plus_n_Sm q p)) (eq_sym (plus_n_Sm r p))
    (⇓ Hqp) (leR_add_mono_r (⇑ Hr) p) ε ω d =
  mkPshPlainStepInverseIndex PC2 PCX C q Hq r Hr Hqp ε ω d HP.
Proof.
  unfold pshRestrCohsAt, mkPshOwnerFrameHex.
  now exact (pshCohPoint_to_from (mkPshDepsCohsNext PCX)
    (mkPshRestrFrames (proj1PshDepsCohs (mkPshDepsCohsNext PCX)) C)
    q Hq r Hr (eq_sym (plus_n_Sm q p)) (eq_sym (plus_n_Sm r p))
    (leR_eq (plus_n_Sm q p) (⇓ Hqp)) (⇓ Hqp)
    (leR_add_mono_r (⇑ Hr) p) ε ω d
    (mkPshPlainStepInverseIndex PC2 PCX C q Hq r Hr Hqp ε ω d HP)).
Defined.

Fixpoint mkPshRestrCohsNext {m p k} (PC2: PshDepsCohs2 m p k)
  (PCX: PshDepsCohsExtension m PC2 PC2.(_pExtraDepsCohs))
  (HP: mkPshRestrPaintingCohData PC2 PCX):
  mkPshRestrCohData (mkPshDepsCohsNext PCX).
Proof.
  destruct p.
  - unshelve econstructor.
    + now exact tt.
    + intros q Hq r Hr Hqp ε ω d.
      cbn.
      now destruct (psh.(GFaceCoh) m.+1 (q + 0) (⇓ Hqp) (r + 0) _ ε ω d).
  - unshelve econstructor.
    + now exact (mkPshRestrCohsNext m p k.+1 (proj1PshDepsCohs2 PC2)
               (AddPshCohDep PC2 PCX) HP.1).
    + now exact (mkPshOwnerFrameHex PC2 PCX
        (mkPshRestrCohsNext m p k.+1 (proj1PshDepsCohs2 PC2)
          (AddPshCohDep PC2 PCX) HP.1) HP).
Defined.

(** The next stage's presheaf filler.

    It is the filler of the [DepsRestr] the next stage determines, and that
    [DepsRestr] depends on the stage only through the three fields
    [mkPshDepsCohs2Next]'s own [_pshDepsCohs] and [_pshRestrCohs] use.  Naming
    it separately is what keeps the level-2 extension below non-circular: the
    extension's filler is this term, and this term does not mention the
    extension. *)

Definition pshFiller3 {m p} (PC3: PshDepsCohs3 m p 0) :=
  mkPshFiller (mkPshDepsRestrCore
    (mkPshDepsCohsNext PC3.(_pshExtraDepsCohs))
    (mkPshRestrCohsNext PC3.(_pshDepsCohs2) PC3.(_pshExtraDepsCohs)
       PC3.(_pshRestrPaintingCohs))).

(** The presheaf realization of the [mkDepsCohs2] step: the next stage of
    the ladder's second rung.  Its indexed fields are the indexed
    constructions applied to the level-2 extension, and its
    restriction-frame coherences are the stage construction above, fed with
    the stage's painting 2-coherences.

    The level-2 extension [XC] and the indexed 2-coherence paintings [C2P] are
    arguments rather than fields of [PshDepsCohs3].  They have to be: the
    recursion that builds the next rung's painting 2-coherences descends the
    stage tower by destructing the extension below, which generalizes [XC]
    away from any field it might be pinned to, and [C2P] is typed over [XC]. *)

Definition mkPshDepsCohs2Next {m p k} (PC3: PshDepsCohs3 m p k)
  (XC: DepsCohs2Extension p k (pshDepsCohs2 PC3.(_pshDepsCohs2)))
  (C2P: mkCoh2PaintingTypes XC):
  PshDepsCohs2 m.+1 p.+1 k := {|
  _pshDepsCohs := mkPshDepsCohsNext PC3.(_pshExtraDepsCohs);
  _pExtraDepsCohs := mkExtraCohs XC;
  _pCohPaintings := mkCohPaintings XC;
  _pCoh2Frames := mkCoh2Frames XC C2P;
  _pshRestrCohs := mkPshRestrCohsNext PC3.(_pshDepsCohs2)
    PC3.(_pshExtraDepsCohs) PC3.(_pshRestrPaintingCohs);
|}.

(** Presheaf data for [DepsCohs2Extension], and its realization as a
    [DepsCohsExtension] one stage up.

    These are to the second rung what [PshDepsCohsExtension] and
    [mkPshExtraDeps] are to the first: the inductive pins the extension's
    filler to the one the presheaf construction produces, and the fixpoint
    transports a level-2 extension to the level-1 extension of the next
    stage, so that [mkExtraCohs] has a presheaf counterpart.

    The indexed 2-coherence paintings travel with the extension, one
    [mkCoh2PaintingType] per stage, so that descending a stage keeps them
    aligned with the level-2 extension. *)

Inductive PshDepsCohs3Extension (m: nat):
  forall {p k} (PC3: PshDepsCohs3 m p k)
    (XC: DepsCohs2Extension p k (pshDepsCohs2 PC3.(_pshDepsCohs2))),
  mkCoh2PaintingTypes XC -> Type :=
| TopPshCoh3Dep {p} {PC3: PshDepsCohs3 m p 0}
    (C2P: mkCoh2PaintingTypes
       (@TopCoh2Dep p (pshDepsCohs2 PC3.(_pshDepsCohs2)) (pshFiller3 PC3))):
    PshDepsCohs3Extension m PC3
      (@TopCoh2Dep p (pshDepsCohs2 PC3.(_pshDepsCohs2)) (pshFiller3 PC3)) C2P
| AddPshCoh3Dep {p k} (PC3: PshDepsCohs3 m p.+1 k)
    {XC: DepsCohs2Extension p.+1 k (pshDepsCohs2 PC3.(_pshDepsCohs2))}
    {C2P: mkCoh2PaintingTypes XC}:
    PshDepsCohs3Extension m PC3 XC C2P ->
    PshDepsCohs3Extension m (proj1PshDepsCohs3 PC3)
      (AddCoh2Dep (pshDepsCohs2 PC3.(_pshDepsCohs2)) XC) C2P.1.

Arguments TopPshCoh3Dep {m p PC3} C2P.
Arguments AddPshCoh3Dep {m p k} PC3 {XC C2P} _.

Fixpoint mkPshExtraCohs {m p k} {PC3: PshDepsCohs3 m p k}
  {XC: DepsCohs2Extension p k (pshDepsCohs2 PC3.(_pshDepsCohs2))}
  {C2P: mkCoh2PaintingTypes XC}
  (PCX3: PshDepsCohs3Extension m PC3 XC C2P):
  PshDepsCohsExtension m.+1 (mkPshDepsCohs2Next PC3 XC C2P)
    (mkExtraCohs XC) :=
  match PCX3 with
  | TopPshCoh3Dep _ => TopPshCohDep
  | AddPshCoh3Dep PC3' PCX3' =>
      AddPshCohDep (mkPshDepsCohs2Next PC3' _ _) (mkPshExtraCohs PCX3')
  end.

(** Restriction data at a dimension carried by a path

    Every statement of the presheaf ladder computes its face dimension from the
    index and the stage: [mkPshRestrTypesStep] and [mkPshRestrPaintingType] both
    read [psh.(GFace) m (q + p) …], and the bound is [SProp], so the dimension is
    not a parameter anywhere and a dimension path can never be destructed.  The
    recursion that builds the painting 2-coherences below needs exactly that,
    because descending the extension trades one unit of [q] for one of the
    stage and [q.+1 + p] is only propositionally [q + p.+1].

    The companions here restate the data at a dimension variable [QQ] together
    with a path [q + p = QQ].  They are [match]es on the path, so at [eq_refl]
    they reduce to the stored forms and the derived statements are
    definitionally the stored ones .

    Presheaf-side data needs no companion: [psh.(GFace)] and [psh.(GFaceCoh)]
    take the dimension as an explicit [nat]. *)

Definition pshRestrPaintingAt {m p k} (P: PshDepsRestr m p.+1 k)
  {X: DepsRestrExtension p.+1 k P.(_pdeps)} (PX: PshDepsExtension m P X)
  {restrPaintings: mkRestrPaintingTypes X}
  (RP: mkPshRestrPaintingType P PX restrPaintings)
  q (Hq: q <= k) {QQ} (e: q + p = QQ) (HQ: QQ <= m) (ε: arity)
  (d: psh.(G0) m.+1):
  rew [P.(_pdeps).(_paintings).2] pshRestrAt P.(_pshRestrs) q Hq e HQ ε d in
    P.(_pshPaintings).2 (psh.(GFace) m QQ HQ ε d) =
  restrPaintings.2 q Hq ε (mkPshFrame (proj1PshDepsRestr P) d)
    (mkPshPainting (AddPshDep P PX) d) :=
  match e as e0 in _ = z return forall Hz: z <= m,
    rew [P.(_pdeps).(_paintings).2] pshRestrAt P.(_pshRestrs) q Hq e0 Hz ε d in
      P.(_pshPaintings).2 (psh.(GFace) m z Hz ε d) =
    restrPaintings.2 q Hq ε (mkPshFrame (proj1PshDepsRestr P) d)
      (mkPshPainting (AddPshDep P PX) d)
  with
  | eq_refl => fun Hz => RP q Hq Hz ε d
  end HQ.

Definition mkPshRestrPaintingAt {m p k} {PC2: PshDepsCohs2 m p k}
  {XC: DepsCohsExtension p k (pshDepsCohs PC2.(_pshDepsCohs))}
  (PCX: PshDepsCohsExtension m PC2 XC)
  q (Hq: q <= k) {QQ} (e: q + p = QQ) (HQ: QQ <= m.+1) (ε: arity)
  (d: psh.(G0) m.+2) :=
  pshRestrPaintingAt (mkPshDepsRestr PC2) (mkPshExtraDeps PCX)
    (mkPshRestrPainting PCX) q Hq e HQ ε d.

Definition mkPshRestrPaintingCohTypeAt {m p k} (PC2: PshDepsCohs2 m p.+1 k)
  (PCX: PshDepsCohsExtension m PC2 PC2.(_pExtraDepsCohs))
  q (Hq: q <= k) r (Hr: r <= q) {QQ RR}
  (e1: q + p = QQ) (e2: r + p = RR)
  (HQ: QQ <= m) (HRQ: RR <= QQ)
  (ε ω: arity) (d: psh.(G0) m.+2): Type :=
  let Pt := fun x =>
    GDom (PC2.(_pshDepsCohs).(_pshDeps).(_pdeps).(_paintings).2 x) in
  rew [fun π => rew [Pt] π in _ = _]
      (pshRestrCohsAt PC2.(_pshDepsCohs)
         (mkPshRestrFrames (proj1PshDepsCohs PC2.(_pshDepsCohs))
            PC2.(_pshRestrCohs).1)
         PC2.(_pshRestrCohs).2 q Hq r Hr e1 e2 HQ HRQ ε ω d) in
  (sigT_map_eq (Q := Pt)
     (f := PC2.(_pshDepsCohs).(_pshDeps).(_pshFrames).2)
     (fun (_: psh.(G0) m) x => x)
     (f_equal_dep
        (fun y => GDom (PC2.(_pshDepsCohs).(_pshDeps).(_pdeps).(_paintings).2
           (PC2.(_pshDepsCohs).(_pshDeps).(_pshFrames).2 y)))
        PC2.(_pshDepsCohs).(_pshDeps).(_pshPaintings).2
        (psh.(GFaceCoh) m QQ HQ RR HRQ ε ω d))
   ⊙[Pt] (pshRestrPaintingAt PC2.(_pshDepsCohs).(_pshDeps)
        PC2.(_pshDepsCohs).(_pshExtraDeps)
        PC2.(_pshDepsCohs).(_pshRestrPaintings).2 r (Hr ↕ Hq) e2 (HRQ ↕ HQ) ω
        (psh.(GFace) m.+1 QQ.+1 (⇑ HQ) ε d)
      ⊙[Pt] sigT_map_eq (Q := Pt)
          (PC2.(_pshDepsCohs).(_pRestrPaintings).2 r (Hr ↕ Hq) ω)
          (mkPshRestrPaintingAt (AddPshCohDep PC2 PCX) q.+1 (⇑ Hq)
             (f_equal S e1) (⇑ HQ) ε d))) =
  pshRestrPaintingAt PC2.(_pshDepsCohs).(_pshDeps)
    PC2.(_pshDepsCohs).(_pshExtraDeps)
    PC2.(_pshDepsCohs).(_pshRestrPaintings).2 q Hq e1 HQ ε
    (psh.(GFace) m.+1 RR (↑ (HRQ ↕ HQ)) ω d)
  ⊙[Pt] (sigT_map_eq (Q := Pt)
       (PC2.(_pshDepsCohs).(_pRestrPaintings).2 q Hq ε)
       (mkPshRestrPaintingAt (AddPshCohDep PC2 PCX) r (↑ (Hr ↕ Hq)) e2
          (↑ (HRQ ↕ HQ)) ω d)
     ⊙[Pt] PC2.(_pCohPaintings).2 q Hq r Hr ε ω
         ((mkPshFrames (proj1PshDepsRestr
             (proj1PshDepsRestr (mkPshDepsRestr PC2)))).2 d)
         (mkPshPainting
            (AddPshDep (proj1PshDepsRestr (mkPshDepsRestr PC2))
               (AddPshDep (mkPshDepsRestr PC2) (mkPshExtraDeps PCX))) d)).

Lemma cohTypeAt_refl {m p k} (PC2: PshDepsCohs2 m p.+1 k)
  (PCX: PshDepsCohsExtension m PC2 PC2.(_pExtraDepsCohs)):
  (forall q (Hq: q <= k) r (Hr: r <= q) QQ RR (e1: q + p = QQ) (e2: r + p = RR)
     (HQ: QQ <= m) (HRQ: RR <= QQ) (ε ω: arity) (d: psh.(G0) m.+2),
   mkPshRestrPaintingCohTypeAt PC2 PCX q Hq r Hr e1 e2 HQ HRQ ε ω d) ->
  mkPshRestrPaintingCohType PC2 PCX.
Proof.
  intros H q Hq r Hr Hqp ε ω d.
  now exact (H q Hq r Hr _ _ eq_refl eq_refl (⇓ Hqp) (leR_add_mono_r Hr p)
               ε ω d).
Defined.



Lemma pshRestrPaintingAt_alignInv {m p k} (P: PshDepsRestr m p.+1 k)
  {X: DepsRestrExtension p.+1 k P.(_pdeps)} (PX: PshDepsExtension m P X)
  {rp: mkRestrPaintingTypes X} (RP: mkPshRestrPaintingType P PX rp)
  q (Hq: q <= k) {QQ} (e: q + p = QQ)
  (HQ: QQ <= m) (HQ0: q + p <= m) (ε: arity) (d: psh.(G0) m.+1):
  pshRestrPaintingAt P PX RP q Hq e HQ ε d =
  path_reindex_source (rew_align_dep (P := P.(_pdeps).(_paintings).2)
    (f_equal P.(_pshFrames).2 (pshFaceDimIrr (eq_sym e) (Hq := HQ) (Hq' := HQ0) ε d))
    (eq_trans
       (eq_sym (rew_map P.(_pdeps).(_paintings).2 P.(_pshFrames).2
          (pshFaceDimIrr (eq_sym e) (Hq := HQ) (Hq' := HQ0) ε d)
          (P.(_pshPaintings).2 (psh.(GFace) m QQ HQ ε d))))
       (f_equal_dep
          (fun z => P.(_pdeps).(_paintings).2 (P.(_pshFrames).2 z))
          P.(_pshPaintings).2
          (pshFaceDimIrr (eq_sym e) (Hq := HQ) (Hq' := HQ0) ε d)))
    (pshRestrAtSourceInv P q Hq e HQ HQ0 ε d))
    (RP q Hq HQ0 ε d).
Proof.
  destruct e.
  set (p0 := pshRestrAt P.(_pshRestrs) q Hq eq_refl HQ0 ε d).
  set (v0 := P.(_pshPaintings).2 (psh.(GFace) m (q + p) HQ0 ε d)).
  change (RP q Hq HQ0 ε d =
    path_reindex_source
      (rew_align_dep (P := P.(_pdeps).(_paintings).2) (e := p0) (e' := p0)
        (v := v0) (v' := v0) eq_refl eq_refl (eq_sym (eq_trans_refl_l p0)))
      (RP q Hq HQ0 ε d)).
  now exact (eq_sym (f_equal
    (fun c: rew [P.(_pdeps).(_paintings).2] p0 in v0 =
      rew [P.(_pdeps).(_paintings).2] p0 in v0 =>
      path_reindex_source c (RP q Hq HQ0 ε d))
    (rew_align_dep_identity_base (P := P.(_pdeps).(_paintings).2) p0 v0))).
Defined.

Lemma pshRestrPaintingAt_alignGen {m p k} (P: PshDepsRestr m p.+1 k)
  {X: DepsRestrExtension p.+1 k P.(_pdeps)} (PX: PshDepsExtension m P X)
  {rp: mkRestrPaintingTypes X} (RP: mkPshRestrPaintingType P PX rp)
  q (Hq: q <= k) {QQ} (e: q + p = QQ) {h: QQ = q + p} (a: eq_sym e = h)
  (HQ: QQ <= m) (HQ0: q + p <= m) (ε: arity) (d: psh.(G0) m.+1):
  pshRestrPaintingAt P PX RP q Hq e HQ ε d =
  path_reindex_source (rew_align_dep (P := P.(_pdeps).(_paintings).2)
    (f_equal P.(_pshFrames).2 (pshFaceDimIrr h (Hq := HQ) (Hq' := HQ0) ε d))
    (eq_trans
       (eq_sym (rew_map P.(_pdeps).(_paintings).2 P.(_pshFrames).2
          (pshFaceDimIrr h (Hq := HQ) (Hq' := HQ0) ε d)
          (P.(_pshPaintings).2 (psh.(GFace) m QQ HQ ε d))))
       (f_equal_dep
          (fun z => P.(_pdeps).(_paintings).2 (P.(_pshFrames).2 z))
          P.(_pshPaintings).2
          (pshFaceDimIrr h (Hq := HQ) (Hq' := HQ0) ε d)))
    (pshRestrAtSourceGen P q Hq e a HQ HQ0 ε d))
    (RP q Hq HQ0 ε d).
Proof.
  destruct a. now exact (pshRestrPaintingAt_alignInv P PX RP q Hq e HQ HQ0 ε d).
Defined.

Lemma pshRestrPaintingAt_align {m p k} (P: PshDepsRestr m p.+1 k)
  {X: DepsRestrExtension p.+1 k P.(_pdeps)} (PX: PshDepsExtension m P X)
  {rp: mkRestrPaintingTypes X} (RP: mkPshRestrPaintingType P PX rp)
  q (Hq: q <= k) {QQ} (e: q + p = QQ) (h: QQ = q + p)
  (HQ: QQ <= m) (HQ0: q + p <= m) (ε: arity) (d: psh.(G0) m.+1):
  pshRestrPaintingAt P PX RP q Hq e HQ ε d =
  path_reindex_source (rew_align_dep (P := P.(_pdeps).(_paintings).2)
    (f_equal P.(_pshFrames).2 (pshFaceDimIrr h (Hq := HQ) (Hq' := HQ0) ε d))
    (eq_trans
       (eq_sym (rew_map P.(_pdeps).(_paintings).2 P.(_pshFrames).2
          (pshFaceDimIrr h (Hq := HQ) (Hq' := HQ0) ε d)
          (P.(_pshPaintings).2 (psh.(GFace) m QQ HQ ε d))))
       (f_equal_dep
          (fun z => P.(_pdeps).(_paintings).2 (P.(_pshFrames).2 z))
          P.(_pshPaintings).2
          (pshFaceDimIrr h (Hq := HQ) (Hq' := HQ0) ε d)))
    (pshRestrAtSourceBase P q Hq e h HQ HQ0 ε d))
    (RP q Hq HQ0 ε d).
Proof.
  now exact (pshRestrPaintingAt_alignGen P PX RP q Hq e
    (natUIP (eq_sym e) h) HQ HQ0 ε d).
Defined.

(** Restriction-frame paths at a shifted dimension. The dimension path
    and the correction path are independent parameters and are identified
    by natural-number path uniqueness. *)



Lemma pshRestrPaintingAt_rebase {m p k} (P: PshDepsRestr m p.+1 k)
  {X: DepsRestrExtension p.+1 k P.(_pdeps)} (PX: PshDepsExtension m P X)
  {rp: mkRestrPaintingTypes X} (RP: mkPshRestrPaintingType P PX rp)
  q (Hq: q <= k) {QQ} (e: q + p = QQ) (h: QQ = q + p)
  (HQ: QQ <= m) (HQ0: q + p <= m) (ε: arity) (d: psh.(G0) m.+1)
  {g: P.(_pshFrames).2 (psh.(GFace) m QQ HQ ε d) =
      P.(_pdeps).(_restrFrames).2 q Hq ε (mkPshFrame (proj1PshDepsRestr P) d)}
  (Hcohg: g =
     f_equal P.(_pshFrames).2 (pshFaceDimIrr h (Hq := HQ) (Hq' := HQ0) ε d)
     • pshRestrAt P.(_pshRestrs) q Hq eq_refl HQ0 ε d):
  rew <- [fun π => rew [P.(_pdeps).(_paintings).2] π in
            P.(_pshPaintings).2 (psh.(GFace) m QQ HQ ε d) =
          rp.2 q Hq ε (mkPshFrame (proj1PshDepsRestr P) d)
            (mkPshPainting (AddPshDep P PX) d)] (path_compare_target Hcohg (pshRestrAtSourceBase P q Hq e h HQ HQ0 ε d)) in
    pshRestrPaintingAt P PX RP q Hq e HQ ε d
  = path_reindex_source (rew_align_dep (P := P.(_pdeps).(_paintings).2)
      (f_equal P.(_pshFrames).2 (pshFaceDimIrr h (Hq := HQ) (Hq' := HQ0) ε d))
      (eq_trans
         (eq_sym (rew_map P.(_pdeps).(_paintings).2 P.(_pshFrames).2
            (pshFaceDimIrr h (Hq := HQ) (Hq' := HQ0) ε d)
            (P.(_pshPaintings).2 (psh.(GFace) m QQ HQ ε d))))
         (f_equal_dep
            (fun z => P.(_pdeps).(_paintings).2 (P.(_pshFrames).2 z))
            P.(_pshPaintings).2
            (pshFaceDimIrr h (Hq := HQ) (Hq' := HQ0) ε d)))
      Hcohg)
      (RP q Hq HQ0 ε d).
Proof.
  set (Hcoh := pshRestrAtSourceBase P q Hq e h HQ HQ0 ε d).
  rewrite (pshRestrPaintingAt_align P PX RP q Hq e h HQ HQ0 ε d).
  lazymatch goal with
  | |- rew <- [_] _ in (path_reindex_source ?c ?c') = _ =>
      rewrite (source_reindex_rebase (P := P.(_pdeps).(_paintings).2)
        (path_compare_target Hcohg (pshRestrAtSourceBase P q Hq e h HQ HQ0 ε d)) c c')
  end.
  lazymatch goal with
  | |- path_reindex_source
      (rew <- [_] _ in @rew_align_dep _ _ _ _ _ _ _ ?b _ _ ?hv ?hc) ?cc = _ =>
      now exact (f_equal (fun z => path_reindex_source z cc)
        (rew_align_dep_compare (P := P.(_pdeps).(_paintings).2) b hv hc Hcohg))
  end.
Defined.
(** The presheaf edge's shape.

    Splitting the presheaf painting into a dependent sum presents its action on
    the exchange path as the fibre half [f_equal_dep2]; the induction hypothesis
    has the section's action.  The two agree — at the same dimensions, so this
    bridge carries no dimension content. *)



Lemma edgeA_rebase {AA B: Type} {P': B -> Type} {R': forall b, P' b -> Type}
  (F: AA -> B) (s1: forall a, P' (F a)) (s2: forall a, R' (F a) (s1 a))
  {x y: AA} (e: x = y):
  rew <- [fun π: (F x; s1 x) = (F y; s1 y) =>
            rew [fun z: {b: B &T P' b} => R' z.1 z.2] π in
              (s2 x: (fun z: {b: B &T P' b} => R' z.1 z.2) (F x; s1 x)) = s2 y]
      (edgeA_base F s1 e) in
    (@sigT_map_eq AA {b: B &T P' b} (fun a => R' (F a) (s1 a))
       (fun z: {b: B &T P' b} => R' z.1 z.2) (fun a => (F a; s1 a))
       (fun a u => u) x y (s2 x) (s2 y) e
       (f_equal_dep (fun a => R' (F a) (s1 a)) s2 e))
  = @sigT_map_eq {a: AA &T P' (F a)} {b: B &T P' b}
      (fun z => R' (F z.1) z.2) (fun z => R' z.1 z.2)
      (fun z => (F z.1; z.2)) (fun z v => v)
      (x; s1 x) (y; s1 y) (s2 x) (s2 y)
      (@eq_existT_curried AA (fun a => P' (F a)) x y (s1 x) (s1 y) e
         (f_equal_dep (fun a => P' (F a)) s1 e))
      (@f_equal_dep2 AA (fun a => P' (F a)) (fun a u => R' (F a) u) s1 s2 x y e).
Proof. now destruct e. Defined.

(** The presheaf painting 2-coherence of the next stage, stated at a dimension
    carried by a path.

    The dimension has to be a variable: the recursion descends the extension,
    which trades one unit of [q] for one of the stage, and [q.+1 + p] is only
    propositionally [q + p.+1].  With the dimension abstracted, the goal and
    the induction hypothesis are about the same [QQ] and differ only in the
    path, which the step bridges above turn into the corrections that
    [mkPshRestrPainting]'s successor branch inserts. *)

Definition mkPshCoh2PaintingAt {m}: forall p k (PC3: PshDepsCohs3 m p k)
  (XC: DepsCohs2Extension p k (pshDepsCohs2 PC3.(_pshDepsCohs2)))
  (C2P: mkCoh2PaintingTypes XC)
  (PCX3: PshDepsCohs3Extension m PC3 XC C2P)
  q (Hq: q <= k) r (Hr: r <= q) QQ RR (e1: q + p = QQ) (e2: r + p = RR)
  (HQQ: QQ <= m.+1) (HRR: RR <= QQ) (ε ω: arity) (d: psh.(G0) m.+3),
  mkPshRestrPaintingCohTypeAt (mkPshDepsCohs2Next PC3 XC C2P)
    (mkPshExtraCohs PCX3) q Hq r Hr e1 e2 HQQ HRR ε ω d.
Proof.
  intros p k PC3 XC C2P PCX3 q Hq r.
  generalize dependent q.
  generalize dependent PCX3. generalize dependent C2P.
  generalize dependent XC. generalize dependent PC3.
  generalize dependent k. generalize dependent p.
  induction r as [|r IHr].
  - intros p k PC3 XC C2P PCX3 q Hq Hr QQ RR e1 e2 HQQ HRR ε ω d.
    destruct e1, e2.
    unfold mkPshRestrPaintingCohTypeAt.
    cbn [mkPshRestrPaintingAt pshRestrPaintingAt pshRestrAt pshRestrCohsAt].
    set (PCb := (mkPshDepsCohs2Next PC3 XC C2P).(_pshDepsCohs)) in *.
    rewrite (nth_dpath_sigT_fst (θ := ω)
      (P := fun x => PCb.(_pshDeps).(_pdeps).(_paintings).2 x)
      (rf0 := fun a x => PCb.(_pshDeps).(_pdeps).(_restrFrames).2 0 leR_O a x)
      (R := fun d0 a => mkPainting PCb.(_pExtraDeps) (d0; a))).
    lazymatch goal with
    | |- context [ mkPshRestrLayer ?PC ?Q ?HC ?q0 ?Hq0 ?Hqp0 ?e0 ?d0 ] =>
      rewrite (nth_dpath_mkPshRestrLayer PC Q HC q0 Hq0 Hqp0 e0 d0 ω)
    end.
    unfold mkPshRestrLayerChain.
    rewrite mkPshRestrLayerChainB_split.
    unfold mkPshRestrLayerChainBsplit.
    unshelve eapply (rew_coh2Painting_restr0_edges
      (TU2 := psh.(G0) m.+1)
      (P := fun x : PCb.(_pshDeps).(_pdeps).(_frames).2 =>
              PCb.(_pshDeps).(_pdeps).(_paintings).2 x)
      (r0 := fun x => PCb.(_pshDeps).(_pdeps).(_restrFrames).2 0 leR_O ω x)
      (rq := PCb.(_pshDeps).(_pshFrames).2)
      (rr := fun x => PCb.(_pshDeps).(_pdeps).(_restrFrames).2 q Hq ε x)
      (Sq := fun mm : psh.(G0) m.+1 =>
               PCb.(_pshDeps).(_pdeps).(_paintings).2
                 (PCb.(_pshDeps).(_pshFrames).2 mm))
      (Sr := fun nn =>
               (mkPaintings (PCb.(_pshDeps).(_pdeps); PCb.(_pExtraDeps))).2 nn)
      (fun _ a => a)
      (PCb.(_pRestrPaintings).2 q Hq ε)).
    all: now reflexivity.

  - intros p k PC3 XC C2P PCX3 q Hq Hr QQ RR e1 e2 HQQ HRR ε ω d.
    destruct q; [now destruct (leR_O_contra Hr) |].
    destruct PCX3 as [p0 PC30 C2P0 | p0 k0 PC30 XC0 C2P0 PCX30].
    + now destruct (leR_O_contra Hq).
    + destruct e1, e2.
      unfold mkPshRestrPaintingCohTypeAt.
      cbn [mkPshRestrPaintingAt pshRestrPaintingAt pshRestrAt pshRestrCohsAt].
      assert (Hqp: q.+2 + p0 <= m.+2) by now exact (⇑ HQQ).
      pose (PC2 := PC30.(_pshDepsCohs2)).
      pose (PCX := PC30.(_pshExtraDepsCohs)).
      pose (PCq := PC2.(_pshDepsCohs)).
      pose (PCn := mkPshDepsCohsNext (AddPshCohDep PC2 PCX)).
      pose (PC2n := mkPshDepsCohs2Next (proj1PshDepsCohs3 PC30)
                      (pshDepsCohs2 PC2; XC0)%extradepscohs2 C2P0.1).
      pose (Qp := mkPshRestrFrames (proj1PshDepsCohs PCq) PC2.(_pshRestrCohs).1).
      pose (Qprev := mkPshRestrFrames (proj1PshDepsCohs PCn)
                       PC2n.(_pshRestrCohs).1).
      pose (D2 := psh.(GFace) m.+2 (q.+2 + p0) Hqp ε d).
      pose (D1 := psh.(GFace) m.+2 (r.+1 + p0)
                    (↑ (leR_add_mono_r Hr p0 ↕ ⇓ Hqp)) ω d).
      cbn [mkPshDepsCohs2Next _pshDepsCohs mkPshDepsCohsNext
        _pshRestrPaintings _pRestrPaintings _pCohPaintings _pshPaintings
        mkPshRestrPaintings mkRestrPaintings mkCohPaintings mkPshPaintings
        mkPshRestrPainting mkRestrPainting mkCohPainting mkPshPainting
        proj1PshDepsCohs3 _pshExtraDepsCohs projT2 mkPshDepsRestr
        mkPshDepsRestrCore
        proj1PshDepsCohs2 _pExtraDepsCohs pshDepsCohs _pshDepsCohs2].
      rewrite (f_equal_dep_as_existT
        (fun y => (mkPshFrame PCq.(_pshDeps) y).2)
        (fun y => mkPshPainting PCq.(_pshExtraDeps) y)
        (psh.(GFaceCoh) m.+1 (q.+1 + p0) (⇓ Hqp) (r.+1 + p0)
           (leR_add_mono_r Hr p0) ε ω d)).
      unshelve eapply ((eq_existT_curried_dep_hex_split
        (P' := fun x => (mkLayer PCq.(_pshDeps).(_pdeps).(_restrFrames).2 x).(GDom))
        (R' := fun x l => (mkPainting PCq.(_pExtraDeps) (x; l)).(GDom))
        (P1 := fun a => (mkLayer PCq.(_pshDeps).(_pdeps).(_restrFrames).2
                 (PCn.(_pshDeps).(_pshFrames).2 a)).(GDom))
        (R1 := fun a u => (mkPainting PCq.(_pExtraDeps)
                 (PCn.(_pshDeps).(_pshFrames).2 a; u)).(GDom))
        (P3 := fun dd => (mkLayer PCn.(_pshDeps).(_pdeps).(_restrFrames).2 dd).(GDom))
        (R3 := fun dd l => (mkPainting PCn.(_pExtraDeps) (dd; l)).(GDom))
        (P2 := fun dd => (mkLayer PCn.(_pshDeps).(_pdeps).(_restrFrames).2 dd).(GDom))
        (R2 := fun dd l => (mkPainting PCn.(_pExtraDeps) (dd; l)).(GDom))
        (PCn.(_pshDeps).(_pshFrames).2) (fun a u => u) (fun a u v => v)
        (PCn.(_pshDeps).(_pdeps).(_restrFrames).2 r.+1 (Hr ↕ Hq) ω)
        (fun dd u => mkRestrLayer PCq.(_pRestrPaintings).2 PCq.(_pCohs).2
           r (⇓ (Hr ↕ Hq)) ω dd u)
        (fun dd u v => mkRestrPainting PC2.(_pExtraDepsCohs)
           r (⇓ (Hr ↕ Hq)) ω (dd; u) v)
        (PCn.(_pshDeps).(_pdeps).(_restrFrames).2 q.+1 Hq ε)
        (fun dd u => mkRestrLayer PCq.(_pRestrPaintings).2 PCq.(_pCohs).2
           q (⇓ Hq) ε dd u)
        (fun dd u v => mkRestrPainting PC2.(_pExtraDepsCohs)
           q (⇓ Hq) ε (dd; u) v))).
      1: {
        now exact (mkPshPlainStepSplitLayer PC2 PCX PC2n.(_pshRestrCohs)
          q (⇓ Hq) r (⇓ Hr) Hqp ε ω d PC30.(_pshRestrPaintingCohs)).
      }

      pose proof (IHr p0.+1 k0 PC30 XC0 C2P0 PCX30 q (⇓ Hq) (⇓ Hr) _ _
        (eq_sym (plus_n_Sm q p0)) (eq_sym (plus_n_Sm r p0)) HQQ HRR
        ε ω d) as IH0.
      unfold mkPshRestrPaintingCohTypeAt in IH0.
      cbn [mkPshDepsCohs2Next _pshDepsCohs mkPshDepsCohsNext
        _pshRestrPaintings _pRestrPaintings _pCohPaintings _pshPaintings
        mkPshRestrPaintings mkRestrPaintings mkCohPaintings mkPshPaintings
        mkPshRestrPainting mkRestrPainting mkCohPainting mkPshPainting
        proj1PshDepsCohs3 _pshExtraDepsCohs projT2 mkPshDepsRestr
        mkPshDepsRestrCore
        proj1PshDepsCohs2 _pExtraDepsCohs pshDepsCohs _pshDepsCohs2
        mkPshRestrPaintingAt] in IH0.
      pose (PC2x := mkPshDepsCohs2Next PC30 XC0 C2P0).
      pose (PCXx := mkPshExtraCohs PCX30).
      rewrite (mkPshOwnerFrameHex_toAt PC2 PCX PC2n.(_pshRestrCohs)
        PC30.(_pshRestrPaintingCohs) q (⇓ Hq) r (⇓ Hr) Hqp ε ω d) in IH0.
      (* Each rebase path is chosen from the painting's boundary and the
         dimension-transfer boundary. The displayed law uses those same
         witnesses, so it needs no separate equality of boundary proofs. *)
      (* LHS second edge *)
      lazymatch goal with
      | |- rew [_] _ in (_ ⊙ ((path_reindex_source (@rew_align_dep _ _ _ _ _ _ _ _ _ _ _ ?hcgB) _)
             ⊙ _)) = _ =>
        pose (hcB := pshRestrAt_stepG PCq PC2.(_pshRestrCohs).1
          PC2.(_pshRestrCohs).2 r (⇓ Hr ↕ ⇓ Hq)
          (eq_sym (plus_n_Sm r p0)) (plus_n_Sm r p0) (HRR ↕ HQQ)
          (leR_eq (plus_n_Sm r p0) (HRR ↕ HQQ)) ω D2);
        pose (HaB := path_compare_target hcgB hcB);
        pose proof (pshRestrPaintingAt_rebase (mkPshDepsRestr PC2)
          (mkPshExtraDeps PCX) (mkPshRestrPainting PCX) r (⇓ Hr ↕ ⇓ Hq)
          (eq_sym (plus_n_Sm r p0)) (plus_n_Sm r p0) (HRR ↕ HQQ)
          (leR_eq (plus_n_Sm r p0) (HRR ↕ HQQ)) ω D2 hcgB) as HEB
      end.
      rewrite <- HEB.
      (* RHS first edge *)
      lazymatch goal with
      | |- _ = (path_reindex_source (@rew_align_dep _ _ _ _ _ _ _ _ _ _ _ ?hcgD) _) ⊙ _ =>
        pose (hcD := pshRestrAt_stepG PCq PC2.(_pshRestrCohs).1
          PC2.(_pshRestrCohs).2 q (⇓ Hq) (eq_sym (plus_n_Sm q p0))
          (plus_n_Sm q p0) HQQ (leR_eq (plus_n_Sm q p0) HQQ) ε D1);
        pose (HaD := path_compare_target hcgD hcD);
        pose proof (pshRestrPaintingAt_rebase (mkPshDepsRestr PC2)
          (mkPshExtraDeps PCX) (mkPshRestrPainting PCX) q (⇓ Hq)
          (eq_sym (plus_n_Sm q p0)) (plus_n_Sm q p0) HQQ
          (leR_eq (plus_n_Sm q p0) HQQ) ε D1 hcgD) as HED
      end.
      rewrite <- HED.
      (* LHS third edge *)
      lazymatch goal with
      | |- rew [_] _ in (_ ⊙ (_ ⊙ @sigT_map_eq _ _ ?PC1 ?QC1 ?fC ?gC _ _ _ _ _
            (path_reindex_source (@rew_align_dep _ _ _ _ _ _ _ _ _ _ _ ?hcgC) _))) = _ =>
        pose (hcC := pshRestrAt_stepG PCn PC2n.(_pshRestrCohs).1
          PC2n.(_pshRestrCohs).2 q.+1 (⇑ (⇓ Hq))
          (f_equal S (eq_sym (plus_n_Sm q p0))) (plus_n_Sm q.+1 p0) (⇑ HQQ)
          (leR_eq (plus_n_Sm q.+1 p0) (⇑ HQQ)) ε d);
        pose (HaC := path_compare_target hcgC hcC);
        pose proof (pshRestrPaintingAt_rebase (mkPshDepsRestr PC2n)
          (mkPshExtraDeps (AddPshCohDep PC2x PCXx))
          (mkPshRestrPainting (AddPshCohDep PC2x PCXx)) q.+1 (⇑ (⇓ Hq))
          (f_equal S (eq_sym (plus_n_Sm q p0))) (plus_n_Sm q.+1 p0) (⇑ HQQ)
          (leR_eq (plus_n_Sm q.+1 p0) (⇑ HQQ)) ε d hcgC) as HCin;
        rewrite <- HCin;
        lazymatch type of HCin with
        | rew <- [_] _ in ?cc = _ =>
          rewrite (sigT_map_eq_rebase (P := PC1) (Q := QC1) (f := fC) gC HaC cc)
        end
      end.
      (* RHS second edge *)
      lazymatch goal with
      | |- _ = _ ⊙ (@sigT_map_eq _ _ ?PE1 ?QE1 ?fE ?gE _ _ _ _ _
            (path_reindex_source (@rew_align_dep _ _ _ _ _ _ _ _ _ _ _ ?hcgE) _) ⊙ _) =>
        pose (hcE := pshRestrAt_stepG PCn PC2n.(_pshRestrCohs).1
          PC2n.(_pshRestrCohs).2 r (⇓ (↑ (⇓ Hr ↕ ⇓ Hq)))
          (eq_sym (plus_n_Sm r p0)) (plus_n_Sm r p0) (↑ (HRR ↕ HQQ))
          (leR_eq (plus_n_Sm r p0) (↑ (HRR ↕ HQQ))) ω d);
        pose (HaE := path_compare_target hcgE hcE);
        pose proof (pshRestrPaintingAt_rebase (mkPshDepsRestr PC2n)
          (mkPshExtraDeps (AddPshCohDep PC2x PCXx))
          (mkPshRestrPainting (AddPshCohDep PC2x PCXx)) r
          (⇓ (↑ (⇓ Hr ↕ ⇓ Hq))) (eq_sym (plus_n_Sm r p0)) (plus_n_Sm r p0)
          (↑ (HRR ↕ HQQ)) (leR_eq (plus_n_Sm r p0) (↑ (HRR ↕ HQQ))) ω d
          hcgE) as HEin;
        rewrite <- HEin;
        lazymatch type of HEin with
        | rew <- [_] _ in ?cc = _ =>
          rewrite (sigT_map_eq_rebase (P := PE1) (Q := QE1) (f := fE) gE HaE cc)
        end
      end.
      (* presheaf edge *)
      pose (HaA := edgeA_base
        (P' := fun x => (mkLayer PCq.(_pshDeps).(_pdeps).(_restrFrames).2 x).(GDom))
        PCn.(_pshDeps).(_pshFrames).2
        (fun y: psh.(G0) m.+1 => (mkPshFrame PCq.(_pshDeps) y).2)
        (psh.(GFaceCoh) m.+1 (q.+1 + p0) (⇓ Hqp) (r.+1 + p0)
           (leR_add_mono_r Hr p0) ε ω d)).
      rewrite <- (edgeA_rebase
        (P' := fun x => (mkLayer PCq.(_pshDeps).(_pdeps).(_restrFrames).2 x).(GDom))
        (R' := fun x l => (mkPainting PCq.(_pExtraDeps) (x; l)).(GDom))
        PCn.(_pshDeps).(_pshFrames).2
        (fun y: psh.(G0) m.+1 => (mkPshFrame PCq.(_pshDeps) y).2)
        (fun y: psh.(G0) m.+1 => mkPshPainting PCq.(_pshExtraDeps) y)
        (psh.(GFaceCoh) m.+1 (q.+1 + p0) (⇓ Hqp) (r.+1 + p0)
           (leR_add_mono_r Hr p0) ε ω d)).
      now exact (hex_reindex_recover_dep
        (fun z => GDom (mkPainting PCq.(_pExtraDeps) z))
        _ _ _ _ _ eq_refl _ _ _ _ _ _ _ IH0).

Defined.

Definition mkPshCoh2Painting {m p k} (PC3: PshDepsCohs3 m p k)
  (XC: DepsCohs2Extension p k (pshDepsCohs2 PC3.(_pshDepsCohs2)))
  (C2P: mkCoh2PaintingTypes XC)
  (PCX3: PshDepsCohs3Extension m PC3 XC C2P):
  mkPshRestrPaintingCohType (mkPshDepsCohs2Next PC3 XC C2P)
    (mkPshExtraCohs PCX3) :=
  cohTypeAt_refl (mkPshDepsCohs2Next PC3 XC C2P) (mkPshExtraCohs PCX3)
    (fun q Hq r Hr QQ RR e1 e2 HQQ HRR ε ω d =>
       mkPshCoh2PaintingAt p k PC3 XC C2P PCX3 q Hq r Hr QQ RR e1 e2
         HQQ HRR ε ω d).

(** The painting 2-coherences of every stage of the next level, nested as
    [mkPshRestrPaintingCohData] requires: the stage below is the same
    construction one extension deep, the top one is the rung above. *)

Fixpoint mkPshCoh2Paintings {m p k} (PC3: PshDepsCohs3 m p k)
  (XC: DepsCohs2Extension p k (pshDepsCohs2 PC3.(_pshDepsCohs2)))
  (C2P: mkCoh2PaintingTypes XC)
  (PCX3: PshDepsCohs3Extension m PC3 XC C2P):
  mkPshRestrPaintingCohData (mkPshDepsCohs2Next PC3 XC C2P)
    (mkPshExtraCohs PCX3).
Proof.
  destruct p.
  - now exact (tt; mkPshCoh2Painting PC3 XC C2P PCX3).
  - now exact (mkPshCoh2Paintings m p k.+1 (proj1PshDepsCohs3 PC3)
      (AddCoh2Dep (pshDepsCohs2 PC3.(_pshDepsCohs2)) XC) C2P.1
      (AddPshCoh3Dep PC3 PCX3);
      mkPshCoh2Painting PC3 XC C2P PCX3).
Defined.

(** Presheaf-equipped chains and the computation of faces on
    presheaf-built cells. *)

Inductive PshCohsChain {m P K} (PCTop: PshDepsCohs2 m P K):
  forall {p k}, PshDepsCohs2 m p k -> Type :=
| PshCohsChainNil: PshCohsChain PCTop PCTop
| PshCohsChainCons {p k} {PC: PshDepsCohs2 m p.+1 k}:
    PshCohsChain PCTop PC ->
    PshCohsChain PCTop (proj1PshDepsCohs2 PC).

Arguments PshCohsChainNil {m P K PCTop}.
Arguments PshCohsChainCons {m P K PCTop p k PC} _.

(** The presheaf-generated tower. *)

Definition mkTowerDeps {m} (X: (νGpdAt m.+1).(prefix)):
  DepsRestr m.+1 0 :=
  toDepsRestr ((νGpdAt m.+1).(data) X).(restrFrames).

Class PshTower (m: nat) (X: (νGpdAt m.+1).(prefix)) := {
  _twFrames: mkPshFrameTypes m (mkTowerDeps X).(_frames);
  _twPaintings: mkPshPaintingTypes m _twFrames (mkTowerDeps X).(_paintings);
  _twRestrs: (mkPshRestrTypesAndFrames m leR_refl _twFrames
    _twPaintings).(PshRestrTypesDef) (mkTowerDeps X).(_restrFrames);
}.

Definition towerPshDeps {m X} (T: PshTower m X):
  PshDepsRestr m m.+1 0 := {|
  _pdeps := mkTowerDeps X;
  _pshBound := leR_refl;
  _pshFrames := T.(_twFrames);
  _pshPaintings := T.(_twPaintings);
  _pshRestrs := T.(_twRestrs);
|}.

Definition PshTowerRestrPaintings {m X} (T: PshTower m X): Type :=
  mkPshRestrPaintingTypes (towerPshDeps T) TopPshDep
    (((νGpdAt m.+1).(data) X).(restrPaintings)
      (mkPshFiller (towerPshDeps T))).

Definition towerPshDepsCohs {m X} (T: PshTower m X)
  (rp: PshTowerRestrPaintings T): PshDepsCohs m m.+1 0 := {|
  _pshDeps := towerPshDeps T;
  _pExtraDeps := TopRestrDep (mkPshFiller (towerPshDeps T));
  _pshExtraDeps := TopPshDep;
  _pRestrPaintings := ((νGpdAt m.+1).(data) X).(restrPaintings)
    (mkPshFiller (towerPshDeps T));
  _pshRestrPaintings := rp;
  _pCohs := ((νGpdAt m.+1).(data) X).(cohFrames)
    (mkPshFiller (towerPshDeps T));
|}.

Definition PshTowerRestrCohs {m X} (T: PshTower m X)
  (rp: PshTowerRestrPaintings T): Type :=
  mkPshRestrCohData (towerPshDepsCohs T rp).

Definition towerPshDepsCohs2 {m X} (T: PshTower m X)
  (rp: PshTowerRestrPaintings T) (rc: PshTowerRestrCohs T rp):
  PshDepsCohs2 m m.+1 0 := {|
  _pshDepsCohs := towerPshDepsCohs T rp;
  _pExtraDepsCohs := TopCohDep
    (mkPshFiller (mkPshDepsRestrCore (towerPshDepsCohs T rp) rc));
  _pCohPaintings := ((νGpdAt m.+1).(data) X).(cohPaintings)
    (mkPshFiller (towerPshDeps T))
    (mkPshFiller (mkPshDepsRestrCore (towerPshDepsCohs T rp) rc));
  _pCoh2Frames := ((νGpdAt m.+1).(data) X).(coh2Frames)
    (mkPshFiller (towerPshDeps T))
    (mkPshFiller (mkPshDepsRestrCore (towerPshDepsCohs T rp) rc));
  _pshRestrCohs := rc;
|}.

(** The painting 2-coherences carried by a tower state, one rung above
    [PshTowerRestrCohs]. *)

Definition PshTowerRestrPaintingCohs {m X} (T: PshTower m X)
  (rp: PshTowerRestrPaintings T) (rc: PshTowerRestrCohs T rp): Type :=
  mkPshRestrPaintingCohData (towerPshDepsCohs2 T rp rc)
    (TopPshCohDep (PC2 := towerPshDepsCohs2 T rp rc)).

Definition pshFiller0:
  mkFrame (toDepsRestr ((νGpdAt 0).(data) tt).(restrFrames)) -> HGpd :=
  fun D => {d': psh.(G0) 0 & hgpdOfHSet (hpaths D tt)}.

Definition tower1: PshTower 0 (tt; pshFiller0).
Proof.
  unshelve esplit.
  - now exact (tt; fun _ => tt).
  - now exact (tt; fun d => (d; eq_refl)).
  - now exact (tt; fun q Hq Hqp ε d => eq_refl).
Defined.

(** The bottom restriction-painting comparison is the [nth_lam] correction
    that reads a presheaf frame's layer at an arity, which is what
    [nth_mkPshFrame] names.  Stating it as that lemma rather than proving it by
    a rewrite is what makes the painting 2-coherence below a conversion
    check. *)

Definition tower1RestrPaintings: PshTowerRestrPaintings tower1.
Proof.
  unshelve esplit.
  - now exact tt.
  - intros q Hq Hqp ε d. destruct q.
    + now exact (eq_sym (nth_mkPshFrame (towerPshDeps tower1) d ε)).
    + now destruct (leR_O_contra Hq).
Defined.

Definition tower1RestrCohs:
  PshTowerRestrCohs tower1 tower1RestrPaintings.
Proof.
  unshelve esplit.
  - now exact tt.
  - intros q Hq r Hr Hqp ε ω d.
    now apply unit_UIP.
Defined.

(** The bottom painting 2-coherence.  Both indices are forced to [0] by
    [k = 0], so this is the restriction-at-0 configuration: the two
    [nth_dpath] rewrites turn the third left-hand edge into the layer
    comparison's five-factor chain, read in the presentation whose two halves
    sit in separate slots, and the fused square consumes it.  Its four
    defining hypotheses are conversion checks because every edge involved is
    at index [0], where the constructions compute to their corrections. *)

Definition tower1RestrPaintingCohs:
  PshTowerRestrPaintingCohs tower1 tower1RestrPaintings tower1RestrCohs.
Proof.
  unshelve esplit.
  - now exact tt.
  - intros q Hq r Hr Hqp ε ω d.
    destruct q; [| now destruct (leR_O_contra Hq)].
    destruct r; [| now destruct (leR_O_contra Hr)].
    set (PCb := towerPshDepsCohs tower1 tower1RestrPaintings) in *.
    rewrite (nth_dpath_sigT_fst (θ := ω)
      (P := fun x => PCb.(_pshDeps).(_pdeps).(_paintings).2 x)
      (rf0 := fun a x => PCb.(_pshDeps).(_pdeps).(_restrFrames).2 0 leR_O a x)
      (R := fun d0 a => mkPainting PCb.(_pExtraDeps) (d0; a))).
    lazymatch goal with
    | |- context [ mkPshRestrLayer ?PC ?Q ?HC ?q0 ?Hq0 ?Hqp0 ?e0 ?d0 ] =>
      rewrite (nth_dpath_mkPshRestrLayer PC Q HC q0 Hq0 Hqp0 e0 d0 ω)
    end.
    unfold mkPshRestrLayerChain.
    rewrite mkPshRestrLayerChainB_split.
    unfold mkPshRestrLayerChainBsplit.
    unshelve eapply (rew_coh2Painting_restr0_edges
      (TU2 := psh.(G0) 0)
      (P := fun x : PCb.(_pshDeps).(_pdeps).(_frames).2 =>
              PCb.(_pshDeps).(_pdeps).(_paintings).2 x)
      (r0 := fun x => PCb.(_pshDeps).(_pdeps).(_restrFrames).2 0 leR_O ω x)
      (rq := PCb.(_pshDeps).(_pshFrames).2)
      (rr := fun x => PCb.(_pshDeps).(_pdeps).(_restrFrames).2 0 (⇓ (⇑ Hq)) ε x)
      (Sq := fun mm : psh.(G0) 0 =>
               PCb.(_pshDeps).(_pdeps).(_paintings).2
                 (PCb.(_pshDeps).(_pshFrames).2 mm))
      (Sr := fun nn =>
               (mkPaintings (PCb.(_pshDeps).(_pdeps); PCb.(_pExtraDeps))).2 nn)
      (fun _ a => a)
      (PCb.(_pRestrPaintings).2 0 (⇓ (⇑ Hq)) ε)).
    all: now reflexivity.
Defined.

Definition towerStep {m X} (T: PshTower m X)
  (rp: PshTowerRestrPaintings T) (rc: PshTowerRestrCohs T rp):
  PshTower m.+1 (X; mkPshFiller (towerPshDeps T)) :=
  Build_PshTower m.+1 (X; mkPshFiller (towerPshDeps T))
    (mkPshFrames (towerPshDeps T))
    (mkPshPaintings (TopPshDep (P := towerPshDeps T)))
    (mkPshRestrFrames (towerPshDepsCohs T rp) rc).

Definition towerStepRestrPaintings {m X} (T: PshTower m X)
  (rp: PshTowerRestrPaintings T) (rc: PshTowerRestrCohs T rp):
  PshTowerRestrPaintings (towerStep T rp rc) :=
  mkPshRestrPaintings
    (TopPshCohDep (PC2 := towerPshDepsCohs2 T rp rc)).

(** The next tower state's restriction-frame coherences.  The stage
    construction applies directly: the tower's own [PshDepsCohs2] is the
    stage, its extension is the top constructor, and the painting
    2-coherences carried by the state are the extra parameter. *)

Definition towerStepRestrCohs {m X} (T: PshTower m X)
  (rp: PshTowerRestrPaintings T) (rc: PshTowerRestrCohs T rp)
  (rpc: PshTowerRestrPaintingCohs T rp rc):
  PshTowerRestrCohs (towerStep T rp rc) (towerStepRestrPaintings T rp rc) :=
  mkPshRestrCohsNext (towerPshDepsCohs2 T rp rc) TopPshCohDep rpc.

(** The tower state read as a stage of the second rung, together with the
    level-2 extension and the indexed 2-coherence paintings that the stage
    step consumes.  The extension's filler is [pshFiller3] of the stage, which
    is the same term [towerPshDepsCohs3]'s own next-stage frames are built
    from. *)

Definition towerPshDepsCohs3 {m X} (T: PshTower m X)
  (rp: PshTowerRestrPaintings T) (rc: PshTowerRestrCohs T rp)
  (rpc: PshTowerRestrPaintingCohs T rp rc): PshDepsCohs3 m m.+1 0 := {|
  _pshDepsCohs2 := towerPshDepsCohs2 T rp rc;
  _pshExtraDepsCohs := TopPshCohDep;
  _pshRestrPaintingCohs := rpc;
|}.

Definition towerPshExtra3 {m X} (T: PshTower m X)
  (rp: PshTowerRestrPaintings T) (rc: PshTowerRestrCohs T rp)
  (rpc: PshTowerRestrPaintingCohs T rp rc):
  DepsCohs2Extension m.+1 0
    (pshDepsCohs2 (towerPshDepsCohs3 T rp rc rpc).(_pshDepsCohs2)) :=
  @TopCoh2Dep m.+1 (pshDepsCohs2 (towerPshDepsCohs2 T rp rc))
    (pshFiller3 (towerPshDepsCohs3 T rp rc rpc)).

Definition towerPshCoh2Paintings {m X} (T: PshTower m X)
  (rp: PshTowerRestrPaintings T) (rc: PshTowerRestrCohs T rp)
  (rpc: PshTowerRestrPaintingCohs T rp rc):
  mkCoh2PaintingTypes (towerPshExtra3 T rp rc rpc) :=
  ((νGpdAt m.+1).(data) X).(coh2Paintings)
    (mkPshFiller (towerPshDeps T))
    (mkPshFiller (mkPshDepsRestrCore (towerPshDepsCohs T rp) rc))
    (pshFiller3 (towerPshDepsCohs3 T rp rc rpc)).

(** The next tower state is the stage construction applied to the tower
    data, so its painting 2-coherences specialize the stage result. *)

Definition towerStepRestrPaintingCohs {m X} (T: PshTower m X)
  (rp: PshTowerRestrPaintings T) (rc: PshTowerRestrCohs T rp)
  (rpc: PshTowerRestrPaintingCohs T rp rc):
  PshTowerRestrPaintingCohs (towerStep T rp rc)
    (towerStepRestrPaintings T rp rc) (towerStepRestrCohs T rp rc rpc) :=
  mkPshCoh2Paintings (towerPshDepsCohs3 T rp rc rpc)
    (towerPshExtra3 T rp rc rpc) (towerPshCoh2Paintings T rp rc rpc)
    (TopPshCoh3Dep (towerPshCoh2Paintings T rp rc rpc)).

(** The forward map.  A tower state is a quadruple — tower, restriction
    paintings, restriction coherences, painting 2-coherences — one component
    more than on the νSet side, because the groupoid tower carries the painting
    2-coherences.  All the bonding equations are [eq_refl]. *)

Definition PshState (l: nat): (νGpdAt l).(prefix) -> Type :=
  match l with
  | 0 => fun _ => unit
  | l.+1 => fun X => {T: PshTower l X &T
      {rp: PshTowerRestrPaintings T &T
       {rc: PshTowerRestrCohs T rp &T PshTowerRestrPaintingCohs T rp rc}}}
  end.

Definition pshExtend (l: nat):
  forall (X: (νGpdAt l).(prefix)), PshState l X ->
  {E: mkExtensionType X &T PshState l.+1 (X; E)} :=
  match l return forall X: (νGpdAt l).(prefix), PshState l X ->
    {E: mkExtensionType X &T PshState l.+1 (X; E)} with
  | 0 => fun X =>
    match X as X0 return PshState 0 X0 ->
      {E: mkExtensionType (X0: (νGpdAt 0).(prefix)) &T
       PshState 1 ((X0: (νGpdAt 0).(prefix)); E)} with
    | tt => fun _ => (pshFiller0;
        (tower1; (tower1RestrPaintings;
         (tower1RestrCohs; tower1RestrPaintingCohs))))
    end
  | l.+1 => fun X s => (mkPshFiller (towerPshDeps s.1);
      (towerStep s.1 s.2.1 s.2.2.1;
       (towerStepRestrPaintings s.1 s.2.1 s.2.2.1;
        (towerStepRestrCohs s.1 s.2.1 s.2.2.1 s.2.2.2;
         towerStepRestrPaintingCohs s.1 s.2.1 s.2.2.1 s.2.2.2))))
  end.

Fixpoint pshChain (l: nat): {X: (νGpdAt l).(prefix) &T PshState l X} :=
  match l with
  | 0 => (tt; tt)
  | l.+1 =>
    let s := pshChain l in
    let e := pshExtend l s.1 s.2 in
    ((s.1; e.1); e.2)
  end.

Definition pshApprox (l: nat): (νGpdAt l).(prefix) := (pshChain l).1.

Definition pshFrom (n: nat): νGpdFrom n (pshApprox n) :=
  ofChain (T := νGpdTel) pshApprox (fun _ => eq_refl) n.

Definition f: νGpds := pshFrom 0.

End Construction.

Lemma mkPshRestrPaintingMerged_comp (ps: νGpdPresentation arity)
  {m p k} (PC2: PshDepsCohs2 ps m p.+1 k)
  {XC: DepsCohsExtension p.+1 k (pshDepsCohs ps PC2.(_pshDepsCohs _))}
  (PCX: PshDepsCohsExtension ps m PC2 XC)
  (q: nat) (Hq: q <= k) (Hdim: q + p.+1 <= m.+1)
  (ε: arity) (d: ps.(G0) m.+2):
  eq_existT_curried_dep
    (P := fun a => (mkLayer
      PC2.(_pshDepsCohs _).(_pshDeps _).(_pdeps _).(_restrFrames).2 a).(GDom))
    (Q := fun a => (mkPainting PC2.(_pshDepsCohs _).(_pExtraDeps _) a).(GDom))
    (Hu := mkPshRestrLayerMerged ps PC2.(_pshDepsCohs _)
      (mkPshRestrFrames ps (proj1PshDepsCohs ps PC2.(_pshDepsCohs _))
        PC2.(_pshRestrCohs _).1)
      PC2.(_pshRestrCohs _).2 q Hq Hdim ε d)
    (Hv := mkPshRestrPainting ps PCX q Hq Hdim ε d) =
  f_equal_dep_sigT
    (Q := fun a => {u: (mkLayer
      PC2.(_pshDepsCohs _).(_pshDeps _).(_pdeps _).(_restrFrames).2 a).(GDom) &T
      (mkPainting PC2.(_pshDepsCohs _).(_pExtraDeps _) (a; u)).(GDom)})
    (fun a => (mkPshFrame ps PC2.(_pshDepsCohs _).(_pshDeps _) a).1)
    (fun a => ((mkPshFrame ps PC2.(_pshDepsCohs _).(_pshDeps _) a).2;
      mkPshPainting ps PC2.(_pshDepsCohs _).(_pshExtraDeps _) a))
    (pshFaceDimIrr ps (eq_sym (plus_n_Sm q p))
      (Hq := Hdim) (Hq' := leR_add_shift Hdim) ε d)
  ⊙ mkPshRestrPainting ps (AddPshCohDep ps m PC2 PCX) q.+1 (⇑ Hq)
    (leR_add_shift Hdim) ε d.
Proof.
  cbn [mkPshRestrPainting].
  now exact (section_pair_source_shift_dep
    (L := fun a => (mkLayer
      PC2.(_pshDepsCohs _).(_pshDeps _).(_pdeps _).(_restrFrames).2 a).(GDom))
    (C := fun a => (mkPainting PC2.(_pshDepsCohs _).(_pExtraDeps _) a).(GDom))
    (fun a => (mkPshFrame ps PC2.(_pshDepsCohs _).(_pshDeps _) a).1)
    (fun a => (mkPshFrame ps PC2.(_pshDepsCohs _).(_pshDeps _) a).2)
    (fun a => mkPshPainting ps PC2.(_pshDepsCohs _).(_pshExtraDeps _) a)
    (pshFaceDimIrr ps (plus_n_Sm q p)
      (Hq := leR_add_shift Hdim) (Hq' := Hdim) ε d)
    (pshFaceDimIrr ps (eq_sym (plus_n_Sm q p))
      (Hq := Hdim) (Hq' := leR_add_shift Hdim) ε d)
    (eq_sym (pshFaceDimIrr_sym ps (plus_n_Sm q p)
      (Hq := leR_add_shift Hdim) (Hq' := Hdim) ε d))
    ((mkPshRestrFrames ps (proj1PshDepsCohs ps PC2.(_pshDepsCohs _))
        PC2.(_pshRestrCohs _).1).2 q.+1 (⇑ Hq) (leR_add_shift Hdim) ε d)
    (mkPshRestrLayer ps PC2.(_pshDepsCohs _)
      (mkPshRestrFrames ps (proj1PshDepsCohs ps PC2.(_pshDepsCohs _))
        PC2.(_pshRestrCohs _).1)
      PC2.(_pshRestrCohs _).2 q Hq (leR_add_shift Hdim) ε d)
    (mkPshRestrLayerMerged ps PC2.(_pshDepsCohs _)
      (mkPshRestrFrames ps (proj1PshDepsCohs ps PC2.(_pshDepsCohs _))
        PC2.(_pshRestrCohs _).1)
      PC2.(_pshRestrCohs _).2 q Hq Hdim ε d)
    (mkPshRestrLayerMerged_comp ps PC2.(_pshDepsCohs _)
      (mkPshRestrFrames ps (proj1PshDepsCohs ps PC2.(_pshDepsCohs _))
        PC2.(_pshRestrCohs _).1)
      PC2.(_pshRestrCohs _).2 q Hq Hdim ε d)
    (mkPshRestrPainting ps PCX q Hq Hdim ε d)).
Defined.

End νGpdOfPresheaf.

Module νGpdOfPresheafSimplicial := νGpdOfPresheaf SimplicialGpdLayer.
Module νGpdOfPresheafCubical := νGpdOfPresheaf CubicalGpdLayer.
