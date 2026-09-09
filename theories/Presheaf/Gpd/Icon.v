(** An icon comparing a path diagram with the action generated
    by its faces.

    The pseudofunctor's compositors identify its action on a word with
    iterated face action. These identifications form the icon's components.
    Composition compatibility is proved by induction on the word's source
    object, following the cases of word composition.

    A [wkeep] shifts the face structure. Its faces agree with the shifted
    generating cofaces through [wgenLift], so the induction carries the
    object family, pseudofunctor axioms in pointwise form, faces and their
    comparison with generators, and the exchange law read off the compositors.
    These data and hypotheses are all preserved by shifting.

    Equalities of words remain parameters: the hom-types are h-sets, so
    parallel equalities agree regardless of how they are proved. *)

Set Warnings "-notation-overridden".
From Bonak.Lib Require Import RewLemmas.
From Bonak Require Import HSet Notation LeSProp.
From Bonak Require Import νGpd.HGpd.

From Bonak.Category Require Import Category.
From Bonak.Category.Bicategory Require Import Bicategory.
From Bonak.Presheaf Require Import νSemiShape WordAction.
From Bonak.Presheaf.Gpd Require Import Pseudofunctor.
From Stdlib Require Import Logic.FunctionalExtensionality.

From Bonak.Category.Bicategory Require Import PathDiagramPasting.

From Bonak.Category.Bicategory Require Import HGpd2Cat.
Set Primitive Projections.
Set Printing Projections.

Section GpdIcon.
Context (A: HSet).

(** Precomposition with the shift endofunctor of the ν-semi-shape category. Both
    the identity and the composition of two shifted words are the shifts of the
    identity and of the composite, on the nose, so no transport appears. *)

Definition npsfShift {ob: nat -> HGpd}
  (F: PathDiagramData (Op (νSemiShape A)) ob):
  PathDiagramData (Op (νSemiShape A)) (fun n => ob (S n)) :=
  Build_PathDiagramData (Op (νSemiShape A)) (fun n => ob (S n))
    (fun a b w => F.(phom) (a := S a) (b := S b) (wkeep w))
    (fun a => F.(pid) (S a))
    (fun a b c f g => F.(pcomp) (a := S a) (b := S b) (c := S c)
       (wkeep f) (wkeep g)).

(** The action of a word under the face structure read off a pseudofunctor,
    compared with the pseudofunctor's own action on that word. *)

Lemma applyWphom (m: nat): forall n (w: Word A n m) (ob: nat -> HGpd)
  (F: PathDiagramData (Op (νSemiShape A)) ob)
  (SF: forall k q (Hq: q <= k) (ε: A), ob (S k) -> ob k)
  (HSF: forall k q (Hq: q <= k) (ε: A) x,
     SF k q Hq ε x = F.(phom) (a := S k) (b := k) (wgen k q ε) x)
  (x: ob m),
  applyW m w (Build_FaceStr A ob SF) x = F.(phom) (a := m) (b := n) w x.
Proof.
  intros n w ob F SF HSF x.
  exact (applyWCompare m n w ob
    (fun p n w => F.(phom) (a := p) (b := n) w)
    (fun n x => f_equal (fun h => h x) (F.(pid) n))
    (fun p m n g f x => F.(pcomp) g f x) SF HSF x).
Defined.

(** The face structure and the pseudofunctor generated from one another *)

Definition ofPsfStr {ob: nat -> HGpd} (F: PathDiagramData (Op (νSemiShape A)) ob):
  FaceStr A :=
  Build_FaceStr A ob (fun k q (Hq: q <= k) (ε: A) =>
    F.(phom) (a := S k) (b := k) (wgen k q ε)).

Definition ofPsfStrCoh {ob: nat -> HGpd} (F: PathDiagramData (Op (νSemiShape A)) ob):
  CohOf (ofPsfStr F) := ofPsfCoh A ob F.

Lemma psfUnitLPtShift {ob: nat -> HGpd}
  {F: PathDiagramData (Op (νSemiShape A)) ob} (PL: PathDiagramUnitLPt F):
  PathDiagramUnitLPt (npsfShift F).
Proof.
  intros a b f E x.
  refine (PL (S a) (S b) (wkeep f) (f_equal wkeep E) x • _).
  now exact (transCongL _ (f_equal (@eq_sym _ _ _)
    (f_equal_compose (@wkeep A b a)
      (fun z: Word A (S b) (S a) => F.(phom) (a := S a) (b := S b) z x) E))).
Defined.

Lemma psfUnitRPtShift {ob: nat -> HGpd}
  {F: PathDiagramData (Op (νSemiShape A)) ob} (PR: PathDiagramUnitRPt F):
  PathDiagramUnitRPt (npsfShift F).
Proof.
  intros a b f E x.
  refine (PR (S a) (S b) (wkeep f) (f_equal wkeep E) x • _).
  now exact (transCongL _ (f_equal (@eq_sym _ _ _)
    (f_equal_compose (@wkeep A b a)
      (fun z: Word A (S b) (S a) => F.(phom) (a := S a) (b := S b) z x) E))).
Defined.

Lemma psfAssocPtShift {ob: nat -> HGpd}
  {F: PathDiagramData (Op (νSemiShape A)) ob} (PA: PathDiagramAssocPt F):
  PathDiagramAssocPt (npsfShift F).
Proof.
  intros a b c d u v w E x.
  refine (transCongL _ (transCongL _ (eq_sym (f_equal_compose (@wkeep A d a)
    (fun z: Word A (S d) (S a) => F.(phom) (a := S a) (b := S d) z x) E)))
    • _).
  now exact (PA (S a) (S b) (S c) (S d) (wkeep u) (wkeep v) (wkeep w)
    (f_equal wkeep E) x).
Defined.

(** The comparison cells of a face structure

    A face structure whose faces are compared with the action of the
    generating cofaces of a pseudofunctor carries two families of cells: one
    comparing the action of a word after a top face with the action of the
    word prefixed by that face, and one comparing the action of a shifted word
    followed by a top face with the same prefixed word. *)

Definition FaceCmp (ob: nat -> HGpd) (F: PathDiagramData (Op (νSemiShape A)) ob)
  (SF: GFaceType A ob): Type :=
  forall k q (Hq: q <= k) (ε: A) x,
    SF k q Hq ε x = F.(phom) (a := S k) (b := k) (wgen k q ε) x.

Definition shiftFace {ob: nat -> HGpd} (SF: GFaceType A ob):
  GFaceType A (fun k => ob (S k)) := fun k q Hq ε => SF (S k) q (↑ Hq) ε.

Definition shiftCmp {ob: nat -> HGpd} {F: PathDiagramData (Op (νSemiShape A)) ob}
  {SF: GFaceType A ob} (HSF: FaceCmp ob F SF):
  FaceCmp (fun k => ob (S k)) (npsfShift F) (shiftFace SF) :=
  fun k q Hq ε x => HSF (S k) q (↑ Hq) ε x • phomEq F (wgenLift Hq ε) x.

Definition topFace {ob: nat -> HGpd} (SF: GFaceType A ob) (k: nat) (ε: A):
  ob (S k) -> ob k := SF k k leR_refl ε.

Definition skipCell {ob: nat -> HGpd} (F: PathDiagramData (Op (νSemiShape A)) ob)
  {SF: GFaceType A ob} (HSF: FaceCmp ob F SF) {p n} (w: Word A n p) (ε: A)
  (x: ob (S p)):
  F.(phom) (a := p) (b := n) w (topFace SF p ε x)
  = F.(phom) (a := S p) (b := n) (wskip ε w) x :=
  f_equal (F.(phom) (a := p) (b := n) w) (HSF p p leR_refl ε x)
  • (F.(pcomp) (a := S p) (b := p) (c := n) (wgen p p ε) w x
     • phomEq F (wgenSkip ε w) x).

Definition topCell {ob: nat -> HGpd} (F: PathDiagramData (Op (νSemiShape A)) ob)
  {SF: GFaceType A ob} (HSF: FaceCmp ob F SF) {k l} (w: Word A l k) (ε: A)
  (y: ob (S k)):
  topFace SF l ε (F.(phom) (a := S k) (b := S l) (wkeep w) y)
  = F.(phom) (a := S k) (b := l) (wskip ε w) y :=
  HSF l l leR_refl ε (F.(phom) (a := S k) (b := S l) (wkeep w) y)
  • (F.(pcomp) (a := S k) (b := S l) (c := l) (wkeep w) (wgen l l ε) y
     • phomEq F (wskipKeep ε w) y).

Definition tauCell {ob: nat -> HGpd} (F: PathDiagramData (Op (νSemiShape A)) ob)
  {SF: GFaceType A ob} (HSF: FaceCmp ob F SF) {k l} (w: Word A l k) (ε: A)
  (y: ob (S k)):
  topFace SF l ε (F.(phom) (a := S k) (b := S l) (wkeep w) y)
  = F.(phom) (a := k) (b := l) w (topFace SF k ε y) :=
  topCell F HSF w ε y • eq_sym (skipCell F HSF w ε y).

(** [skipCell] is compatible with composition of words. *)

Lemma skipCellComp {ob: nat -> HGpd} (F: PathDiagramData (Op (νSemiShape A)) ob)
  (PA: PathDiagramAssocPt F)
  {SF: GFaceType A ob} (HSF: FaceCmp ob F SF)
  {p m n} (f: Word A m p) (g: Word A n m) (ε: A) (x: ob (S p)):
  f_equal (F.(phom) (a := m) (b := n) g) (skipCell F HSF f ε x)
  • F.(pcomp) (a := S p) (b := m) (c := n) (wskip ε f) g x
  = F.(pcomp) (a := p) (b := m) (c := n) f g (topFace SF p ε x)
    • skipCell F HSF (wcomp f g) ε x.
Proof.
  unfold skipCell.
  rewrite eq_trans_map_distr, eqTransAssoc.
  refine (transCongL _ (pcompPaste F PA (wgen p p ε) f g
    (wgenSkip ε f) eq_refl eq_refl (wgenSkip ε (wcomp f g)) x) • _).
  rewrite <- eqTransAssoc.
  refine (transCongR (pcompNatPt F f g (HSF p p leR_refl ε x)) _ • _).
  apply eqTransAssoc.
Defined.

(** [topCell] against composition of words, whiskered by a further word and
    by the top face. *)

Lemma topCellComp {ob: nat -> HGpd} (F: PathDiagramData (Op (νSemiShape A)) ob)
  (PA: PathDiagramAssocPt F)
  {SF: GFaceType A ob} (HSF: FaceCmp ob F SF)
  {k l n} (u: Word A l k) (v: Word A n l) (ε: A) (y: ob (S k)):
  f_equal (F.(phom) (a := l) (b := n) v) (topCell F HSF u ε y)
  • F.(pcomp) (a := S k) (b := l) (c := n) (wskip ε u) v y
  = skipCell F HSF v ε (F.(phom) (a := S k) (b := S l) (wkeep u) y)
    • F.(pcomp) (a := S k) (b := S l) (c := n) (wkeep u) (wskip ε v) y.
Proof.
  unfold topCell, skipCell.
  rewrite eq_trans_map_distr, eqTransAssoc.
  refine (transCongL _ (pcompPaste F PA (wkeep u) (wgen l l ε) v
    (wskipKeep ε u) (wgenSkip ε v) eq_refl eq_refl y) • _).
  apply eq_sym, eqTransAssoc.
Defined.

Lemma topCellCompose {ob: nat -> HGpd} (F: PathDiagramData (Op (νSemiShape A)) ob)
  (PA: PathDiagramAssocPt F)
  {SF: GFaceType A ob} (HSF: FaceCmp ob F SF)
  {k l n} (u: Word A l k) (v: Word A n l) (ε: A) (y: ob (S k)):
  f_equal (topFace SF n ε)
    (F.(pcomp) (a := S k) (b := S l) (c := S n) (wkeep u) (wkeep v) y)
  • topCell F HSF (wcomp u v) ε y
  = topCell F HSF v ε (F.(phom) (a := S k) (b := S l) (wkeep u) y)
    • F.(pcomp) (a := S k) (b := S l) (c := n) (wkeep u) (wskip ε v) y.
Proof.
  unfold topCell.
  rewrite <- eqTransAssoc, homotopyNat, eqTransAssoc.
  refine (transCongL _ (pcompPaste F PA (wkeep u) (wkeep v) (wgen n n ε)
    eq_refl (wskipKeep ε v) (wskipKeep ε (wcomp u v)) eq_refl y) • _).
  apply eq_sym, eqTransAssoc.
Defined.

(** [tauCell] at the identity word is the unit comparison. The unit axioms
    identify the compositors involving that word with transported identities. *)

Lemma tauIdCore {ob: nat -> HGpd} (F: PathDiagramData (Op (νSemiShape A)) ob)
  (PL: PathDiagramUnitLPt F) (PR: PathDiagramUnitRPt F) (k: nat) (ε: A) (x: ob (S k)):
  f_equal (F.(phom) (a := S k) (b := k) (wgen k k ε))
    (eq_sym (pidPt F (S k) x))
  • (F.(pcomp) (a := S k) (b := S k) (c := k) (wkeep (wid k)) (wgen k k ε) x
     • (phomEq F (wskipKeep ε (wid k)) x
        • eq_sym (phomEq F (wgenSkip ε (wid k)) x)))
  = eq_sym (pidPt F k (F.(phom) (a := S k) (b := k) (wgen k k ε) x))
    • F.(pcomp) (a := S k) (b := k) (c := k) (wgen k k ε) (wid k) x.
Proof.
  refine (transCongL _ (transCongR (PL _ _ (wgen k k ε)
    (wcompIdl (wgen k k ε)) x) _) • _).
  refine (_ • eq_sym (transCongL _ (PR _ _ (wgen k k ε)
    (wcompIdr (wgen k k ε)) x))).
  refine (transCongR (fEqualSym _ (pidPt F (S k) x)) _ • _).
  refine (transCongL _ (eqTransAssoc _ _ _) • _).
  refine (eq_trans_sym_cancel_l _ _ • _).
  refine (_ • eq_sym (eq_trans_sym_cancel_l _ _)).
  refine (transCongR (eq_sym (fEqualSym
    (fun w: Word A k (S k) => F.(phom) (a := S k) (b := k) w x)
    (wcompIdl (wgen k k ε)))) _ • _).
  refine (transCongL _ (transCongL _ (eq_sym (fEqualSym
    (fun w: Word A k (S k) => F.(phom) (a := S k) (b := k) w x)
    (wgenSkip ε (wid k))))) • _).
  refine (transCongL _ (eq_sym (eq_trans_map_distr
    (fun w: Word A k (S k) => F.(phom) (a := S k) (b := k) w x)
    (wskipKeep ε (wid k)) (eq_sym (wgenSkip ε (wid k))))) • _).
  refine (eq_sym (eq_trans_map_distr
    (fun w: Word A k (S k) => F.(phom) (a := S k) (b := k) w x)
    (eq_sym (wcompIdl (wgen k k ε)))
    (wskipKeep ε (wid k) • eq_sym (wgenSkip ε (wid k)))) • _).
  refine (f_equal (fun e: wgen k k ε = wcomp (wgen k k ε) (wid k) =>
            phomEq F e x) _ • _).
  - now exact (((Op (νSemiShape A)).(CHom) (S k) k).(UIP)).
  - now exact (fEqualSym _ (wcompIdr (wgen k k ε))).
Defined.

Lemma tauId {ob: nat -> HGpd} (F: PathDiagramData (Op (νSemiShape A)) ob)
  (PL: PathDiagramUnitLPt F) (PR: PathDiagramUnitRPt F)
  {SF: GFaceType A ob} (HSF: FaceCmp ob F SF) (k: nat) (ε: A) (x: ob (S k)):
  f_equal (topFace SF k ε) (eq_sym (pidPt F (S k) x))
  • tauCell F HSF (wid k) ε x
  = eq_sym (pidPt F k (topFace SF k ε x)).
Proof.
  unfold tauCell, topCell, skipCell.
  rewrite !eq_trans_sym_distr, !eqTransAssoc.
  refine (eq_sym (eqTransAssoc _ _ _) • _).
  refine (transCongR (homotopyNat _ _ (HSF k k leR_refl ε)
    (eq_sym (pidPt F (S k) x))) _ • _).
  refine (eqTransAssoc _ _ _ • _).
  refine (transCongL _ (transCongL _ (transCongL _
    (eq_sym (eqTransAssoc _ _ _)))) • _).
  refine (transCongL _ (transCongL _ (eq_sym (eqTransAssoc _ _ _))) • _).
  refine (transCongL _ (eq_sym (eqTransAssoc _ _ _)) • _).
  refine (transCongL _ (transCongR (tauIdCore F PL PR k ε x) _) • _).
  refine (transCongL _ (transCancelMid _ _ _) • _).
  refine (eq_sym (eqTransAssoc _ _ _) • _).
  refine (transCongR (transCongR (eq_sym (f_equal_id (HSF k k leR_refl ε x))) _
    • homotopyNat (fun z: ob k => z) (F.(phom) (a := k) (b := k) (wid k))
        (fun z => eq_sym (pidPt F k z)) (HSF k k leR_refl ε x)) _ • _).
  now exact (transSymCancelR _ _).
Defined.

(** [tauCell] is compatible with composition of words. *)

Lemma tauComp {ob: nat -> HGpd} (F: PathDiagramData (Op (νSemiShape A)) ob)
  (PA: PathDiagramAssocPt F)
  {SF: GFaceType A ob} (HSF: FaceCmp ob F SF)
  {k l n} (u: Word A l k) (v: Word A n l) (ε: A) (y: ob (S k)):
  f_equal (topFace SF n ε)
    (F.(pcomp) (a := S k) (b := S l) (c := S n) (wkeep u) (wkeep v) y)
  • tauCell F HSF (wcomp u v) ε y
  = tauCell F HSF v ε (F.(phom) (a := S k) (b := S l) (wkeep u) y)
    • (f_equal (F.(phom) (a := l) (b := n) v) (tauCell F HSF u ε y)
       • F.(pcomp) (a := k) (b := l) (c := n) u v (topFace SF k ε y)).
Proof.
  refine (transCancelR _ _ (skipCell F HSF (wcomp u v) ε y) _).
  refine (eqTransAssoc _ _ _ • _).
  refine (transCongL _ (transSymCancelR2 (topCell F HSF (wcomp u v) ε y)
    (skipCell F HSF (wcomp u v) ε y)) • _).
  refine (topCellCompose F PA HSF u v ε y • eq_sym _).
  refine (eqTransAssoc _ _ _ • _).
  refine (transCongL _ (eqTransAssoc _ _ _) • _).
  refine (transCongL _ (transCongL _
    (eq_sym (skipCellComp F PA HSF u v ε y))) • _).
  refine (transCongL _ (transCongR
    (eq_trans_map_distr (F.(phom) (a := l) (b := n) v) (topCell F HSF u ε y)
       (eq_sym (skipCell F HSF u ε y))
     • transCongL _ (fEqualSym (F.(phom) (a := l) (b := n) v)
         (skipCell F HSF u ε y))) _) • _).
  refine (transCongL _ (transCancelMid2 _ _ _) • _).
  refine (transCongL _ (topCellComp F PA HSF u v ε y) • _).
  unfold tauCell. now exact (transCancelMid2 _ _ _).
Defined.

(** The exchange law read off the pseudofunctor

    A face structure compared with the generating cofaces of a pseudofunctor
    inherits an exchange law, transported from the defining relation of the
    ν-semi-shape category by the compositors. *)

Definition faceCohOf {ob: nat -> HGpd} (F: PathDiagramData (Op (νSemiShape A)) ob)
  {SF: GFaceType A ob} (HSF: FaceCmp ob F SF): CohOf (Build_FaceStr A ob SF) :=
  fun n q Hq r Hr ε ω X =>
    HSF n q Hq ε (SF (S n) r (Hr ↕ (↑ Hq)) ω X)
    • (f_equal (F.(phom) (a := S n) (b := n) (wgen n q ε))
         (HSF (S n) r (Hr ↕ (↑ Hq)) ω X)
    • (F.(pcomp) (a := S (S n)) (b := S n) (c := n)
         (wgen (S n) r ω) (wgen n q ε) X
    • (phomEq F (wgenExchange n q Hq r Hr ε ω) X
    • (eq_sym (F.(pcomp) (a := S (S n)) (b := S n) (c := n)
                 (wgen (S n) (S q) ε) (wgen n r ω) X)
    • (eq_sym (f_equal (F.(phom) (a := S n) (b := n) (wgen n r ω))
                 (HSF (S n) (S q) (⇑ Hq) ε X))
    • eq_sym (HSF n r (Hr ↕ Hq) ω (SF (S n) (S q) (⇑ Hq) ε X))))))).

(** The instance of that exchange law at the top face is [tauCell] at a
    generating coface. *)

Lemma tauGen {ob: nat -> HGpd} (F: PathDiagramData (Op (νSemiShape A)) ob)
  {SF: GFaceType A ob} (HSF: FaceCmp ob F SF)
  (k q: nat) (Hq: q <= k) (ε b: A) (x: ob (S (S k))):
  topCoh (faceCohOf F HSF) k q Hq ε b x
  = f_equal (topFace SF k ε)
      (HSF (S k) q (↑ Hq) b x • phomEq F (wgenLift Hq b) x)
    • (tauCell F HSF (wgen k q b) ε x
       • eq_sym (HSF k q Hq b (topFace SF (S k) ε x))).
Proof.
  refine (eq_sym _).
  unfold tauCell, topCell, skipCell, topCoh, faceCohOf.
  rewrite !eq_trans_sym_distr, !eqTransAssoc.
  refine (eq_sym (eqTransAssoc _ _ _) • _).
  refine (transCongR (homotopyNat _ _ (HSF k k leR_refl ε)
    (HSF (S k) q (↑ Hq) b x • phomEq F (wgenLift Hq b) x)) _ • _).
  refine (eqTransAssoc _ _ _ • _).
  refine (transCongL _ (transCongR
    (eq_trans_map_distr (F.(phom) (a := S k) (b := k) (wgen k k ε))
       (HSF (S k) q (↑ Hq) b x) (phomEq F (wgenLift Hq b) x)) _) • _).
  refine (transCongL _ (eqTransAssoc _ _ _) • _).
  refine (transCongL _ (transCongL _ (eq_sym (eqTransAssoc _ _ _))) • _).
  refine (transCongL _ (transCongL _ (transCongR (pcompNatL F
    (wgenLift Hq b) (wgen k k ε)
    (f_equal (fun z: Word A (S k) (S (S k)) => wcomp z (wgen k k ε))
       (wgenLift Hq b)) x) _)) • _).
  refine (transCongL _ (transCongL _ (eqTransAssoc _ _ _)) • _).
  refine (transCongL _ (transCongL _ (transCongL _ _))).
  (* the three word equalities agree, the hom-types of the ν-semi-shape category being h-sets *)
  refine (eq_sym (eqTransAssoc _ _ _) • _).
  refine (eq_sym (eqTransAssoc _ _ _) • _).
  refine (transCongR _ _).
  refine (transCongL _ (eq_sym (fEqualSym
    (fun w: Word A k (S (S k)) => F.(phom) (a := S (S k)) (b := k) w x)
    (wgenSkip ε (wgen k q b)))) • _).
  refine (transCongR (eq_sym (eq_trans_map_distr
    (fun w: Word A k (S (S k)) => F.(phom) (a := S (S k)) (b := k) w x)
    (f_equal (fun z: Word A (S k) (S (S k)) => wcomp z (wgen k k ε))
       (wgenLift Hq b))
    (wskipKeep ε (wgen k q b)))) _ • _).
  refine (eq_sym (eq_trans_map_distr
    (fun w: Word A k (S (S k)) => F.(phom) (a := S (S k)) (b := k) w x)
    (f_equal (fun z: Word A (S k) (S (S k)) => wcomp z (wgen k k ε))
       (wgenLift Hq b) • wskipKeep ε (wgen k q b))
    (eq_sym (wgenSkip ε (wgen k q b)))) • _).
  refine (f_equal (fun e: wcomp (wgen (S k) q b) (wgen k k ε)
                         = wcomp (wgen (S k) (S k) ε) (wgen k q b) =>
            phomEq F e x) _).
  now exact (((Op (νSemiShape A)).(CHom) (S (S k)) k).(UIP)).
Defined.

(** The exchange law read off a pseudofunctor is stable under shifting. *)

Lemma faceCohOfShift {ob: nat -> HGpd} (F: PathDiagramData (Op (νSemiShape A)) ob)
  {SF: GFaceType A ob} (HSF: FaceCmp ob F SF)
  n q (Hq: q <= n) r (Hr: r <= q) (ε ω: A) (X: ob (S (S (S n)))):
  faceCohOf F HSF (S n) q (↑ Hq) r Hr ε ω X
  = faceCohOf (npsfShift F) (shiftCmp HSF) n q Hq r Hr ε ω X.
Proof.
  refine (eq_sym _).
  unfold faceCohOf at 1, shiftCmp.
  refine (eqTransAssoc _ _ _ • _).
  refine (transCongL _ (transCongL _ (eq_sym (eqTransAssoc _ _ _))) • _).
  refine (transCongL _ (eq_sym (eqTransAssoc _ _ _)) • _).
  refine (transCongL _ (transCongR (pcompCompareNat F
    (wgenLift (Hr ↕ (↑ Hq)) ω) (wgenLift Hq ε)
    (SF (S (S n)) r (↑ (Hr ↕ (↑ Hq))) ω) (HSF (S (S n)) r (↑ (Hr ↕ (↑ Hq))) ω)
    (f_equal (fun z: Word A (S (S n)) (S (S (S n))) =>
                wcomp z (wgen (S n) q ε)) (wgenLift (Hr ↕ (↑ Hq)) ω)
     • f_equal (fun z: Word A (S n) (S (S n)) =>
                  wcomp (wkeep (wgen (S n) r ω)) z) (wgenLift Hq ε))
    X) _) • _).
  refine (transCongL _ (eqTransAssoc _ _ _) • _).
  refine (transCongL _ (transCongL _ (eqTransAssoc _ _ _)) • _).
  refine (transCongL _ (transCongL _ (transCongL _ _))).
  refine (transCongL _ (transCongL _ (pcompCompareNatSym F
    (wgenLift (⇑ Hq) ε) (wgenLift (Hr ↕ Hq) ω)
    (SF (S (S n)) (S q) (⇑ (↑ Hq)) ε) (HSF (S (S n)) (S q) (⇑ (↑ Hq)) ε)
    (SF (S n) r (Hr ↕ (↑ Hq)) ω) (HSF (S n) r (Hr ↕ (↑ Hq)) ω)
    (f_equal (fun z: Word A (S (S n)) (S (S (S n))) =>
                wcomp z (wgen (S n) r ω)) (wgenLift (⇑ Hq) ε)
     • f_equal (fun z: Word A (S n) (S (S n)) =>
                  wcomp (wkeep (wgen (S n) (S q) ε)) z)
         (wgenLift (Hr ↕ Hq) ω))
    X)) • _).
  refine (transCongL _ (eq_sym (eqTransAssoc _ _ _)) • _).
  refine (eq_sym (eqTransAssoc _ _ _) • _).
  refine (transCongR _ _).
  (* the three word equalities agree, the hom-types of the ν-semi-shape category being h-sets *)
  refine (transCongL _ (transCongR (eq_sym (f_equal_compose (@wkeep A n (S (S n)))
    (fun z: Word A (S n) (S (S (S n))) =>
       F.(phom) (a := S (S (S n))) (b := S n) z X)
    (wgenExchange n q Hq r Hr ε ω))) _) • _).
  refine (transCongL _ (transCongL _ (eq_sym (fEqualSym
    (fun z: Word A (S n) (S (S (S n))) =>
       F.(phom) (a := S (S (S n))) (b := S n) z X) _))) • _).
  refine (transCongL _ (eq_sym (eq_trans_map_distr
    (fun z: Word A (S n) (S (S (S n))) =>
       F.(phom) (a := S (S (S n))) (b := S n) z X) _ _)) • _).
  refine (eq_sym (eq_trans_map_distr
    (fun z: Word A (S n) (S (S (S n))) =>
       F.(phom) (a := S (S (S n))) (b := S n) z X) _ _) • _).
  refine (f_equal (fun e: wcomp (wgen (S (S n)) r ω) (wgen (S n) q ε)
                         = wcomp (wgen (S (S n)) (S q) ε) (wgen (S n) r ω) =>
            phomEq F e X) _).
  now exact (((Op (νSemiShape A)).(CHom) (S (S (S n))) (S n)).(UIP)).
Defined.

(** The comparison of a word action with a top face

    The naturality statement below is proved for an abstract family [T] of top
    faces and an abstract comparison [tau], because a [wkeep] moves the word to
    the shifted structure while [T] stays where it is. The three hypotheses on
    [tau] are stable under that shift, which is what makes the induction go
    through. *)

Section TauPackage.

Definition TauFam (ob: nat -> HGpd) (F: PathDiagramData (Op (νSemiShape A)) ob)
  (T: forall k (ε: A), ob (S k) -> ob k): Type :=
  forall k l (w: Word A l k) (ε: A) (y: ob (S k)),
    T l ε (F.(phom) (a := S k) (b := S l) (wkeep w) y)
    = F.(phom) (a := k) (b := l) w (T k ε y).

(** Naturality in the word holds for any such family. *)

Lemma tauNatural {ob: nat -> HGpd} (F: PathDiagramData (Op (νSemiShape A)) ob)
  {T: forall k (ε: A), ob (S k) -> ob k} (tau: TauFam ob F T)
  {k l} {w w': Word A l k} (E: w = w') (ε: A) (y: ob (S k)):
  f_equal (T l ε) (phomEq (npsfShift F) E y) • tau k l w' ε y
  = tau k l w ε y • phomEq F E (T k ε y).
Proof. destruct E. now exact (eq_trans_refl_l _). Defined.

(** The exchange hypothesis, rearranged: it says exactly that the comparison
    at a generating coface is the exchange cell of the face structure. *)

Lemma tauGenPair {ob: nat -> HGpd} (F: PathDiagramData (Op (νSemiShape A)) ob)
  {SF: GFaceType A ob} (HSF: FaceCmp ob F SF)
  {T: forall k (ε: A), ob (S k) -> ob k}
  (HT: forall k q (Hq: q <= k) (ε ω: A) (X: ob (S (S k))),
     T k ε (SF (S k) q (↑ Hq) ω X) = SF k q Hq ω (T (S k) ε X))
  (tau: TauFam ob F T)
  (tauG: forall k q (Hq: q <= k) (ε b: A) (x: ob (S (S k))),
     HT k q Hq ε b x
     = f_equal (T k ε) (HSF (S k) q (↑ Hq) b x • phomEq F (wgenLift Hq b) x)
       • (tau (S k) k (wgen k q b) ε x
          • eq_sym (HSF k q Hq b (T (S k) ε x))))
  (p: nat) (b ε: A) (x: ob (S (S p))):
  f_equal (T p ε)
    (HSF (S p) p (↑ leR_refl) b x • phomEq F (wgenLift leR_refl b) x)
  • tau (S p) p (wgen p p b) ε x
  = HT p p leR_refl ε b x • HSF p p leR_refl b (T (S p) ε x).
Proof.
  refine (eq_sym (transCongR (tauG p p leR_refl ε b x) _
    • (eqTransAssoc _ _ _ • transCongL _ (transSymCancelR2 _ _)))).
Defined.

(** One [wskip] step of the comparison. *)

Lemma tauSkip {ob: nat -> HGpd} (F: PathDiagramData (Op (νSemiShape A)) ob)
  {SF: GFaceType A ob} (HSF: FaceCmp ob F SF)
  {T: forall k (ε: A), ob (S k) -> ob k}
  (HT: forall k q (Hq: q <= k) (ε ω: A) (X: ob (S (S k))),
     T k ε (SF (S k) q (↑ Hq) ω X) = SF k q Hq ω (T (S k) ε X))
  (tau: TauFam ob F T)
  (tauC: forall k l n (u: Word A l k) (v: Word A n l) (ε: A) (y: ob (S k)),
     f_equal (T n ε)
       (F.(pcomp) (a := S k) (b := S l) (c := S n) (wkeep u) (wkeep v) y)
     • tau k n (wcomp u v) ε y
     = tau l n v ε (F.(phom) (a := S k) (b := S l) (wkeep u) y)
       • (f_equal (F.(phom) (a := l) (b := n) v) (tau k l u ε y)
          • F.(pcomp) (a := k) (b := l) (c := n) u v (T k ε y)))
  (tauG: forall k q (Hq: q <= k) (ε b: A) (x: ob (S (S k))),
     HT k q Hq ε b x
     = f_equal (T k ε) (HSF (S k) q (↑ Hq) b x • phomEq F (wgenLift Hq b) x)
       • (tau (S k) k (wgen k q b) ε x
          • eq_sym (HSF k q Hq b (T (S k) ε x))))
  {p m} (w: Word A m p) (b ε: A) (x: ob (S (S p))):
  f_equal (T m ε) (skipCell (npsfShift F) (shiftCmp HSF) w b x)
  • tau (S p) m (wskip b w) ε x
  = tau p m w ε (SF (S p) p (↑ leR_refl) b x)
    • (f_equal (F.(phom) (a := p) (b := m) w) (HT p p leR_refl ε b x)
       • skipCell F HSF w b (T (S p) ε x)).
Proof.
  unfold skipCell at 1.
  refine (transCongR (eq_trans_map_distr (T m ε) _ _) _ • _).
  refine (transCongR (transCongL _ (eq_trans_map_distr (T m ε) _ _)) _ • _).
  refine (eqTransAssoc _ _ _ • _).
  refine (transCongL _ (eqTransAssoc _ _ _) • _).
  refine (transCongL _ (transCongL _ (tauNatural F tau (wgenSkip b w) ε x))
    • _).
  refine (transCongL _ (eq_sym (eqTransAssoc _ _ _)) • _).
  refine (transCongL _ (transCongR (tauC (S p) p m (wgen p p b) w ε x) _) • _).
  refine (transCongL _ (eqTransAssoc _ _ _) • _).
  refine (transCongL _ (transCongL _ (eqTransAssoc _ _ _)) • _).
  refine (transCongR (f_equal_compose (F.(phom) (a := S p) (b := S m) (wkeep w))
    (T m ε) (HSF (S p) p (↑ leR_refl) b x
             • phomEq F (wgenLift leR_refl b) x)) _ • _).
  refine (eq_sym (eqTransAssoc _ _ _) • _).
  refine (transCongR (homotopyNat _ _ (tau p m w ε)
    (HSF (S p) p (↑ leR_refl) b x • phomEq F (wgenLift leR_refl b) x)) _ • _).
  refine (eqTransAssoc _ _ _ • _).
  refine (transCongL _ (transCongR (eq_sym (f_equal_compose (T p ε)
    (F.(phom) (a := p) (b := m) w)
    (HSF (S p) p (↑ leR_refl) b x • phomEq F (wgenLift leR_refl b) x))) _)
    • _).
  unfold skipCell.
  refine (transCongL _ (eq_sym (eqTransAssoc _ _ _)) • _).
  refine (transCongL _ (transCongR
    (eq_sym (eq_trans_map_distr (F.(phom) (a := p) (b := m) w) _ _)
     • (f_equal (fun e: T p ε (SF (S p) p (↑ leR_refl) b x)
                        = F.(phom) (a := S p) (b := p) (wgen p p b)
                            (T (S p) ε x) =>
                   f_equal (F.(phom) (a := p) (b := m) w) e)
          (tauGenPair F HSF HT tau tauG p b ε x)
        • eq_trans_map_distr (F.(phom) (a := p) (b := m) w) _ _)) _) • _).
  now exact (transCongL _ (eqTransAssoc _ _ _)).
Defined.

End TauPackage.

(** The three hypotheses on [tau] are stable under shifting. The unit and the
    composition hypotheses are instances of themselves at [wkeep]-ed words;
    the exchange hypothesis needs the naturality of [tau] in the word, because
    the shifted comparison of faces carries one extra transport. *)

Lemma tauGShift {ob: nat -> HGpd} (F: PathDiagramData (Op (νSemiShape A)) ob)
  {SF: GFaceType A ob} (HSF: FaceCmp ob F SF)
  {T: forall k (ε: A), ob (S k) -> ob k}
  (HT: forall k q (Hq: q <= k) (ε ω: A) (X: ob (S (S k))),
     T k ε (SF (S k) q (↑ Hq) ω X) = SF k q Hq ω (T (S k) ε X))
  (tau: TauFam ob F T)
  (tauG: forall k q (Hq: q <= k) (ε b: A) (x: ob (S (S k))),
     HT k q Hq ε b x
     = f_equal (T k ε) (HSF (S k) q (↑ Hq) b x • phomEq F (wgenLift Hq b) x)
       • (tau (S k) k (wgen k q b) ε x
          • eq_sym (HSF k q Hq b (T (S k) ε x))))
  (k q: nat) (Hq: q <= k) (ε b: A) (x: ob (S (S (S k)))):
  HT (S k) q (↑ Hq) ε b x
  = f_equal (T (S k) ε)
      (shiftCmp HSF (S k) q (↑ Hq) b x
       • phomEq (npsfShift F) (wgenLift Hq b) x)
    • (tau (S (S k)) (S k) (wkeep (wgen k q b)) ε x
       • eq_sym (shiftCmp HSF k q Hq b (T (S (S k)) ε x))).
Proof.
  refine (tauG (S k) q (↑ Hq) ε b x • _).
  refine (_ • eq_sym (transCongR (eq_trans_map_distr (T (S k) ε) _ _) _)).
  refine (_ • eq_sym (eqTransAssoc _ _ _)).
  refine (transCongL _ _).
  refine (_ • eqTransAssoc _ _ _).
  refine (_ • eq_sym (transCongR (tauNatural F tau (wgenLift Hq b) ε x) _)).
  refine (_ • eq_sym (transCongL _ (eq_trans_sym_distr _ _))).
  now exact (eq_sym (transCancelMid _ _ _)).
Defined.

(** The action of a word commutes with a top face, compatibly with the
    comparison of the two pseudofunctors. *)

Lemma applyWphomNat (p: nat): forall m (w: Word A m p) (ob: nat -> HGpd)
  (F: PathDiagramData (Op (νSemiShape A)) ob)
  (SF: GFaceType A ob) (HSF: FaceCmp ob F SF)
  (T: forall k (ε: A), ob (S k) -> ob k)
  (HT: forall k q (Hq: q <= k) (ε ω: A) (X: ob (S (S k))),
     T k ε (SF (S k) q (↑ Hq) ω X) = SF k q Hq ω (T (S k) ε X))
  (tau: TauFam ob F T)
  (tauI: forall k (ε: A) (x: ob (S k)),
     f_equal (T k ε) (eq_sym (pidPt F (S k) x)) • tau k k (wid k) ε x
     = eq_sym (pidPt F k (T k ε x)))
  (tauC: forall k l n (u: Word A l k) (v: Word A n l) (ε: A) (y: ob (S k)),
     f_equal (T n ε)
       (F.(pcomp) (a := S k) (b := S l) (c := S n) (wkeep u) (wkeep v) y)
     • tau k n (wcomp u v) ε y
     = tau l n v ε (F.(phom) (a := S k) (b := S l) (wkeep u) y)
       • (f_equal (F.(phom) (a := l) (b := n) v) (tau k l u ε y)
          • F.(pcomp) (a := k) (b := l) (c := n) u v (T k ε y)))
  (tauG: forall k q (Hq: q <= k) (ε b: A) (x: ob (S (S k))),
     HT k q Hq ε b x
     = f_equal (T k ε) (HSF (S k) q (↑ Hq) b x • phomEq F (wgenLift Hq b) x)
       • (tau (S k) k (wgen k q b) ε x
          • eq_sym (HSF k q Hq b (T (S k) ε x))))
  (ε: A) (x: ob (S p)),
  applyWNat p m w (Build_FaceStr A ob SF) T HT ε x
  • (f_equal (T m ε) (applyWphom p m w (fun k => ob (S k)) (npsfShift F)
       (shiftFace SF) (shiftCmp HSF) x)
     • tau p m w ε x)
  = applyWphom p m w ob F SF HSF (T p ε x).
Proof.
  induction p as [|p IHp]; intros m w ob F SF HSF T HT tau tauI tauC tauG ε x.
  - destruct m as [|m]; [|now destruct w].
    destruct w.
    now exact (eq_trans_refl_l _ • tauI 0 ε x).
  - destruct w as [(b, w)|w].
    + refine (transCongL _ (transCongR (eq_trans_map_distr (T m ε) _ _) _) • _).
      refine (transCongL _ (eqTransAssoc _ _ _) • _).
      refine (transCongL _ (transCongL _
        (tauSkip F HSF HT tau tauC tauG w b ε x)) • _).
      refine (transCongL _ (eq_sym (eqTransAssoc _ _ _)) • _).
      refine (eq_sym (eqTransAssoc _ _ _) • _).
      refine (transCongR (eqTransAssoc _ _ _) _ • _).
      refine (transCongR (transCongL _ (IHp m w ob F SF HSF T HT tau tauI
        tauC tauG ε (SF (S p) p (↑ leR_refl) b x))) _ • _).
      refine (transCongR (homotopyNat _ _ (applyWphom p m w ob F SF HSF)
        (eq_sym (HT p p leR_refl ε b x))) _ • _).
      refine (eqTransAssoc _ _ _ • _).
      refine (transCongL _ (transCongR (fEqualSym
        (F.(phom) (a := p) (b := m) w) (HT p p leR_refl ε b x)) _) • _).
      now exact (transCongL _ (eq_trans_sym_cancel_l _ _)).
    + destruct m as [|m]; [now destruct w|].
      now exact (IHp m w (fun k => ob (S k)) (npsfShift F) (shiftFace SF)
        (shiftCmp HSF) (fun k => T (S k))
        (fun k q Hq ε ω X => HT (S k) q (↑ Hq) ε ω X)
        (fun k l v ε y => tau (S k) (S l) (wkeep v) ε y)
        (fun k ε z => tauI (S k) ε z)
        (fun k l n u v ε y => tauC (S k) (S l) (S n) (wkeep u) (wkeep v) ε y)
        (tauGShift F HSF HT tau tauG) ε x).
Defined.

(** Composition compatibility of the comparison cells

    [iconComp] carries the object family, pseudofunctor axioms, faces and
    exchange comparison so that the [wkeep] case can use their shifted forms. *)

Lemma iconKeepSkip {ob: nat -> HGpd} (F: PathDiagramData (Op (νSemiShape A)) ob)
  (PA: PathDiagramAssocPt F) {SF: GFaceType A ob} (HSF: FaceCmp ob F SF)
  {k l n} (u: Word A l k) (v: Word A n l) (ω: A) (y: ob (S k)):
  f_equal (F.(phom) (a := l) (b := n) v) (tauCell F HSF u ω y)
  • (F.(pcomp) (a := k) (b := l) (c := n) u v (topFace SF k ω y)
     • skipCell F HSF (wcomp u v) ω y)
  = skipCell F HSF v ω (F.(phom) (a := S k) (b := S l) (wkeep u) y)
    • F.(pcomp) (a := S k) (b := S l) (c := n) (wkeep u) (wskip ω v) y.
Proof.
  unfold tauCell.
  refine (transCongR (eq_trans_map_distr (F.(phom) (a := l) (b := n) v) _ _
    • transCongL _ (fEqualSym (F.(phom) (a := l) (b := n) v)
        (skipCell F HSF u ω y))) _ • _).
  refine (transCongL _ (eq_sym (skipCellComp F PA HSF u v ω y)) • _).
  refine (transCancelMid2 _ _ _ • _).
  now exact (topCellComp F PA HSF u v ω y).
Defined.

Lemma iconComp (p: nat): forall m n (f: Word A m p) (g: Word A n m)
  (ob: nat -> HGpd) (F: PathDiagramData (Op (νSemiShape A)) ob)
  (PL: PathDiagramUnitLPt F) (PR: PathDiagramUnitRPt F) (PA: PathDiagramAssocPt F)
  (SF: GFaceType A ob) (HSF: FaceCmp ob F SF)
  (HQ: CohOf (Build_FaceStr A ob SF))
  (Hcomp: forall j q (Hq: q <= j) r (Hr: r <= q) (ε ω: A) X,
     HQ j q Hq r Hr ε ω X = faceCohOf F HSF j q Hq r Hr ε ω X)
  (x: ob p),
  f_equal (applyW m g (Build_FaceStr A ob SF))
    (applyWphom p m f ob F SF HSF x)
  • (applyWphom m n g ob F SF HSF (F.(phom) (a := p) (b := m) f x)
     • F.(pcomp) (a := p) (b := m) (c := n) f g x)
  = applyWComp p m n f g (Build_FaceStr A ob SF) HQ x
    • applyWphom p n (wcomp f g) ob F SF HSF x.
Proof.
  induction p as [|p IHp];
    intros m n f g ob F PL PR PA SF HSF HQ Hcomp x.
  - destruct m as [|m]; [|now destruct f].
    destruct n as [|n]; [|now destruct g].
    destruct f, g.
    refine (transCongR (f_equal_id _) _ • _).
    refine (transCongL _ (transCongL _
      (PR 0 0 (wid 0) (wcompIdr (wid 0)) x)) • _).
    refine (transCongL _ (eq_trans_sym_cancel_l _ _) • _).
    refine (transCongL _ (f_equal (@eq_sym _ _ _)
      (f_equal (fun e: wcomp (wid 0) (wid 0) = wid 0 => phomEq F e x)
         (((Op (νSemiShape A)).(CHom) 0 0).(UIP)
            (h := wcompIdr (wid 0)) (g := eq_refl)))) • _).
    now exact (eq_sym (eq_trans_refl_l _)).
  - destruct f as [(ε, f)|f].
    + (* a deleted top dimension in the first word *)
      refine (transCongR (eq_trans_map_distr (applyW m g (Build_FaceStr A ob SF))
        (applyWphom p m f ob F SF HSF (topFace SF p ε x))
        (skipCell F HSF f ε x)) _ • _).
      refine (eqTransAssoc _ _ _ • _).
      refine (transCongL _ (eq_sym (eqTransAssoc _ _ _)) • _).
      refine (transCongL _ (transCongR (homotopyNat _ _
        (applyWphom m n g ob F SF HSF) (skipCell F HSF f ε x)) _) • _).
      refine (transCongL _ (eqTransAssoc _ _ _) • _).
      refine (transCongL _ (transCongL _ (skipCellComp F PA HSF f g ε x)) • _).
      refine (transCongL _ (eq_sym (eqTransAssoc _ _ _)) • _).
      refine (eq_sym (eqTransAssoc _ _ _) • _).
      refine (transCongR (IHp m n f g ob F PL PR PA SF HSF HQ Hcomp
        (topFace SF p ε x)) _ • _).
      now exact (eqTransAssoc _ _ _).
    + destruct m as [|m]; [now destruct f|].
      destruct g as [(ω, g)|g].
      * (* a kept top dimension, then a deleted one *)
        refine (transCancelL (f_equal (applyW m g (Build_FaceStr A ob SF))
          (applyWNat p m f (Build_FaceStr A ob SF)
             (sTop (Build_FaceStr A ob SF)) (topCoh HQ) ω x)) _ _ _).
        refine (_ • eq_sym (transCongL _
          (transCongR (transCongR
             (fEqualSym (applyW m g (Build_FaceStr A ob SF))
                (applyWNat p m f (Build_FaceStr A ob SF)
                   (sTop (Build_FaceStr A ob SF)) (topCoh HQ) ω x)) _) _
           • eqTransAssoc _ _ _)
          • transSymCancelL _ _)).
        refine (transCongL _ (transCongR (eq_sym (f_equal_compose
          (topFace SF m ω) (applyW m g (Build_FaceStr A ob SF))
          (applyWphom p m f (fun k => ob (S k)) (npsfShift F)
             (shiftFace SF) (shiftCmp HSF) x))) _) • _).
        refine (transCongL _ (transCongL _ (eqTransAssoc _ _ _)) • _).
        refine (transCongL _ (transCongL _ (transCongL _
          (eq_sym (iconKeepSkip F PA HSF f g ω x)))) • _).
        refine (transCongL _ (transCongL _ (eq_sym (eqTransAssoc _ _ _)))
          • _).
        refine (transCongL _ (transCongL _ (transCongR (eq_sym (homotopyNat
          _ _ (applyWphom m n g ob F SF HSF) (tauCell F HSF f ω x))) _)) • _).
        refine (transCongL _ (transCongL _ (eqTransAssoc _ _ _)) • _).
        refine (transCongL _ (eq_sym (eqTransAssoc _ _ _)) • _).
        refine (transCongL _ (transCongR (eq_sym (eq_trans_map_distr
          (applyW m g (Build_FaceStr A ob SF)) _ _)) _) • _).
        refine (eq_sym (eqTransAssoc _ _ _) • _).
        refine (transCongR (eq_sym (eq_trans_map_distr
          (applyW m g (Build_FaceStr A ob SF)) _ _)) _ • _).
        refine (transCongR (f_equal (fun e: applyW p f (Build_FaceStr A ob SF)
                                              (topFace SF p ω x)
                                            = F.(phom) (a := p) (b := m) f
                                                (topFace SF p ω x) =>
          f_equal (applyW m g (Build_FaceStr A ob SF)) e)
          (applyWphomNat p m f ob F SF HSF (topFace SF) (topCoh HQ)
             (fun j i w ε z => tauCell F HSF (k := j) (l := i) w ε z)
             (fun k ε z => tauId F PL PR HSF k ε z)
             (fun k l j u v ε z => tauComp F PA HSF u v ε z)
             (fun k q Hq ε b z =>
                Hcomp k k leR_refl q Hq ε b z • tauGen F HSF k q Hq ε b z)
             ω x)) _ • _).
        refine (transCongL _ (eq_sym (eqTransAssoc _ _ _)) • _).
        refine (eq_sym (eqTransAssoc _ _ _) • _).
        refine (transCongR (IHp m n f g ob F PL PR PA SF HSF HQ Hcomp
          (topFace SF p ω x)) _ • _).
        now exact (eqTransAssoc _ _ _).
      * (* two kept top dimensions *)
        destruct n as [|n]; [now destruct g|].
        now exact (IHp m n f g (fun k => ob (S k)) (npsfShift F)
          (psfUnitLPtShift PL) (psfUnitRPtShift PR) (psfAssocPtShift PA)
          (shiftFace SF) (shiftCmp HSF) (cohShift HQ)
          (fun j q Hq r Hr ε ω X =>
             Hcomp (S j) q (↑ Hq) r Hr ε ω X
             • faceCohOfShift F HSF j q Hq r Hr ε ω X) x).
Defined.

(** The comparison at the identity word is the identity law of the action. *)

Lemma applyWphomId (a: nat): forall (ob: nat -> HGpd)
  (F: PathDiagramData (Op (νSemiShape A)) ob) (SF: GFaceType A ob)
  (HSF: FaceCmp ob F SF) (x: ob a),
  applyWphom a a (wid a) ob F SF HSF x • pidPt F a x
  = applyW_id (Build_FaceStr A ob SF) x.
Proof.
  induction a as [|a IHa]; intros ob F SF HSF x.
  - now exact (eq_trans_sym_inv_l _).
  - now exact (IHa (fun k => ob (S k)) (npsfShift F) (shiftFace SF)
      (shiftCmp HSF) x).
Defined.

(** The icon

    Its components are the comparison of the two actions on a word; the
    composition axiom is the induction above, and the unit axiom the
    identity law. *)

Definition genIcon {ob: nat -> HGpd} (F: PathDiagram (Op (νSemiShape A)) ob)
  (SF: GFaceType A ob) (HSF: FaceCmp ob (pathData (Op (νSemiShape A)) ob F) SF)
  (HQ: CohOf (Build_FaceStr A ob SF))
  (Hcomp: forall j q (Hq: q <= j) r (Hr: r <= q) (ε ω: A) X,
     HQ j q Hq r Hr ε ω X
     = faceCohOf (pathData (Op (νSemiShape A)) ob F) HSF j q Hq r Hr ε ω X):
  Icon (toPsfStr A SF HQ) (pathData (Op (νSemiShape A)) ob F).
Proof.
  pose (S := pathData (Op (νSemiShape A)) ob F).
  unshelve refine (Build_Icon _ _ _ _ _ _ _).
  - now exact (fun a b w x => applyWphom a b w ob S SF HSF x).
  - intros a b c f g.
    apply functional_extensionality_dep; intro x.
    now exact (eqTransAssoc _ _ _
      • iconComp a b c f g ob S
          (pcompUnitLPt S (pathUnitL _ _ F))
          (pcompUnitRPt S (pathUnitR _ _ F))
          (pcompAssocPt S (pathAssoc _ _ F))
          SF HSF HQ Hcomp x).
  - intros a.
    apply functional_extensionality_dep; intro x.
    refine (hom2RewPt _ _ _ x • _).
    refine (transCongR (f_equal (@eq_sym _ _ _)
      (f_equal__functional_extensionality_dep_good
         (fun z => applyW_id (Build_FaceStr A ob SF) z) x)) _ • _).
    refine (transCongL _ (applyWphomId a ob S SF HSF x) • _).
    now exact (eq_trans_sym_inv_l _).
Defined.

(** The face structure read off a pseudofunctor satisfies the hypothesis on
    the nose, so the specialisation needs no further data. *)

Lemma psfIconCoh {ob: nat -> HGpd} (F: PathDiagramData (Op (νSemiShape A)) ob)
  j q (Hq: q <= j) r (Hr: r <= q) (ε ω: A) X:
  ofPsfStrCoh F j q Hq r Hr ε ω X
  = faceCohOf F (fun k i (Hi: i <= k) (b: A) z => eq_refl) j q Hq r Hr ε ω X.
Proof. now exact (eq_sym (eq_trans_refl_l _ • eq_trans_refl_l _)). Defined.

Definition psfIcon {ob: nat -> HGpd} (F: PathDiagram (Op (νSemiShape A)) ob):
  Icon (toPsfStr A (fun k q (Hq: q <= k) (ε: A) =>
          (pathData (Op (νSemiShape A)) ob F).(phom) (a := S k) (b := k)
            (wgen k q ε))
          (ofPsfStrCoh (pathData (Op (νSemiShape A)) ob F)))
       (pathData (Op (νSemiShape A)) ob F) :=
  genIcon F _ (fun k q (Hq: q <= k) (ε: A) z => eq_refl)
    (ofPsfStrCoh (pathData (Op (νSemiShape A)) ob F))
    (psfIconCoh (pathData (Op (νSemiShape A)) ob F)).

End GpdIcon.
