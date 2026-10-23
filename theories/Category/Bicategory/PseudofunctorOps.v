Set Warnings "-notation-overridden".
From Bonak.Lib Require Import HSet Notation RewLemmas.
From Bonak.Category Require Import UnivalenceFacts.
From Bonak.Category.Bicategory Require Export BicategoryEq Pseudofunctor.
Set Primitive Projections.
Set Universe Polymorphism.

Set Printing Projections.

(** Preservation paths for a bicategory structure map give the comparison
    cells of a pseudofunctor. *)
Local Lemma idTo2Invertible {B: Bicategory} {a b} {f g: Hom B a b}
  (p: f = g): IsInvertible (idTo2 p).
Proof. destruct p. now exact (idToIso eq_refl).(isoInvertible). Defined.

Local Lemma hom2RewInverseSquare {B: Bicategory} {a b}
  {f f' g g': Hom B a b} (p: f = f') (q: g = g')
  (α: Hom2 f g) (β: Hom2 f' g')
  (e: α = hom2Rew (eq_sym p) (eq_sym q) β):
  β ⨟₂ idTo2 (eq_sym q) = idTo2 (eq_sym p) ⨟₂ α.
Proof.
  destruct p, q. change (α = β) in e. subst β.
  unfold comp2, idTo2, hom2Rew, id2. now rewrite cidl, cidr.
Defined.

Local Lemma hom2RewUnit {B: Bicategory} {a b}
  {f g h i: Hom B a b} (p: f = g) (q: g = h)
  (α: Hom2 f i) (β: Hom2 h i)
  (e: α = hom2Rew (eq_sym (p • q)) eq_refl β):
  idTo2 (eq_sym p) ⨟₂ α = idTo2 q ⨟₂ β.
Proof. destruct p, q. change (α = β) in e. now subst β. Defined.

Local Lemma hom2RewAssoc {B: Bicategory} {a b}
  {f f' f'' g g' g'': Hom B a b}
  (p: f = f') (q: f' = f'') (r: g = g') (s: g' = g'')
  (α: Hom2 f g) (β: Hom2 f'' g'')
  (e: α = hom2Rew (eq_sym (p • q)) (eq_sym (r • s)) β):
  (idTo2 (eq_sym q) ⨟₂ idTo2 (eq_sym p)) ⨟₂ α
    = β ⨟₂ (idTo2 (eq_sym s) ⨟₂ idTo2 (eq_sym r)).
Proof.
  destruct p, q, r, s. change (α = β) in e. subst β.
  unfold comp2, idTo2, hom2Rew, id2. now rewrite 3 cidl, cidr.
Defined.

Definition structureMapData {S T: Bicategory} (F: BicategoryStructureMap S T):
  PsfData S T F.(f2obj) :=
  Build_PsfData S T F.(f2obj)
    (fun a b f => F.(f2hom) f)
    (fun a b f g α => F.(f2hom2) α)
    (fun a => idTo2 (F.(f2id1) a))
    (fun a b c f g => idTo2 (eq_sym (F.(f2comp1) f g))).

Local Definition structureMapLaws {S T: Bicategory} (F: BicategoryStructureMap S T):
  PsfLaws (structureMapData F).
Proof.
  constructor.
  - intro a. now apply idTo2Invertible.
  - intros a b c f g. now apply idTo2Invertible.
  - intros a b f. now apply F.(f2id2).
  - intros a b f g h α β. now apply F.(f2comp2).
  - intros a b c f g h α.
    now apply hom2RewInverseSquare, F.(f2whiskerL).
  - intros a b c f g α h.
    now apply hom2RewInverseSquare, F.(f2whiskerR).
  - intros a b f. cbn [structureMapData psHom psCell psUnit psComp].
    change (idTo2 (eq_sym (F.(f2comp1) (id1 a) f)) ⨟₂ F.(f2hom2) (bunitL f).(isoHom)
      = (idTo2 (F.(f2id1) a) ▷ F.(f2hom) f) ⨟₂ (bunitL (F.(f2hom) f)).(isoHom)).
    rewrite idTo2WhiskerR.
    now apply hom2RewUnit, F.(f2unitL).
  - intros a b f. cbn [structureMapData psHom psCell psUnit psComp].
    change (idTo2 (eq_sym (F.(f2comp1) f (id1 b))) ⨟₂ F.(f2hom2) (bunitR f).(isoHom)
      = (F.(f2hom) f ◁ idTo2 (F.(f2id1) b)) ⨟₂ (bunitR (F.(f2hom) f)).(isoHom)).
    rewrite idTo2WhiskerL.
    now apply hom2RewUnit, F.(f2unitR).
  - intros a b c d f g h. cbn [structureMapData psHom psCell psComp].
    change ((idTo2 (eq_sym (F.(f2comp1) f g)) ▷ F.(f2hom) h
        ⨟₂ idTo2 (eq_sym (F.(f2comp1) (f ⨟₁ g) h)))
        ⨟₂ F.(f2hom2) (bassoc f g h).(isoHom)
      = (bassoc (F.(f2hom) f) (F.(f2hom) g) (F.(f2hom) h)).(isoHom)
        ⨟₂ (F.(f2hom) f ◁ idTo2 (eq_sym (F.(f2comp1) g h))
          ⨟₂ idTo2 (eq_sym (F.(f2comp1) f (g ⨟₁ h))))).
    rewrite idTo2WhiskerR, idTo2WhiskerL, 2 fEqualSym.
    now apply hom2RewAssoc, F.(f2assoc).
Defined.

Definition structureMapPseudofunctor {S T: Bicategory}
  (F: BicategoryStructureMap S T): Pseudofunctor S T :=
  Build_Pseudofunctor S T F.(f2obj)
    (Build_Psf S T F.(f2obj) (structureMapData F) (structureMapLaws F)).

Set Universe Minimization ToSet.
Unset Keyed Unification.

(** Composition of pseudofunctors. *)
Local Definition psHomFunctor {S T: Bicategory} (F: Pseudofunctor S T) (a b: S.(BObj)):
  Functor (S.(BHom) a b) (T.(BHom) (F.(psObj) a) (F.(psObj) b)) :=
  @Build_Functor _ _ (fun f => (psfData F).(psHom) f)
    (fun f g α => (psfData F).(psCell) α)
    (fun f => (psCellId _ F.(psStr).(psLaws)) a b f)
    (fun f g h α β => (psCellComp _ F.(psStr).(psLaws)) a b f g h α β).

Definition composePsfData {S T U: Bicategory} (F: Pseudofunctor S T) (G: Pseudofunctor T U):
  PsfData S U (fun a => G.(psObj) (F.(psObj) a)) :=
  @Build_PsfData S U (fun a => G.(psObj) (F.(psObj) a))
    (fun a b f => (psfData G).(psHom) ((psfData F).(psHom) f))
    (fun a b f g α => (psfData G).(psCell) ((psfData F).(psCell) α))
    (fun a => (psfData G).(psCell) ((psfData F).(psUnit) a)
      ⨟ (psfData G).(psUnit) (F.(psObj) a))
    (fun a b c f g => (psfData G).(psComp) ((psfData F).(psHom) f) ((psfData F).(psHom) g)
      ⨟ (psfData G).(psCell) ((psfData F).(psComp) f g)).

Local Definition composePsfLaws {S T U: Bicategory} (F: Pseudofunctor S T) (G: Pseudofunctor T U):
  PsfLaws (composePsfData F G).
Proof.
  refine (@Build_PsfLaws S U (fun a => G.(psObj) (F.(psObj) a)) (composePsfData F G)
    _ _ _ _ _ _ _ _ _).
  - intro a. apply composeInvertible.
    + now exact (functorIso (psHomFunctor G (F.(psObj) a) (F.(psObj) a))
        (@Build_Iso _ _ _ ((psfData F).(psUnit) a) ((psUnitInvertible _ F.(psStr).(psLaws)) a))).(isoInvertible).
    + now exact ((psUnitInvertible _ G.(psStr).(psLaws)) (F.(psObj) a)).
  - intros a b c f g. apply composeInvertible.
    + now exact ((psCompInvertible _ G.(psStr).(psLaws)) _ _ _
        ((psfData F).(psHom) f) ((psfData F).(psHom) g)).
    + now exact (functorIso (psHomFunctor G (F.(psObj) a) (F.(psObj) c))
        (@Build_Iso _ _ _ ((psfData F).(psComp) f g)
          ((psCompInvertible _ F.(psStr).(psLaws)) a b c f g))).(isoInvertible).
  - intros a b f. unfold composePsfData; cbn; unfold psfData.
    now rewrite (psCellId _ F.(psStr).(psLaws)), (psCellId _ G.(psStr).(psLaws)).
  - intros a b f g h α β. unfold composePsfData; cbn; unfold psfData.
    now rewrite (psCellComp _ F.(psStr).(psLaws)), (psCellComp _ G.(psStr).(psLaws)).
  - intros a b c f g h α. unfold composePsfData; cbn; unfold psfData.
    rewrite <- cassoc, (psCompNatL _ G.(psStr).(psLaws)), cassoc.
    rewrite <- (psCellComp _ G.(psStr).(psLaws)), (psCompNatL _ F.(psStr).(psLaws)).
    now rewrite (psCellComp _ G.(psStr).(psLaws)), <- cassoc.
  - intros a b c f g α h. unfold composePsfData; cbn; unfold psfData.
    rewrite <- cassoc, (psCompNatR _ G.(psStr).(psLaws)), cassoc.
    rewrite <- (psCellComp _ G.(psStr).(psLaws)), (psCompNatR _ F.(psStr).(psLaws)).
    now rewrite (psCellComp _ G.(psStr).(psLaws)), <- cassoc.
  - intros a b f. unfold composePsfData; cbn; unfold psfData.
    rewrite cassoc, <- (psCellComp _ G.(psStr).(psLaws)), (psUnitL _ F.(psStr).(psLaws)).
    rewrite (psCellComp _ G.(psStr).(psLaws)), <- cassoc, <- (psCompNatR _ G.(psStr).(psLaws)).
    now rewrite cassoc, (psUnitL _ G.(psStr).(psLaws)), <- cassoc, <- U.(bwhiskerRComp).
  - intros a b f. unfold composePsfData; cbn; unfold psfData.
    rewrite cassoc, <- (psCellComp _ G.(psStr).(psLaws)), (psUnitR _ F.(psStr).(psLaws)).
    rewrite (psCellComp _ G.(psStr).(psLaws)), <- cassoc, <- (psCompNatL _ G.(psStr).(psLaws)).
    now rewrite cassoc, (psUnitR _ G.(psStr).(psLaws)), <- cassoc, <- U.(bwhiskerLComp).
  - intros a b c d f g h. unfold composePsfData; cbn; unfold psfData.
    pose proof (psCompPaste (psfData G) (psCellComp _ G.(psStr).(psLaws))
      (psCompNatL _ G.(psStr).(psLaws)) (psCompNatR _ G.(psStr).(psLaws))
      (psAssoc _ G.(psStr).(psLaws))
      ((psfData F).(psHom) f) ((psfData F).(psHom) g) ((psfData F).(psHom) h)
      ((psfData F).(psComp) f g) ((psfData F).(psComp) g h)
      ((psfData F).(psComp) (bcomp f g) h ⨟ (psfData F).(psCell) (bassoc f g h).(isoHom))
      ((psfData F).(psComp) f (bcomp g h))
      (eq_sym ((T.(BHom) (F.(psObj) a) (F.(psObj) d)).(cassoc) (bwhiskerR ((psfData F).(psComp) f g) ((psfData F).(psHom) h))
        ((psfData F).(psComp) (bcomp f g) h) ((psfData F).(psCell) (bassoc f g h).(isoHom)))
        • (psAssoc _ F.(psStr).(psLaws)) a b c d f g h)) as q.
    unfold psCompareComp in q.
    rewrite (psCellComp _ G.(psStr).(psLaws)) in q.
    rewrite 2 cassoc. now exact q.
Defined.

Definition composePseudofunctor {S T U: Bicategory} (F: Pseudofunctor S T) (G: Pseudofunctor T U):
  Pseudofunctor S U :=
  @Build_Pseudofunctor S U (fun a => G.(psObj) (F.(psObj) a))
    (@Build_Psf S U (fun a => G.(psObj) (F.(psObj) a)) (composePsfData F G) (composePsfLaws F G)).

Unset Universe Minimization ToSet.
