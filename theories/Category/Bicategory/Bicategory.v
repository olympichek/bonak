(** Bicategories with h-set 2-cell types. Associators and unitors are
    specified isomorphisms in the hom-categories; other 2-cells need not
    be invertible. Composition and whiskering use diagrammatic order. *)

Set Warnings "-notation-overridden".
From Bonak.Category Require Export Category.
From Bonak.Lib Require Import HSet SigT Contractible Notation.
Set Primitive Projections.
Set Printing Projections.

Record Bicategory := {
  BObj: Type;
  BHom: BObj -> BObj -> Category;
  bid a: (BHom a a).(CObj);
  bcomp {a b c} (f: (BHom a b).(CObj)) (g: (BHom b c).(CObj)):
    (BHom a c).(CObj);
  bwhiskerL {a b c} (f: (BHom a b).(CObj)) {g h: (BHom b c).(CObj)}
    (α: (BHom b c).(CHom) g h): (BHom a c).(CHom) (bcomp f g) (bcomp f h);
  bwhiskerR {a b c} {f g: (BHom a b).(CObj)} (α: (BHom a b).(CHom) f g)
    (h: (BHom b c).(CObj)): (BHom a c).(CHom) (bcomp f h) (bcomp g h);
  bunitL {a b} (f: (BHom a b).(CObj)): Iso (BHom a b) (bcomp (bid a) f) f;
  bunitR {a b} (f: (BHom a b).(CObj)): Iso (BHom a b) (bcomp f (bid b)) f;
  bassoc {a b c d} (f: (BHom a b).(CObj)) (g: (BHom b c).(CObj))
    (h: (BHom c d).(CObj)):
    Iso (BHom a d) (bcomp (bcomp f g) h) (bcomp f (bcomp g h));
  bwhiskerLId {a b c} (f: (BHom a b).(CObj)) (g: (BHom b c).(CObj)):
    bwhiskerL f (cid g) = cid (bcomp f g);
  bwhiskerRId {a b c} (f: (BHom a b).(CObj)) (g: (BHom b c).(CObj)):
    bwhiskerR (cid f) g = cid (bcomp f g);
  bwhiskerLComp {a b c} (f: (BHom a b).(CObj)) {g h i: (BHom b c).(CObj)}
    (α: (BHom b c).(CHom) g h) (β: (BHom b c).(CHom) h i):
    bwhiskerL f (α ⨟ β) = bwhiskerL f α ⨟ bwhiskerL f β;
  bwhiskerRComp {a b c} {f g h: (BHom a b).(CObj)}
    (α: (BHom a b).(CHom) f g) (β: (BHom a b).(CHom) g h)
    (i: (BHom b c).(CObj)):
    bwhiskerR (α ⨟ β) i = bwhiskerR α i ⨟ bwhiskerR β i;
  binterchange {a b c} {f g: (BHom a b).(CObj)} {h i: (BHom b c).(CObj)}
    (α: (BHom a b).(CHom) f g) (β: (BHom b c).(CHom) h i):
    bwhiskerR α h ⨟ bwhiskerL g β = bwhiskerL f β ⨟ bwhiskerR α i;
  bunitLNat {a b} {f g: (BHom a b).(CObj)} (α: (BHom a b).(CHom) f g):
    bwhiskerL (bid a) α ⨟ (bunitL g).(isoHom) = (bunitL f).(isoHom) ⨟ α;
  bunitRNat {a b} {f g: (BHom a b).(CObj)} (α: (BHom a b).(CHom) f g):
    bwhiskerR α (bid b) ⨟ (bunitR g).(isoHom) = (bunitR f).(isoHom) ⨟ α;
  bassocNatL {a b c d} (f: (BHom a b).(CObj)) (g: (BHom b c).(CObj))
    {h i: (BHom c d).(CObj)} (α: (BHom c d).(CHom) h i):
    bwhiskerL (bcomp f g) α ⨟ (bassoc f g i).(isoHom)
    = (bassoc f g h).(isoHom) ⨟ bwhiskerL f (bwhiskerL g α);
  bassocNatR {a b c d} {f g: (BHom a b).(CObj)} (α: (BHom a b).(CHom) f g)
    (h: (BHom b c).(CObj)) (i: (BHom c d).(CObj)):
    bwhiskerR (bwhiskerR α h) i ⨟ (bassoc g h i).(isoHom)
    = (bassoc f h i).(isoHom) ⨟ bwhiskerR α (bcomp h i);
  bassocNatM {a b c d} (f: (BHom a b).(CObj)) {g h: (BHom b c).(CObj)}
    (α: (BHom b c).(CHom) g h) (i: (BHom c d).(CObj)):
    bwhiskerR (bwhiskerL f α) i ⨟ (bassoc f h i).(isoHom)
    = (bassoc f g i).(isoHom) ⨟ bwhiskerL f (bwhiskerR α i);
  btriangle {a b c} (f: (BHom a b).(CObj)) (g: (BHom b c).(CObj)):
    (bassoc f (bid b) g).(isoHom) ⨟ bwhiskerL f (bunitL g).(isoHom)
    = bwhiskerR (bunitR f).(isoHom) g;
  bpentagon {a b c d e} (f: (BHom a b).(CObj)) (g: (BHom b c).(CObj))
    (h: (BHom c d).(CObj)) (i: (BHom d e).(CObj)):
    (bassoc (bcomp f g) h i).(isoHom) ⨟ (bassoc f g (bcomp h i)).(isoHom)
    = bwhiskerR (bassoc f g h).(isoHom) i
      ⨟ ((bassoc f (bcomp g h) i).(isoHom) ⨟ bwhiskerL f (bassoc g h i).(isoHom));
}.
Arguments bid {_} _.
Arguments bcomp {_ _ _ _} _ _.
Arguments bwhiskerL {_ _ _ _} _ {_ _} _.
Arguments bwhiskerR {_ _ _ _ _ _} _ _.
Arguments bunitL {_ _ _} _.
Arguments bunitR {_ _ _} _.
Arguments bassoc {_ _ _ _ _} _ _ _.

(** Notation for the two levels of cells and their compositions. *)
Definition Hom (B: Bicategory) (a b: B.(BObj)): Type := (B.(BHom) a b).(CObj).
Definition Hom2 {B: Bicategory} {a b} (f g: Hom B a b): HSet :=
  (B.(BHom) a b).(CHom) f g.
Definition id1 {B: Bicategory} (a: B.(BObj)) := bid a.
Definition comp1 {B: Bicategory} {a b c} (f: Hom B a b) (g: Hom B b c) := bcomp f g.
Definition id2 {B: Bicategory} {a b} (f: Hom B a b): Hom2 f f := cid f.
Definition comp2 {B: Bicategory} {a b} {f g h: Hom B a b}
  (α: Hom2 f g) (β: Hom2 g h): Hom2 f h := α ⨟ β.
Definition whiskerL {B: Bicategory} {a b c} (f: Hom B a b)
  {g h: Hom B b c} (α: Hom2 g h) := bwhiskerL f α.
Definition whiskerR {B: Bicategory} {a b c} {f g: Hom B a b}
  (α: Hom2 f g) (h: Hom B b c) := bwhiskerR α h.
Infix "⨟₁" := comp1 (at level 40, left associativity).
Infix "⨟₂" := comp2 (at level 40, left associativity).
Notation "f ◁ α" := (whiskerL f α) (at level 36, left associativity).
Notation "α ▷ h" := (whiskerR α h) (at level 36, left associativity).

Definition hom2Rew {B: Bicategory} {a b} {f f' g g': Hom B a b}
  (p: f = f') (q: g = g') (α: Hom2 f g): Hom2 f' g' :=
  rew [fun v => Hom2 f' v] q in (rew [fun u => Hom2 u g] p in α).
Definition idTo2 {B: Bicategory} {a b} {f g: Hom B a b} (p: f = g): Hom2 f g :=
  hom2Rew eq_refl p (id2 f).

Lemma idTo2WhiskerR {B: Bicategory} {a b c} {f g: Hom B a b}
  (p: f = g) (h: Hom B b c):
  idTo2 p ▷ h = idTo2 (f_equal (fun u => u ⨟₁ h) p).
Proof. destruct p. apply B.(bwhiskerRId). Qed.

Lemma idTo2WhiskerL {B: Bicategory} {a b c} (f: Hom B a b)
  {g h: Hom B b c} (p: g = h):
  f ◁ idTo2 p = idTo2 (f_equal (comp1 f) p).
Proof. destruct p. apply B.(bwhiskerLId). Qed.

Lemma hom2RewEquation {B: Bicategory} {a b} {f f' g g': Hom B a b}
  (p: f = f') (q: g = g') (α: Hom2 f g) (β: Hom2 f' g'):
  α = hom2Rew (eq_sym p) (eq_sym q) β
  <-> α ⨟₂ idTo2 q = idTo2 p ⨟₂ β.
Proof.
  destruct p, q. change (α = β <-> α ⨟ cid g = cid f ⨟ β).
  now rewrite cidl, cidr.
Qed.

Definition IsLocallyGroupoid (B: Bicategory): Type :=
  forall a b (f g: (B.(BHom) a b).(CObj)) (α: (B.(BHom) a b).(CHom) f g),
    IsInvertible α.

Definition IsLocallyUnivalent (B: Bicategory): Type :=
  forall a b, IsUnivalentCategory (B.(BHom) a b).

(** Adjoint equivalences have a unit and counit satisfying both triangle
    identities, including the associators and unitors of the bicategory. *)
Record AdjointEquivalence (B: Bicategory) (a b: B.(BObj)) := {
  adjHom: (B.(BHom) a b).(CObj);
  adjInv: (B.(BHom) b a).(CObj);
  adjUnit: Iso (B.(BHom) a a) (bid a) (bcomp adjHom adjInv);
  adjCounit: Iso (B.(BHom) b b) (bcomp adjInv adjHom) (bid b);
  adjTriangleL:
    bwhiskerR adjUnit.(isoHom) adjHom
    ⨟ ((bassoc adjHom adjInv adjHom).(isoHom)
       ⨟ (bwhiskerL adjHom adjCounit.(isoHom) ⨟ (bunitR adjHom).(isoHom)))
    = (bunitL adjHom).(isoHom);
  adjTriangleR:
    bwhiskerL adjInv adjUnit.(isoHom)
    ⨟ (inverse (bassoc adjInv adjHom adjInv).(isoInvertible)
       ⨟ (bwhiskerR adjCounit.(isoHom) adjInv ⨟ (bunitL adjInv).(isoHom)))
    = (bunitR adjInv).(isoHom);
}.

(** The total space of adjoint equivalences out of each object is
    contractible precisely when adjoint equivalences classify object paths. *)
Definition IsGloballyUnivalent (B: Bicategory): Type :=
  forall a: B.(BObj), Contr {b: B.(BObj) &T AdjointEquivalence B a b}.
