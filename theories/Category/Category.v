(** Categories with a [Type] of objects and [HSet] hom-types.

    The three category laws are equalities in hom-h-sets, so any two proofs
    of them agree by [UIP]. Composition is written in diagrammatic order:
    [f ⨟ g] is [f] followed by [g]. *)

Set Warnings "-notation-overridden".
From Bonak Require Import SigT HSet Notation.
From Bonak.Lib Require Import RewLemmas Equiv Contractible.
From Stdlib Require Import Logic.FunctionalExtensionality.

Set Primitive Projections.
Set Printing Projections.
Set Universe Polymorphism.

Record Category := {
  CObj: Type;
  CHom: CObj -> CObj -> HSet;
  cid a: CHom a a;
  ccomp {a b c} (f: CHom a b) (g: CHom b c): CHom a c;
  cidl {a b} (f: CHom a b): ccomp (cid a) f = f;
  cidr {a b} (f: CHom a b): ccomp f (cid b) = f;
  cassoc {a b c d} (f: CHom a b) (g: CHom b c) (h: CHom c d):
    ccomp (ccomp f g) h = ccomp f (ccomp g h);
}.

Arguments ccomp {_ _ _ _} _ _.
Arguments cid {_} _.

Infix "⨟" := ccomp (at level 40, left associativity).

(** The opposite category *)

Definition Op (C: Category): Category := {|
  CObj := C.(CObj);
  CHom a b := C.(CHom) b a;
  cid a := C.(cid) a;
  ccomp a b c f g := C.(ccomp) g f;
  cidl a b f := C.(cidr) f;
  cidr a b f := C.(cidl) f;
  cassoc a b c d f g h := eq_sym (C.(cassoc) h g f);
|}.

(** Functors *)

Record Functor (C D: Category) := {
  fobj: C.(CObj) -> D.(CObj);
  fhom {a b} (f: C.(CHom) a b): D.(CHom) (fobj a) (fobj b);
  fid a: fhom (C.(cid) a) = D.(cid) (fobj a);
  fcomp {a b c} (f: C.(CHom) a b) (g: C.(CHom) b c):
    fhom (f ⨟ g) = fhom f ⨟ fhom g;
}.

Arguments fobj {C D} _ _.
Arguments fhom {C D} _ {a b} _.
Arguments fid {C D} _ _.
Arguments fcomp {C D} _ {a b c} _ _.

Definition compFunctor {C D E} (F: Functor C D) (G: Functor D E):
  Functor C E := {|
  fobj a := G.(fobj) (F.(fobj) a);
  fhom a b f := G.(fhom) (F.(fhom) f);
  fid a := f_equal G.(fhom) (F.(fid) a) • G.(fid) (F.(fobj) a);
  fcomp a b c f g :=
    f_equal G.(fhom) (F.(fcomp) f g) • G.(fcomp) (F.(fhom) f) (F.(fhom) g);
|}.

Infix "⨟ᶠ" := compFunctor (at level 40, left associativity).

Definition opFunctor {C D: Category} (F: Functor C D): Functor (Op C) (Op D) :=
  Build_Functor (Op C) (Op D) F.(fobj)
    (fun a b f => F.(fhom) f) (fun a => F.(fid) a)
    (fun a b c f g => F.(fcomp) g f).

(** The identity functor *)

Definition idFunctor (C: Category): Functor C C := {|
  fobj a := a;
  fhom a b f := f;
  fid a := eq_refl;
  fcomp a b c f g := eq_refl;
|}.

(** Natural transformations

    The naturality square is an equality in a hom-[HSet], hence a
    proposition: two natural transformations agree as soon as their
    components do. *)

Record NatTrans {C D: Category} (F G: Functor C D) := {
  ncomp a: D.(CHom) (F.(fobj) a) (G.(fobj) a);
  nnat {a b} (f: C.(CHom) a b):
    F.(fhom) f ⨟ ncomp b = ncomp a ⨟ G.(fhom) f;
}.

Arguments ncomp {C D F G} _ _.
Arguments nnat {C D F G} _ {a b} _.

Lemma natTransEq {C D: Category} {F G: Functor C D} (α β: NatTrans F G)
  (H: forall a, α.(ncomp) a = β.(ncomp) a): α = β.
Proof.
  destruct α as [ac an], β as [bc bn]; simpl in H.
  assert (e: ac = bc)
    by (apply functional_extensionality_dep; intro a; now exact (H a)).
  destruct e.
  assert (en: an = bn).
  { apply functional_extensionality_dep; intro a.
    apply functional_extensionality_dep; intro b.
    apply functional_extensionality_dep; intro f. now apply (D.(CHom)). }
  now destruct en.
Qed.

(** Operations on natural transformations *)

(** Natural transformations form an h-set: they are the pairs of a family of
    components and a naturality proof, and both live in h-sets. *)

Definition natTransData {C D: Category} (F G: Functor C D): HSet :=
  hsigT (A := hpiT (fun a => D.(CHom) (F.(fobj) a) (G.(fobj) a)))
    (fun n => hforall (a b: C.(CObj)) (f: C.(CHom) a b),
       hEq (F.(fhom) f ⨟ n b) (n a ⨟ G.(fhom) f)).

Definition natTransSet {C D: Category} (F G: Functor C D): HSet := {|
  Dom := NatTrans F G;
  UIP := retract_UIP
    (fun α: NatTrans F G =>
       ((fun a => α.(ncomp) a; fun a b f => α.(nnat) f): natTransData F G))
    (fun z => {| ncomp a := z.1 a; nnat a b f := z.2 a b f |})
    (fun α => eq_refl);
|}.

Definition idNatTrans {C D: Category} (F: Functor C D): NatTrans F F := {|
  ncomp a := D.(cid) (F.(fobj) a);
  nnat a b f := D.(cidr) (F.(fhom) f) • eq_sym (D.(cidl) (F.(fhom) f));
|}.

Lemma compNatural {C D: Category} {F G H: Functor C D} (α: NatTrans F G)
  (β: NatTrans G H) {a b} (f: C.(CHom) a b):
  F.(fhom) f ⨟ (α.(ncomp) b ⨟ β.(ncomp) b)
  = (α.(ncomp) a ⨟ β.(ncomp) a) ⨟ H.(fhom) f.
Proof.
  rewrite <- (D.(cassoc) (F.(fhom) f)), α.(nnat).
  rewrite (D.(cassoc) (α.(ncomp) a)), β.(nnat).
  now apply eq_sym, D.(cassoc).
Qed.

Definition compNatTrans {C D: Category} {F G H: Functor C D}
  (α: NatTrans F G) (β: NatTrans G H): NatTrans F H := {|
  ncomp a := α.(ncomp) a ⨟ β.(ncomp) a;
  nnat a b f := compNatural α β f;
|}.

Definition whiskerLNat {C D E: Category} (F: Functor C D)
  {G H: Functor D E} (α: NatTrans G H):
  NatTrans (compFunctor F G) (compFunctor F H) :=
  Build_NatTrans _ _ (compFunctor F G) (compFunctor F H)
    (fun a => α.(ncomp) (F.(fobj) a))
    (fun a b f => α.(nnat) (F.(fhom) f)).

Lemma whiskerRNatural {C D E: Category} {F G: Functor C D} (α: NatTrans F G)
  (H: Functor D E) {a b} (f: C.(CHom) a b):
  H.(fhom) (F.(fhom) f) ⨟ H.(fhom) (α.(ncomp) b)
  = H.(fhom) (α.(ncomp) a) ⨟ H.(fhom) (G.(fhom) f).
Proof.
  rewrite <- 2 H.(fcomp). now apply f_equal, α.(nnat).
Qed.

Definition whiskerRNat {C D E: Category} {F G: Functor C D} (α: NatTrans F G)
  (H: Functor D E): NatTrans (compFunctor F H) (compFunctor G H) :=
  Build_NatTrans _ _ (compFunctor F H) (compFunctor G H)
    (fun a => H.(fhom) (α.(ncomp) a))
    (fun a b f => whiskerRNatural α H f).


(** Functors and natural transformations form a category. The canonical
    unit and associativity transformations have identity components. *)

Definition functorCategory (C D: Category): Category.
Proof.
  refine {| CObj := Functor C D;
    CHom F G := natTransSet F G;
    cid F := idNatTrans F;
    ccomp F G H α β := compNatTrans α β |}.
  - intros F G α. apply natTransEq; intro x. apply cidl.
  - intros F G α. apply natTransEq; intro x. apply cidr.
  - intros F G H I α β γ. apply natTransEq; intro x. apply cassoc.
Defined.

Definition functorUnitL {C D: Category} (F: Functor C D):
  NatTrans (compFunctor (idFunctor C) F) F.
Proof.
  refine (Build_NatTrans C D (compFunctor (idFunctor C) F) F (fun x => cid (F.(fobj) x)) _).
  intros x y f. exact (D.(cidr) _ • eq_sym (D.(cidl) _)).
Defined.

Definition functorUnitR {C D: Category} (F: Functor C D):
  NatTrans (compFunctor F (idFunctor D)) F.
Proof.
  refine (Build_NatTrans C D (compFunctor F (idFunctor D)) F (fun x => cid (F.(fobj) x)) _).
  intros x y f. exact (D.(cidr) _ • eq_sym (D.(cidl) _)).
Defined.

Definition functorAssoc {C D E K: Category}
  (F: Functor C D) (G: Functor D E) (H: Functor E K):
  NatTrans (compFunctor (compFunctor F G) H) (compFunctor F (compFunctor G H)).
Proof.
  refine (Build_NatTrans C K (compFunctor (compFunctor F G) H)
    (compFunctor F (compFunctor G H)) (fun x => cid (H.(fobj) (G.(fobj) (F.(fobj) x)))) _).
  intros x y f. exact (K.(cidr) _ • eq_sym (K.(cidl) _)).
Defined.

(** Invertibility and the canonical isomorphism induced by an object path. *)

Record IsInvertible {C: Category} {a b: C.(CObj)} (f: C.(CHom) a b) := {
  inverse: C.(CHom) b a;
  inverseR: f ⨟ inverse = cid a;
  inverseL: inverse ⨟ f = cid b;
}.
Arguments inverse {C a b f} _.
Arguments inverseR {C a b f} _.
Arguments inverseL {C a b f} _.

Lemma isInvertibleProp {C: Category} {a b} {f: C.(CHom) a b}
  (u v: IsInvertible f): u = v.
Proof.
  destruct u as [u ur ul], v as [v vr vl].
  assert (e: u = v).
  { rewrite <- (C.(cidr) u), <- vr, <- C.(cassoc), ul. apply C.(cidl). }
  destruct e.
  assert (ur = vr) by apply (C.(CHom) a a).
  assert (ul = vl) by apply (C.(CHom) b b). now subst.
Qed.

Record Iso (C: Category) (a b: C.(CObj)) := {
  isoHom: C.(CHom) a b;
  isoInvertible: IsInvertible isoHom;
}.

Arguments isoHom {C a b} _.
Arguments isoInvertible {C a b} _.

Lemma isoEq {C a b} (u v: Iso C a b) (e: u.(isoHom) = v.(isoHom)): u = v.
Proof.
  destruct u as [u ui], v as [v vi]; cbn in e. destruct e.
  now destruct (isInvertibleProp ui vi).
Qed.

Definition isoSet (C: Category) (a b: C.(CObj)): HSet.
Proof.
  refine {| Dom := Iso C a b; UIP := _ |}.
  refine (retract_UIP
    (B := hsigT (A := C.(CHom) a b)
      (fun f => {| Dom := IsInvertible f;
                   UIP := fun x y p q => eq_hprop_UIP (@isInvertibleProp C a b f) p q |}))
    (fun f => (f.(isoHom); f.(isoInvertible)))
    (fun z => {| isoHom := z.1; isoInvertible := z.2 |})
    (fun _ => eq_refl)).
Defined.

Definition idToHom {C: Category} {a b: C.(CObj)} (p: a = b): C.(CHom) a b :=
  rew [fun x => C.(CHom) a x] p in C.(cid) a.

Definition idToIso {C: Category} {a b: C.(CObj)} (p: a = b): Iso C a b.
Proof.
  destruct p. refine {| isoHom := cid a; isoInvertible := _ |}.
  exact {| inverse := cid a; inverseR := C.(cidl) _; inverseL := C.(cidl) _ |}.
Defined.

Lemma idToIsoHom {C: Category} {a b: C.(CObj)} (p: a = b):
  (idToIso p).(isoHom) = idToHom p.
Proof. now destruct p. Qed.

Lemma idToHomTrans {C: Category} {a b c: C.(CObj)} (p: a = b) (q: b = c):
  idToHom p ⨟ idToHom q = idToHom (p • q).
Proof.
  destruct p, q. now apply C.(cidl).
Qed.

Lemma fhomIdToHom {C D: Category} (F: Functor C D)
  {a b: C.(CObj)} (p: a = b):
  F.(fhom) (idToHom p) = idToHom (f_equal F.(fobj) p).
Proof. destruct p. now apply F.(fid). Qed.

(** Categorical univalence identifies object paths with isomorphisms.
    It is stated as contractibility of the fibres of the canonical map. *)

Definition IsUnivalentCategory (C: Category): Type :=
  forall a b (f: Iso C a b), Contr {p: a = b &T idToIso p = f}.

Lemma isUnivalentCategoryProp {C} (u v: IsUnivalentCategory C): u = v.
Proof.
  repeat (apply functional_extensionality_dep; intro). apply contrProp.
Qed.

Record UnivalentCategory := {
  univalentCategory:> Category;
  categoryUnivalence: IsUnivalentCategory univalentCategory;
}.

Definition idToIsoEquiv {C: Category} (u: IsUnivalentCategory C)
  (a b: C.(CObj)): Equiv (a = b) (Iso C a b).
Proof.
  refine (qinvEquiv idToIso (fun f => (u a b f).1.1) _ _).
  - intro p. exact (f_equal (fun z => z.1) ((u a b (idToIso p)).2 (p; eq_refl))).
  - intro f. exact (u a b f).1.2.
Defined.
