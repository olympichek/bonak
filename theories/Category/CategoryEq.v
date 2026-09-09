(** Structure identity and extensionality for categories and functors. *)

Set Warnings "-notation-overridden".
From Bonak.Lib Require Import SigT HSet Notation RewLemmas.
From Bonak.Category Require Import Category.
From Stdlib Require Import Logic.FunctionalExtensionality.
Set Primitive Projections.
Set Printing Projections.
Set Universe Polymorphism.

(** Functor data over a fixed map on objects. *)

Definition FunctorOn {C D: Category} (Fo: C.(CObj) -> D.(CObj)): Type :=
  {Fh: forall a b, C.(CHom) a b -> D.(CHom) (Fo a) (Fo b) &T
   {Fi: forall a, Fh a a (C.(cid) a) = D.(cid) (Fo a) &T
    forall a b c (f: C.(CHom) a b) (g: C.(CHom) b c),
      Fh a c (f ⨟ g) = Fh a b f ⨟ Fh b c g}}.

Definition ofFunctorOn {C D: Category} {Fo: C.(CObj) -> D.(CObj)}
  (z: FunctorOn Fo): Functor C D := {|
  fobj := Fo;
  fhom a b f := z.1 a b f;
  fid a := z.2.1 a;
  fcomp a b c f g := z.2.2 a b c f g;
|}.

Definition toFunctorOn {C D: Category} (F: Functor C D): FunctorOn F.(fobj) :=
  (fun a b f => F.(fhom) f;
   (fun a => F.(fid) a; fun a b c f g => F.(fcomp) f g)).

Lemma functorOnEq {C D: Category} {Fo: C.(CObj) -> D.(CObj)}
  (z w: FunctorOn Fo)
  (H: forall a b (f: C.(CHom) a b), z.1 a b f = w.1 a b f): z = w.
Proof.
  destruct z as [zh [zi zc]], w as [wh [wi wc]]; simpl in H.
  assert (e: zh = wh).
  { apply functional_extensionality_dep; intro a.
    apply functional_extensionality_dep; intro b.
    apply functional_extensionality_dep; intro f. now exact (H a b f). }
  destruct e.
  assert (ei: zi = wi).
  { apply functional_extensionality_dep; intro a. now apply (D.(CHom)). }
  destruct ei.
  assert (ec: zc = wc).
  { apply functional_extensionality_dep; intro a.
    apply functional_extensionality_dep; intro b.
    apply functional_extensionality_dep; intro c.
    apply functional_extensionality_dep; intro f.
    apply functional_extensionality_dep; intro g. now apply (D.(CHom)). }
  now destruct ec.
Qed.

Definition functorEqOn {C D: Category} {Fo: C.(CObj) -> D.(CObj)}
  (z w: FunctorOn Fo)
  (H: forall a b (f: C.(CHom) a b), z.1 a b f = w.1 a b f):
  ofFunctorOn z = ofFunctorOn w :=
  f_equal ofFunctorOn (functorOnEq z w H).

Lemma functorEqOnObj {C D: Category} {Fo: C.(CObj) -> D.(CObj)}
  (z w: FunctorOn Fo)
  (H: forall a b (f: C.(CHom) a b), z.1 a b f = w.1 a b f):
  f_equal fobj (functorEqOn z w H) = eq_refl.
Proof.
  unfold functorEqOn. rewrite f_equal_compose.
  now exact (fEqualConst Fo (functorOnEq z w H)).
Qed.

(** Extensionality for functors: the object and arrow parts determine the
    functor, because the two functoriality fields are equalities in
    hom-[HSet]s. *)

Lemma functorEq {C D} (F G: Functor C D) (Hobj: F.(fobj) = G.(fobj))
  (Hhom: forall a b (f: C.(CHom) a b),
     rew [fun o => D.(CHom) (o a) (o b)] Hobj in F.(fhom) f = G.(fhom) f):
  F = G.
Proof.
  destruct F as [Fo Fh Fi Fc], G as [Go Gh Gi Gc]; cbn in Hobj, Hhom.
  destruct Hobj.
  exact (functorEqOn (Fh; (Fi; Fc)) (Gh; (Gi; Gc)) Hhom).
Qed.

(** Categories from their data

    The three laws are propositions, so a category is determined by its
    objects, homs, identities and composition. [catEqOf] compares an
    arbitrary category with one assembled by [catOf]: the hom families are
    identified first, and identities and composition are then compared across
    that identification. *)

Definition catOf (A: Type) (H: A -> A -> HSet) (i: forall a, H a a)
  (c: forall a b d, H a b -> H b d -> H a d)
  (l: forall a b (f: H a b), c a a b (i a) f = f)
  (r: forall a b (f: H a b), c a b b f (i b) = f)
  (s: forall a b d e (f: H a b) (g: H b d) (h: H d e),
      c a d e (c a b d f g) h = c a b e f (c b d e g h)): Category := {|
  CObj := A;
  CHom := H;
  cid := i;
  ccomp a b d f g := c a b d f g;
  cidl a b f := l a b f;
  cidr a b f := r a b f;
  cassoc a b d e f g h := s a b d e f g h;
|}.

Lemma catEqOf (C: Category) (H: C.(CObj) -> C.(CObj) -> HSet)
  (i: forall a, H a a)
  (c: forall a b d, H a b -> H b d -> H a d)
  (l: forall a b (f: H a b), c a a b (i a) f = f)
  (r: forall a b (f: H a b), c a b b f (i b) = f)
  (s: forall a b d e (f: H a b) (g: H b d) (h: H d e),
      c a d e (c a b d f g) h = c a b e f (c b d e g h))
  (e: C.(CHom) = H)
  (ei: forall a, rew [fun K: C.(CObj) -> C.(CObj) -> HSet => Dom (K a a)] e in
         C.(cid) a = i a)
  (ec: forall a b d (f: C.(CHom) a b) (g: C.(CHom) b d),
         rew [fun K: C.(CObj) -> C.(CObj) -> HSet => Dom (K a d)] e in (f ⨟ g)
         = c a b d
             (rew [fun K: C.(CObj) -> C.(CObj) -> HSet => Dom (K a b)] e in f)
             (rew [fun K: C.(CObj) -> C.(CObj) -> HSet => Dom (K b d)] e in g)):
  C = catOf C.(CObj) H i c l r s.
Proof.
  destruct C as [Co Ch Ci Cc Cl Cr Cs]; simpl in *.
  destruct e; simpl in *.
  assert (e: Ci = i)
    by (apply functional_extensionality_dep; intro a; now exact (ei a)).
  destruct e.
  assert (e: Cc = c).
  { apply functional_extensionality_dep; intro a.
    apply functional_extensionality_dep; intro b.
    apply functional_extensionality_dep; intro d.
    apply functional_extensionality_dep; intro f.
    apply functional_extensionality_dep; intro g. now exact (ec a b d f g). }
  destruct e.
  assert (el: Cl = l).
  { apply functional_extensionality_dep; intro a.
    apply functional_extensionality_dep; intro b.
    apply functional_extensionality_dep; intro f. now apply (Ch a b). }
  assert (er: Cr = r).
  { apply functional_extensionality_dep; intro a.
    apply functional_extensionality_dep; intro b.
    apply functional_extensionality_dep; intro f. now apply (Ch a b). }
  assert (es: Cs = s).
  { apply functional_extensionality_dep; intro a.
    apply functional_extensionality_dep; intro b.
    apply functional_extensionality_dep; intro d.
    apply functional_extensionality_dep; intro e.
    apply functional_extensionality_dep; intro f.
    apply functional_extensionality_dep; intro g.
    apply functional_extensionality_dep; intro h. now apply (Ch a e). }
  now destruct el, er, es.
Qed.

Lemma fobjCompPathL {C D E: Category} {F F': Functor C D}
  (p: F = F') (G: Functor D E):
  f_equal fobj (f_equal (fun u => compFunctor u G) p)
  = f_equal (fun o x => G.(fobj) (o x)) (f_equal fobj p).
Proof. now destruct p. Qed.

Lemma fobjCompPathR {C D E: Category} (F: Functor C D)
  {G G': Functor D E} (p: G = G'):
  f_equal fobj (f_equal (compFunctor F) p)
  = f_equal (fun o x => o (F.(fobj) x)) (f_equal fobj p).
Proof. now destruct p. Qed.

(** Transport of natural transformations is determined on components by
    the object parts of the endpoint functor equalities. *)

Lemma ncompRew {C D: Category} {F F' K K': Functor C D}
  (p: F = F') (q: K = K') (α: NatTrans F K) (x: C.(CObj)):
  (rew [fun k => NatTrans F' k] q in rew [fun f => NatTrans f K] p in α).(ncomp) x
  = rew [fun o => D.(CHom) (F'.(fobj) x) (o x)] (f_equal fobj q) in
    rew [fun o => D.(CHom) (o x) (K.(fobj) x)] (f_equal fobj p) in α.(ncomp) x.
Proof. now destruct p, q. Qed.

Lemma ncompRewOn {C D: Category} {Fo Ko: C.(CObj) -> D.(CObj)}
  (zF wF: FunctorOn Fo) (zK wK: FunctorOn Ko)
  (p: ofFunctorOn zF = ofFunctorOn wF) (q: ofFunctorOn zK = ofFunctorOn wK)
  (hp: f_equal fobj p = eq_refl) (hq: f_equal fobj q = eq_refl)
  (α: NatTrans (ofFunctorOn zF) (ofFunctorOn zK)) (x: C.(CObj)):
  (rew [fun k => NatTrans (ofFunctorOn wF) k] q in
   rew [fun f => NatTrans f (ofFunctorOn zK)] p in α).(ncomp) x = α.(ncomp) x.
Proof. now rewrite ncompRew, hp, hq. Qed.
