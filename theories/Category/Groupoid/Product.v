(** Product functors and products of displayed families over a common base. *)
Set Warnings "-notation-overridden".
From Bonak.Category.Groupoid Require Export Map.
From Bonak.Lib Require Import HSet SigT Notation RewLemmas.
Set Primitive Projections.
Set Printing Projections.
Set Universe Polymorphism.

Definition pairFunctor {X G H: HSetGroupoid} (F: Functor X G) (L: Functor X H):
  Functor X (total (const G H)).
Proof.
  refine (Build_Functor X (total (const G H)) (fun x => (F.(fobj) x; L.(fobj) x))
    (fun x y f => (F.(fhom) f, L.(fhom) f)) _ _).
  - intro x. cbn. now rewrite F.(fid), L.(fid).
  - intros x y z f g. cbn. now rewrite F.(fcomp), L.(fcomp).
Defined.

Lemma pairComp {W X G H: HSetGroupoid} (R: Functor W X)
  (F: Functor X G) (L: Functor X H):
  R ⨟ᶠ pairFunctor F L ≐ pairFunctor (R ⨟ᶠ F) (R ⨟ᶠ L).
Proof. unshelve econstructor; now intros. Defined.

Local Lemma castPairArrow {G H: HSetGroupoid} {x x' y y': G} {a a' b b': H}
  (p: x = x') (q: a = a') (r: y = y') (s: b = b')
  (f: G.(CHom) x y) (g: H.(CHom) a b):
  castArrow (G := total (const G H))
    (eq_existT_nondep p q) (eq_existT_nondep r s) (f, g) =
  (castArrow p r f, castArrow q s g).
Proof. now destruct p, q, r, s. Defined.

Definition pairCongr {X G H: HSetGroupoid}
  {F F': Functor X G} {L L': Functor X H} (e: F ≐ F') (h: L ≐ L'):
  pairFunctor F L ≐ pairFunctor F' L'.
Proof.
  refine (@Build_FunctorEq X (total (const G H)) (pairFunctor F L) (pairFunctor F' L')
    (fun x => eq_existT_nondep (e.(objEq) x) (h.(objEq) x)) _).
  intros x y f. cbn beta.
  change (castArrow (G := total (const G H))
    (eq_existT_nondep (e.(objEq) x) (h.(objEq) x))
    (eq_existT_nondep (e.(objEq) y) (h.(objEq) y))
    (F.(fhom) f, L.(fhom) f) = (F'.(fhom) f, L'.(fhom) f)).
  now rewrite (castPairArrow (G := G) (H := H)), e.(homEq), h.(homEq).
Defined.

(** The second component's arrow lies over the first component's base arrow. *)
Definition familyProduct {G: HSetGroupoid} (E P: Family G): Family G :=
  sigma E (reindex P (proj E)).

Definition productFst {G: HSetGroupoid} (E P: Family G):
  Map (familyProduct E P) E (idFunctor G) := sigmaFst E (reindex P (proj E)).

Definition productSnd {G: HSetGroupoid} (E P: Family G):
  Map (familyProduct E P) P (idFunctor G) :=
  @Build_Map G G (familyProduct E P) P (idFunctor G)
    (fun x a => a.2) (fun x y a b f => f.2.1)
    (fun _ _ => eq_refl) (fun _ _ _ _ _ _ _ _ => eq_refl) (fun _ _ _ _ f => f.2.2).

Definition productPair {G H: HSetGroupoid} {D: Family G} {E P: Family H}
  {F: Functor G H} (m: Map D E F) (n: Map D P F): Map D (familyProduct E P) F.
Proof.
  refine (@Build_Map G H D (familyProduct E P) F
    (fun x a => (m.(mobj) x a; n.(mobj) x a))
    (fun x y a b f => (m.(mhom) f; (n.(mhom) f; n.(mbase) f • eq_sym (m.(mbase) f)))) _ _ _).
  - intros. apply (eq_sigT_nondep_hprop (fun _ _ _ _ => UIP _)); cbn.
    + now apply m.(mid).
    + now apply n.(mid).
  - intros. apply (eq_sigT_nondep_hprop (fun _ _ _ _ => UIP _)); cbn.
    + now apply m.(mcomp).
    + now apply n.(mcomp).
  - intros. now apply m.(mbase).
Defined.

Local Definition observeProduct {G: HSetGroupoid} (E P: Family G) :=
  pairFunctor (totalMap (productFst E P)) (totalMap (productSnd E P)).

Local Lemma observeProductObj {G: HSetGroupoid} (E P: Family G)
  (x y: total (familyProduct E P)):
  (observeProduct E P).(fobj) x = (observeProduct E P).(fobj) y -> x = y.
Proof.
  intros h. destruct x as [x [a b]], y as [y [c d]].
  pose proof (f_equal (fun z => z.1.1) h) as e; cbn in e. destruct e.
  assert (a = c) as ha.
  { now apply (@sigTSecond G (fun x => E.(dobj) x) x a c (f_equal (fun z => z.1) h)). }
  assert (b = d) as hb.
  { now apply (@sigTSecond G (fun x => P.(dobj) x) x b d
      (f_equal (fun z: total (const (total E) (total P)) => z.2) h)). }
  now destruct ha, hb.
Defined.

Local Lemma observeProductHom {G: HSetGroupoid} (E P: Family G)
  (x y: total (familyProduct E P)) (f g: (total (familyProduct E P)).(CHom) x y):
  (observeProduct E P).(fhom) f = (observeProduct E P).(fhom) g -> f = g.
Proof.
  intro h. apply (eq_sigT_nondep_hprop (fun _ _ _ _ => UIP _)).
  - now exact (f_equal fst h).
  - now exact (f_equal snd h).
Defined.

Lemma productExt {X G: HSetGroupoid} (E P: Family G)
  (F L: Functor X (total (familyProduct E P)))
  (h: F ⨟ᶠ totalMap (productFst E P) ≐ L ⨟ᶠ totalMap (productFst E P))
  (k: F ⨟ᶠ totalMap (productSnd E P) ≐ L ⨟ᶠ totalMap (productSnd E P)): F ≐ L.
Proof.
  apply (cancelObservation (observeProduct E P)
    (@hsetGroupoidUIP (total (const (total E) (total P))))
    (observeProductObj E P) (observeProductHom E P)).
  now exact (pairComp F _ _ •ᶠ (pairCongr h k •ᶠ feqSym (pairComp L _ _))).
Defined.

(** The base and fiber projections jointly determine maps into a pullback. *)
Local Definition observeReindex {G H: HSetGroupoid} (E: Family H) (S: Functor G H) :=
  pairFunctor (proj (reindex E S)) (reindexTotal E S).

Local Lemma observeReindexObj {G H: HSetGroupoid} (E: Family H) (S: Functor G H)
  (x y: total (reindex E S)):
  (observeReindex E S).(fobj) x = (observeReindex E S).(fobj) y -> x = y.
Proof.
  intros h. destruct x as [a u], y as [b v].
  pose proof (f_equal (fun z => z.1) h) as e; cbn in e. destruct e.
  apply (f_equal (fun v => (a; v))).
  now apply (@sigTSecond H (fun x => E.(dobj) x) (S.(fobj) a) u v
    (f_equal (fun z: total (const G (total E)) => z.2) h)).
Defined.

Local Lemma observeReindexHom {G H: HSetGroupoid} (E: Family H) (S: Functor G H)
  (x y: total (reindex E S)) (f g: (total (reindex E S)).(CHom) x y):
  (observeReindex E S).(fhom) f = (observeReindex E S).(fhom) g -> f = g.
Proof.
  intro h. apply (eq_sigT_nondep_hprop (fun _ _ _ _ => UIP _)).
  - now exact (f_equal fst h).
  - now exact (f_equal snd h).
Defined.

Lemma reindexExt {X G H: HSetGroupoid} (E: Family H) (S: Functor G H)
  (F L: Functor X (total (reindex E S)))
  (hb: F ⨟ᶠ proj _ ≐ L ⨟ᶠ proj _)
  (hc: F ⨟ᶠ reindexTotal E S ≐ L ⨟ᶠ reindexTotal E S): F ≐ L.
Proof.
  apply (cancelObservation (observeReindex E S)
    (@hsetGroupoidUIP (total (const G (total E))))
    (observeReindexObj E S) (observeReindexHom E S)).
  unfold observeReindex.
  now exact (pairComp F _ _ •ᶠ (pairCongr hb hc •ᶠ feqSym (pairComp L _ _))).
Defined.

(** Reindexed composites preserve a displayed square. The fiber equality
    follows the transport hexagon; uniqueness of object paths fills its
    base coherence. *)
Definition reindexMapEq {X Y Z G H K: HSetGroupoid}
  {E: Family G} {P: Family H} {Q: Family K}
  {r r': Functor G H} {s s': Functor H K}
  (m: Map E P r) (m': Map E P r') (n: Map P Q s) (n': Map P Q s')
  (S: Functor X G) (T: Functor Y H) (U: Functor Z K)
  (F F': Functor X Y) (L L': Functor Y Z)
  (c: S ⨟ᶠ r ≐ F ⨟ᶠ T) (c': S ⨟ᶠ r' ≐ F' ⨟ᶠ T)
  (d: T ⨟ᶠ s ≐ L ⨟ᶠ U) (d': T ⨟ᶠ s' ≐ L' ⨟ᶠ U)
  (hb: F ⨟ᶠ L ≐ F' ⨟ᶠ L') {hComposite: r ⨟ᶠ s ≐ r' ⨟ᶠ s'}
  (hc: MapEq hComposite (compMap m n) (compMap m' n')):
  MapEq hb
    (compMap (reindexMap m S T F c) (reindexMap n T U L d))
    (compMap (reindexMap m' S T F' c') (reindexMap n' T U L' d')).
Proof.
  assert (totalMap (reindexMap m S T F c) ⨟ᶠ
      totalMap (reindexMap n T U L d) ≐
    totalMap (reindexMap m' S T F' c') ⨟ᶠ
      totalMap (reindexMap n' T U L' d')) as h.
  { apply (reindexExt Q U).
    - refine (composeSquares _ _ _ _ _ _ _
        (totalProj (reindexMap m S T F c))
        (totalProj (reindexMap n T U L d)) •ᶠ _).
      refine (feqWhiskerL (proj (reindex E S)) hb •ᶠ _).
      now exact (feqSym (composeSquares _ _ _ _ _ _ _
        (totalProj (reindexMap m' S T F' c'))
        (totalProj (reindexMap n' T U L' d')))).
    - refine (composeSquares _ _ _ _ _ _ _
        (reindexMapTotal m S T F c) (reindexMapTotal n T U L d) •ᶠ _).
      refine (feqWhiskerL (reindexTotal E S) (totalMapEq hComposite hc) •ᶠ _).
      now exact (feqSym (composeSquares _ _ _ _ _ _ _
        (reindexMapTotal m' S T F' c')
        (reindexMapTotal n' T U L' d'))). }
  unshelve econstructor.
  - intros x a.
    change (rew [fun z => Q.(dobj) (U.(fobj) z)] hb.(objEq) x in
      rew [fun z => Q.(dobj) z] d.(objEq) (F.(fobj) x) in
        n.(mobj) (T.(fobj) (F.(fobj) x))
          (rew [fun z => P.(dobj) z] c.(objEq) x in m.(mobj) (S.(fobj) x) a) =
      rew [fun z => Q.(dobj) z] d'.(objEq) (F'.(fobj) x) in
        n'.(mobj) (T.(fobj) (F'.(fobj) x))
          (rew [fun z => P.(dobj) z] c'.(objEq) x in m'.(mobj) (S.(fobj) x) a)).
    eapply (rew_cohLayer_hex (P := fun z => Q.(dobj) z)
      (rf0 := U.(fobj)) (F := n.(mobj)) (G := n'.(mobj))
      (K := hComposite.(objEq) (S.(fobj) x))).
    + now exact (hc.(mapObjEq) (S.(fobj) x) a).
    + now apply UIP.
  - intros x y a b f.
    rewrite (@UIP (total (reindex Q U)) _ _ _ (h.(objEq) (x; a))).
    rewrite (@UIP (total (reindex Q U)) _ _ _ (h.(objEq) (y; b))).
    now exact (h.(homEq) (x; a) (y; b) f).
Defined.
