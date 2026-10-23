(** Arity, layer operations, and restriction coherence for indexed strict groupoids.
    The singleton instance retains its family literally; the Boolean instance
    combines two displayed families over their common base. *)
Set Warnings "-notation-overridden".
From Bonak.Category.Groupoid Require Export Product.
From Bonak.Lib Require Import HSet SigT Notation.
Set Primitive Projections.
Set Printing Projections.
Unset Universe Polymorphism.

Module Type LayerSig.
  Parameter arity: HSet.
  Parameter Layer: forall {G: HSetGroupoid}, (arity -> Family G) -> Family G.
  Parameter nth: forall {G: HSetGroupoid} (E: arity -> Family G) (ε: arity),
    Map (Layer E) (E ε) (idFunctor G).
  Parameter lam: forall {G H: HSetGroupoid} {D: Family G} {E: arity -> Family H}
    {F: Functor G H}, (forall ε, Map D (E ε) F) -> Map D (Layer E) F.
  Parameter nth_lam: forall {G H: HSetGroupoid} {D: Family G} {E: arity -> Family H}
    {F: Functor G H} (m: forall ε, Map D (E ε) F) ε,
    totalMap (lam m) ⨟ᶠ totalMap (nth E ε) ≐ totalMap (m ε).
  Parameter ext: forall {X G: HSetGroupoid} (E: arity -> Family G)
    (F L: Functor X (total (Layer E))),
    (F ⨟ᶠ proj _ ≐ L ⨟ᶠ proj _) ->
    (forall ε, F ⨟ᶠ totalMap (nth E ε) ≐ L ⨟ᶠ totalMap (nth E ε)) -> F ≐ L.
End LayerSig.

Module LayerTheory (A: LayerSig).
Import A.

Definition layer {G H: HSetGroupoid} (E: Family H) (S: arity -> Functor G H): Family G :=
  Layer (fun ε => reindex E (S ε)).

Definition layerProj {G H: HSetGroupoid} (E: Family H) (S: arity -> Functor G H) ε :=
  totalMap (nth (fun ω => reindex E (S ω)) ε) ⨟ᶠ reindexTotal E (S ε).

Definition layerMap {X Y G H: HSetGroupoid} {E: Family G} {P: Family H}
  {R: Functor G H} (m: Map E P R) (S: arity -> Functor X G) (T: arity -> Functor Y H)
  (F: Functor X Y) (c: forall ε, S ε ⨟ᶠ R ≐ F ⨟ᶠ T ε):
  Map (layer E S) (layer P T) F :=
  lam (fun ε => precomposeMapId (nth (fun ω => reindex E (S ω)) ε)
    (Map.reindexMap m (S ε) (T ε) F (c ε))).

Lemma nthProj {G: HSetGroupoid} (E: arity -> Family G) ε:
  totalMap (nth E ε) ⨟ᶠ proj (E ε) ≐ proj (Layer E).
Proof.
  unshelve econstructor; [now intros|]. intros x y f.
  now exact (@mbase _ _ _ _ _ (nth E ε) x.1 y.1 x.2 y.2 f).
Defined.

Lemma layerFace {X Y G H: HSetGroupoid} {E: Family G} {P: Family H}
  {R: Functor G H} (m: Map E P R) (S: arity -> Functor X G) (T: arity -> Functor Y H)
  (F: Functor X Y) (c: forall ε, S ε ⨟ᶠ R ≐ F ⨟ᶠ T ε) ε:
  totalMap (layerMap m S T F c) ⨟ᶠ layerProj P T ε ≐
  layerProj E S ε ⨟ᶠ totalMap m.
Proof.
  unfold layerProj, layerMap.
  refine (feqSym (feqAssoc _ _ _) •ᶠ _).
  refine (feqWhiskerR (nth_lam _ ε) _ •ᶠ _).
  refine (feqWhiskerR (precomposeMapIdTotal _ _) _ •ᶠ _).
  refine (feqAssoc _ _ _ •ᶠ _).
  refine (feqWhiskerL _ (Map.reindexMapTotal m (S ε) (T ε) F (c ε)) •ᶠ _).
  now apply feqSym, feqAssoc.
Defined.

Lemma layerExt {X G H: HSetGroupoid} (E: Family H) (S: arity -> Functor G H)
  (F L: Functor X (total (layer E S)))
  (hb: F ⨟ᶠ proj _ ≐ L ⨟ᶠ proj _)
  (hc: forall ε, F ⨟ᶠ layerProj E S ε ≐ L ⨟ᶠ layerProj E S ε): F ≐ L.
Proof.
  apply (A.ext _ F L hb). intro ε.
  apply (Product.reindexExt E (S ε)).
  - refine (feqAssoc _ _ _ •ᶠ _).
    refine (feqWhiskerL F (nthProj _ ε) •ᶠ _).
    refine (hb •ᶠ _).
    refine (feqSym (feqWhiskerL L (nthProj _ ε)) •ᶠ _).
    now apply feqSym, feqAssoc.
  - now exact (feqAssoc _ _ _ •ᶠ (hc ε •ᶠ feqSym (feqAssoc _ _ _))).
Defined.

Lemma layerMapCone {C D X Y G H: HSetGroupoid}
  {E: Family G} {P: Family H} {R: Functor G H} (m: Map E P R)
  (U: arity -> Functor X G) (V: arity -> Functor Y H)
  (r: Functor X Y) (c: forall ε, U ε ⨟ᶠ R ≐ r ⨟ᶠ V ε)
  (a: Functor C D) (f: Functor D (total (layer P V)))
  (g: Functor C (total (layer E U)))
  (hb: (a ⨟ᶠ f) ⨟ᶠ proj _ ≐ (g ⨟ᶠ proj _) ⨟ᶠ r)
  (hc: forall ε, (a ⨟ᶠ f) ⨟ᶠ layerProj P V ε ≐
    (g ⨟ᶠ layerProj E U ε) ⨟ᶠ totalMap m):
  a ⨟ᶠ f ≐ g ⨟ᶠ totalMap (layerMap m U V r c).
Proof.
  apply (layerExt P V).
  - refine (hb •ᶠ feqSym _).
    refine (feqAssoc _ _ _ •ᶠ _).
    refine (feqWhiskerL _ (totalProj _) •ᶠ _).
    now apply feqSym, feqAssoc.
  - intro ε. refine (hc ε •ᶠ feqSym _).
    refine (feqAssoc _ _ _ •ᶠ _).
    refine (feqWhiskerL _ (layerFace m U V r c ε) •ᶠ _).
    now apply feqSym, feqAssoc.
Defined.

Lemma layerNth {X Y G H: HSetGroupoid} {E: Family G} {P: Family H}
  {R: Functor G H} (m: Map E P R) (S: arity -> Functor X G) (T: arity -> Functor Y H)
  (F: Functor X Y) (c: forall ε, S ε ⨟ᶠ R ≐ F ⨟ᶠ T ε) ε:
  totalMap (layerMap m S T F c) ⨟ᶠ totalMap (nth (fun ω => reindex P (T ω)) ε) ≐
  totalMap (nth (fun ω => reindex E (S ω)) ε) ⨟ᶠ
    totalMap (Map.reindexMap m (S ε) (T ε) F (c ε)).
Proof. now exact (nth_lam _ ε •ᶠ precomposeMapIdTotal _ _). Defined.

(** Layer coherence is displayed over the supplied frame coherence. *)
Definition layerMapEq {X Y Z G H K: HSetGroupoid}
  {E: Family G} {P: Family H} {Q: Family K}
  {r r': Functor G H} {s s': Functor H K}
  (m: Map E P r) (m': Map E P r') (n: Map P Q s) (n': Map P Q s')
  (S: arity -> Functor X G) (T: arity -> Functor Y H) (U: arity -> Functor Z K)
  (F F': Functor X Y) (L L': Functor Y Z)
  (c: forall ε, S ε ⨟ᶠ r ≐ F ⨟ᶠ T ε) (c': forall ε, S ε ⨟ᶠ r' ≐ F' ⨟ᶠ T ε)
  (d: forall ε, T ε ⨟ᶠ s ≐ L ⨟ᶠ U ε) (d': forall ε, T ε ⨟ᶠ s' ≐ L' ⨟ᶠ U ε)
  (hb: F ⨟ᶠ L ≐ F' ⨟ᶠ L') {hComposite: r ⨟ᶠ s ≐ r' ⨟ᶠ s'}
  (hc: MapEq hComposite (compMap m n) (compMap m' n')):
  MapEq hb
    (compMap (layerMap m S T F c) (layerMap n T U L d))
    (compMap (layerMap m' S T F' c') (layerMap n' T U L' d')).
Proof.
  apply (mapEqOfTotal hb), (A.ext (fun ε => reindex Q (U ε))).
  - refine (composeSquares _ _ _ _ _ _ _
      (totalProj (layerMap m S T F c)) (totalProj (layerMap n T U L d)) •ᶠ _).
    refine (feqWhiskerL (proj (layer E S)) hb •ᶠ _).
    now exact (feqSym (composeSquares _ _ _ _ _ _ _
      (totalProj (layerMap m' S T F' c'))
      (totalProj (layerMap n' T U L' d')))).
  - intro ε. refine (composeSquares _ _ _ _ _ _ _
      (layerNth m S T F c ε) (layerNth n T U L d ε) •ᶠ _).
    refine (feqWhiskerL (totalMap (nth (fun ω => reindex E (S ω)) ε))
      (totalMapEq hb (reindexMapEq m m' n n' (S ε) (T ε) (U ε)
        F F' L L' (c ε) (c' ε) (d ε) (d' ε) hb hc)) •ᶠ _).
    now exact (feqSym (composeSquares _ _ _ _ _ _ _
      (layerNth m' S T F' c' ε) (layerNth n' T U L' d' ε))).
Defined.

Definition layerHead {G H: HSetGroupoid} (E: Family H) (S: arity -> Functor G H)
  (P: Family (total (layer E S))) ε: Map (sigma (layer E S) P) E (S ε) :=
  precomposeMapId (sigmaFst _ P)
    (precomposeMapId (nth (fun ω => reindex E (S ω)) ε) (forgetPull E (S ε))).

Lemma layerHeadTotal {G H: HSetGroupoid} (E: Family H) (S: arity -> Functor G H)
  (P: Family (total (layer E S))) ε:
  totalMap (layerHead E S P ε) ≐ totalMap (sigmaFst (layer E S) P) ⨟ᶠ layerProj E S ε.
Proof. unshelve econstructor; now intros. Defined.

Lemma sigmaLayerHead {X Y G H: HSetGroupoid} {E: Family G} {P: Family H}
  {R: Functor G H} (m: Map E P R) (S: arity -> Functor X G) (T: arity -> Functor Y H)
  (F: Functor X Y) (c: forall ε, S ε ⨟ᶠ R ≐ F ⨟ᶠ T ε)
  {Q: Family (total (layer E S))} {U: Family (total (layer P T))}
  (n: Map Q U (totalMap (layerMap m S T F c))) ε:
  totalMap (sigmaMap (layerMap m S T F c) n) ⨟ᶠ totalMap (layerHead P T U ε) ≐
  totalMap (layerHead E S Q ε) ⨟ᶠ totalMap m.
Proof.
  refine (feqWhiskerL _ (layerHeadTotal P T U ε) •ᶠ _).
  refine (feqSym (feqAssoc _ _ _) •ᶠ _).
  refine (feqWhiskerR (sigmaFstTotal (layerMap m S T F c) n) _ •ᶠ _).
  refine (feqAssoc _ _ _ •ᶠ _).
  refine (feqWhiskerL _ (layerFace m S T F c ε) •ᶠ _).
  refine (feqSym (feqAssoc _ _ _) •ᶠ _).
  now exact (feqWhiskerR (feqSym (layerHeadTotal E S Q ε)) _).
Defined.

End LayerTheory.

Module SimplicialLayer <: LayerSig.
  Definition arity: HSet := hunit.
  Definition Layer {G: HSetGroupoid} (E: arity -> Family G): Family G := E tt.
  Definition nth {G: HSetGroupoid} (E: arity -> Family G) (ε: arity):
    Map (Layer E) (E ε) (idFunctor G) :=
    match ε with tt => idMap (E tt) end.
  Definition lam {G H: HSetGroupoid} {D: Family G} {E: arity -> Family H}
    {F: Functor G H} (m: forall ε, Map D (E ε) F): Map D (Layer E) F := m tt.
  Lemma nth_lam {G H: HSetGroupoid} {D: Family G} {E: arity -> Family H}
    {F: Functor G H} (m: forall ε, Map D (E ε) F) ε:
    totalMap (lam m) ⨟ᶠ totalMap (nth E ε) ≐ totalMap (m ε).
  Proof. destruct ε. unshelve econstructor; now intros. Defined.
  Lemma ext {X G: HSetGroupoid} (E: arity -> Family G)
    (F L: Functor X (total (Layer E))) (hb: F ⨟ᶠ proj _ ≐ L ⨟ᶠ proj _)
    (hc: forall ε, F ⨟ᶠ totalMap (nth E ε) ≐ L ⨟ᶠ totalMap (nth E ε)): F ≐ L.
  Proof.
    now exact (@Build_FunctorEq X (total (Layer E)) F L
      (fun x => (hc tt).(objEq) x) (fun x y f => (hc tt).(homEq) x y f)).
  Defined.
End SimplicialLayer.

Module CubicalLayer <: LayerSig.
  Definition arity: HSet := hbool.
  Definition Layer {G: HSetGroupoid} (E: arity -> Family G): Family G :=
    familyProduct (E false) (E true).
  Definition nth {G: HSetGroupoid} (E: arity -> Family G) (ε: arity):
    Map (Layer E) (E ε) (idFunctor G) :=
    match ε with true => productSnd (E false) (E true) | false => productFst (E false) (E true) end.
  Definition lam {G H: HSetGroupoid} {D: Family G} {E: arity -> Family H}
    {F: Functor G H} (m: forall ε, Map D (E ε) F): Map D (Layer E) F :=
    productPair (m false) (m true).
  Lemma nth_lam {G H: HSetGroupoid} {D: Family G} {E: arity -> Family H}
    {F: Functor G H} (m: forall ε, Map D (E ε) F) ε:
    totalMap (lam m) ⨟ᶠ totalMap (nth E ε) ≐ totalMap (m ε).
  Proof. destruct ε; unshelve econstructor; now intros. Defined.
  Lemma ext {X G: HSetGroupoid} (E: arity -> Family G)
    (F L: Functor X (total (Layer E))) (hb: F ⨟ᶠ proj _ ≐ L ⨟ᶠ proj _)
    (hc: forall ε, F ⨟ᶠ totalMap (nth E ε) ≐ L ⨟ᶠ totalMap (nth E ε)): F ≐ L.
  Proof. now exact (productExt (E false) (E true) F L (hc false) (hc true)). Defined.
End CubicalLayer.
