(** Pointwise laws for diagrams from a category into h-groupoids. *)

Set Warnings "-notation-overridden".
From Bonak.Lib Require Import HSet Notation RewLemmas Funext.
From Bonak.νGpd Require Import HGpd.
From Bonak.Category.Bicategory Require Export PathDiagram.
From Bonak.Category.Bicategory Require Import HGpd2Cat.
From Stdlib Require Import Logic.FunctionalExtensionality.
Set Primitive Projections.
Set Printing Projections.

(** Path algebra for whiskering conjugated comparison cells. *)

(** Whiskering a conjugated cell by a function, in the degenerate case where
    the conjugating equality is reflexivity. *)

Local Lemma whiskerAlg {G H: Type} (h: G -> H) {P Q R: G} (κ: P = R) (κ': Q = R)
  {S: H} (Λ: h R = S):
  f_equal h (κ • (eq_refl • eq_sym κ'))
  = (f_equal h κ • Λ) • (eq_refl • eq_sym (f_equal h κ' • Λ)).
Proof. now destruct κ, κ', Λ. Defined.

(** The reassociation at the heart of the inner whiskering: two composites
    [κ • μ] and [κ' • μ'] are given alternative factorisations [Θ • c] and
    [Θ' • c'], and [m], [N] compare them. *)

Local Lemma conjAlgebra {T: Type} {x1 x2 x3 z y1 y2 y3 z': T}
  (κ: x1 = x2) (μ: x2 = x3) (Θ: x1 = z) (c: z = x3)
  (κ': y1 = y2) (μ': y2 = y3) (Θ': y1 = z') (c': z' = y3)
  (m: x2 = y2) (N: x3 = y3)
  (H1: Θ • c = κ • μ) (Hom: Θ' • c' = κ' • μ') (H3: m • μ' = μ • N):
  κ • (m • eq_sym κ') = Θ • ((c • (N • eq_sym c')) • eq_sym Θ').
Proof.
  destruct κ, μ, κ', μ', m, Θ, Θ'.
  rewrite (eq_sym (eq_trans_refl_l c) • H1), (eq_sym (eq_trans_refl_l c') • Hom),
          (eq_sym (eq_trans_refl_l N) • eq_sym H3).
  now reflexivity.
Defined.

Section Pointwise.
Context {C: Category}.

(** The arrow action applied to an equality in a source hom-set. *)

Definition phomEq {ob: C.(CObj) -> HGpd} (F: PathDiagramData C ob)
  {a b} {v v': C.(CHom) a b} (E: v = v') (x: ob a):
  F.(phom) (a := a) (b := b) v x = F.(phom) (a := a) (b := b) v' x :=
  f_equal (fun w => F.(phom) (a := a) (b := b) w x) E.

Definition psfComp3 {ob: C.(CObj) -> HGpd}
  (F: PathDiagramData C ob) {a b c d} (u: C.(CHom) a b)
  (v: C.(CHom) b c) (w: C.(CHom) c d) (X: ob a):
  F.(phom) w (F.(phom) v (F.(phom) u X)) = F.(phom) (u ⨟ v ⨟ w) X :=
  f_equal (F.(phom) w) (F.(pcomp) u v X) • F.(pcomp) (u ⨟ v) w X.

(** Function composition is definitionally associative. Evaluating the
    diagram's associativity law therefore leaves only the path induced by
    associativity in the source category. *)

Lemma psfAssocPt {ob: C.(CObj) -> HGpd}
  (F: PathDiagramData C ob) (FA: PathDiagramAssoc C ob F)
  {a b c d} (f: C.(CHom) a b) (g: C.(CHom) b c)
  (h: C.(CHom) c d) (X: ob a):
  psfComp3 F f g h X
  • f_equal (fun z => F.(phom) z X) (C.(cassoc) f g h)
  = F.(pcomp) g h (F.(phom) f X) • F.(pcomp) f (g ⨟ h) X.
Proof.
  pose proof (FA a b c d f g h) as H.
  unfold hom2Rew in H.
  change (hgpdAssoc (F.(phom) f) (F.(phom) g) (F.(phom) h))
    with (@eq_refl ((Hom HGpd2Cat) (ob a) (ob d))
            ((comp1 (B := HGpd2Cat)) ((comp1 (B := HGpd2Cat)) (F.(phom) f) (F.(phom) g))
               (F.(phom) h))) in H.
  cbn [eq_sym eq_rect] in H.
  pose proof (f_equal (fun c => c X) H) as H'; clear H.
  cbv beta in H'.
  rewrite rewC2Pt, fEqualSym, f_equal_compose in H'.
  cbv beta in H'.
  now exact (movePath _ _ _ H').
Defined.

(** Naturality of the compositor in the point and in each source arrow.
    Source hom-sets identify the chosen equality of composites with the
    equality induced by composition. *)

Lemma pcompNatPt {ob: C.(CObj) -> HGpd} (F: PathDiagramData C ob)
  {a b c} (u: C.(CHom) a b) (v: C.(CHom) b c) {x y: ob a} (e: x = y):
  f_equal (F.(phom) (a := b) (b := c) v) (f_equal (F.(phom) (a := a) (b := b) u) e)
  • F.(pcomp) (a := a) (b := b) (c := c) u v y
  = F.(pcomp) (a := a) (b := b) (c := c) u v x
    • f_equal (F.(phom) (a := a) (b := c) (ccomp u v)) e.
Proof.
  rewrite f_equal_compose.
  now exact (homotopyNat _ _ (F.(pcomp) (a := a) (b := b) (c := c) u v) e).
Defined.

Lemma pcompNatL {ob: C.(CObj) -> HGpd} (F: PathDiagramData C ob)
  {a b c} {u u': C.(CHom) a b} (Eu: u = u') (v: C.(CHom) b c)
  (Euv: ccomp u v = ccomp u' v) (x: ob a):
  f_equal (F.(phom) (a := b) (b := c) v) (phomEq F Eu x)
  • F.(pcomp) (a := a) (b := b) (c := c) u' v x
  = F.(pcomp) (a := a) (b := b) (c := c) u v x • phomEq F Euv x.
Proof.
  destruct Eu.
  rewrite ((C.(CHom) a c).(UIP) (h := Euv) (g := eq_refl)).
  now exact (eq_trans_refl_l _).
Defined.

Lemma pcompNatR {ob: C.(CObj) -> HGpd} (F: PathDiagramData C ob)
  {a b c} (u: C.(CHom) a b) {v v': C.(CHom) b c} (Ev: v = v')
  (Euv: ccomp u v = ccomp u v') (x: ob a):
  phomEq F Ev (F.(phom) (a := a) (b := b) u x)
  • F.(pcomp) (a := a) (b := b) (c := c) u v' x
  = F.(pcomp) (a := a) (b := b) (c := c) u v x • phomEq F Euv x.
Proof.
  destruct Ev.
  rewrite ((C.(CHom) a c).(UIP) (h := Euv) (g := eq_refl)).
  now exact (eq_trans_refl_l _).
Defined.

(** Changing the source arrows in a composite of comparison homotopies.
    The second form expresses the inverse composite. *)

Lemma pcompCompareNat {ob: C.(CObj) -> HGpd} (F: PathDiagramData C ob)
  {a b c} {u u': C.(CHom) a b} (Eu: u = u') {v v': C.(CHom) b c} (Ev: v = v')
  (SU: ob a -> ob b) (HU: forall z, SU z = F.(phom) (a := a) (b := b) u z)
  (Euv: ccomp u v = ccomp u' v') (X: ob a):
  phomEq F Ev (SU X)
  • (f_equal (F.(phom) (a := b) (b := c) v') (HU X • phomEq F Eu X)
     • F.(pcomp) (a := a) (b := b) (c := c) u' v' X)
  = f_equal (F.(phom) (a := b) (b := c) v) (HU X)
    • (F.(pcomp) (a := a) (b := b) (c := c) u v X • phomEq F Euv X).
Proof.
  destruct Eu, Ev.
  rewrite ((C.(CHom) a c).(UIP) (h := Euv) (g := eq_refl)).
  now exact (eq_trans_refl_l _).
Defined.

Lemma pcompCompareNatSym {ob: C.(CObj) -> HGpd} (F: PathDiagramData C ob)
  {a b c} {u u': C.(CHom) a b} (Eu: u = u') {v v': C.(CHom) b c} (Ev: v = v')
  (SU: ob a -> ob b) (HU: forall z, SU z = F.(phom) (a := a) (b := b) u z)
  (SV: ob b -> ob c) (HV: forall z, SV z = F.(phom) (a := b) (b := c) v z)
  (Euv: ccomp u v = ccomp u' v') (X: ob a):
  eq_sym (F.(pcomp) (a := a) (b := b) (c := c) u' v' X)
  • (eq_sym (f_equal (F.(phom) (a := b) (b := c) v')
               (HU X • phomEq F Eu X))
     • eq_sym (HV (SU X) • phomEq F Ev (SU X)))
  = eq_sym (phomEq F Euv X)
    • (eq_sym (F.(pcomp) (a := a) (b := b) (c := c) u v X)
       • (eq_sym (f_equal (F.(phom) (a := b) (b := c) v) (HU X))
          • eq_sym (HV (SU X)))).
Proof.
  destruct Eu, Ev.
  rewrite ((C.(CHom) a c).(UIP) (h := Euv) (g := eq_refl)).
  now exact (eq_sym (eq_trans_refl_l _)).
Defined.

(** The axioms of a path diagram, evaluated at a point

    In [HGpd2Cat] a 2-cell is a homotopy, so each axiom becomes a family of
    equalities between composites of paths. Equalities of source arrows
    remain parameters, since any parallel paths in a source hom-set agree. *)

Definition pidPt {ob: C.(CObj) -> HGpd} (F: PathDiagramData C ob)
  (a: C.(CObj)) (x: ob a): F.(phom) (a := a) (b := a) (C.(cid) a) x = x :=
  f_equal (fun h => h x) (F.(pid) a).

Lemma phomEqHapply {ob: C.(CObj) -> HGpd} (F: PathDiagramData C ob)
  {a b} {w w': C.(CHom) a b} (P: w = w') (x: ob a):
  f_equal (fun h: ob a -> ob b => h x) (f_equal (F.(phom) (a := a) (b := b)) P)
  = phomEq F P x.
Proof. now destruct P. Defined.

(** The two unit comparisons of a pseudofunctor into [HGpd2Cat], evaluated at a
    point. Both unit axioms transport the identity 2-cell, so once the
    identification of the unit with the identity function is consumed only the
    transport along the equality of source arrows is left. *)

Lemma psfUnitLPt {ob: C.(CObj) -> HGpd} (F: PathDiagramData C ob)
  {a b} (f: C.(CHom) a b) (x: ob a):
  f_equal (fun h: ob a -> ob b => h x) (psfUnitL C ob F f)
  = f_equal (F.(phom) (a := a) (b := b) f) (pidPt F a x).
Proof.
  unfold psfUnitL.
  refine (psfUnitLAlgebra _ (F.(pid) a) (hgpdUnitL _) x • _).
  now reflexivity.
Defined.

Lemma psfUnitRPt {ob: C.(CObj) -> HGpd} (F: PathDiagramData C ob)
  {a b} (f: C.(CHom) a b) (x: ob a):
  f_equal (fun h: ob a -> ob b => h x) (psfUnitR C ob F f)
  = pidPt F b (F.(phom) (a := a) (b := b) f x).
Proof.
  unfold psfUnitR.
  refine (psfUnitRAlgebra _ (F.(pid) b) (hgpdUnitR _) x • _).
  now reflexivity.
Defined.

(** Pointwise forms of the three diagram laws, allowing any source paths
    with the indicated endpoints. *)

Definition PathDiagramUnitLPt {ob: C.(CObj) -> HGpd}
  (F: PathDiagramData C ob): Type :=
  forall a b (f: C.(CHom) a b) (E: ccomp (C.(cid) a) f = f) (x: ob a),
    F.(pcomp) (a := a) (b := a) (c := b) (C.(cid) a) f x
    = f_equal (F.(phom) (a := a) (b := b) f) (pidPt F a x)
      • eq_sym (phomEq F E x).

Definition PathDiagramUnitRPt {ob: C.(CObj) -> HGpd}
  (F: PathDiagramData C ob): Type :=
  forall a b (f: C.(CHom) a b) (E: ccomp f (C.(cid) b) = f) (x: ob a),
    F.(pcomp) (a := a) (b := b) (c := b) f (C.(cid) b) x
    = pidPt F b (F.(phom) (a := a) (b := b) f x) • eq_sym (phomEq F E x).

Definition PathDiagramAssocPt {ob: C.(CObj) -> HGpd}
  (F: PathDiagramData C ob): Type :=
  forall a b c d (u: C.(CHom) a b) (v: C.(CHom) b c) (w: C.(CHom) c d)
    (E: ccomp (ccomp u v) w = ccomp u (ccomp v w)) (x: ob a),
    f_equal (F.(phom) (a := c) (b := d) w)
      (F.(pcomp) (a := a) (b := b) (c := c) u v x)
    • (F.(pcomp) (a := a) (b := c) (c := d) (ccomp u v) w x • phomEq F E x)
    = F.(pcomp) (a := b) (b := c) (c := d) v w
        (F.(phom) (a := a) (b := b) u x)
      • F.(pcomp) (a := a) (b := b) (c := d) u (ccomp v w) x.

Lemma pcompUnitLPt {ob: C.(CObj) -> HGpd} (F: PathDiagramData C ob)
  (FU: PathDiagramUnitL C ob F): PathDiagramUnitLPt F.
Proof.
  intros a b f E x.
  refine (f_equal (fun c => c x) (FU a b f) • _).
  rewrite hom2RewPt, hgpd2CatI2Pt, !fEqualSym, eq_sym_involutive.
  rewrite psfUnitLPt, phomEqHapply, eq_trans_refl_l.
  refine (transCongL _ (f_equal (@eq_sym _ _ _)
    (f_equal (fun e: ccomp (C.(cid) a) f = f => phomEq F e x) _))).
  now exact ((C.(CHom) a b).(UIP)).
Defined.

Lemma pcompUnitRPt {ob: C.(CObj) -> HGpd} (F: PathDiagramData C ob)
  (FU: PathDiagramUnitR C ob F): PathDiagramUnitRPt F.
Proof.
  intros a b f E x.
  refine (f_equal (fun c => c x) (FU a b f) • _).
  rewrite hom2RewPt, hgpd2CatI2Pt, !fEqualSym, eq_sym_involutive.
  rewrite psfUnitRPt, phomEqHapply, eq_trans_refl_l.
  refine (transCongL _ (f_equal (@eq_sym _ _ _)
    (f_equal (fun e: ccomp f (C.(cid) b) = f => phomEq F e x) _))).
  now exact ((C.(CHom) a b).(UIP)).
Defined.

(** Associativity with an arbitrary source associativity path and a
    right-associated chain of comparison cells. *)

Lemma pcompAssocPt {ob: C.(CObj) -> HGpd} (F: PathDiagramData C ob)
  (FA: PathDiagramAssoc C ob F): PathDiagramAssocPt F.
Proof.
  intros a b c d u v w E x.
  refine (eq_sym (eqTransAssoc _ _ _) • _).
  refine (_ • psfAssocPt F FA u v w x).
  unfold psfComp3.
  refine (f_equal (fun z => _ • z)
    (f_equal (fun e: ccomp (ccomp u v) w = ccomp u (ccomp v w) => phomEq F e x)
       _)).
  now exact ((C.(CHom) a d).(UIP)).
Defined.

(** Pointwise laws reconstruct the complete diagram laws by functional
    extensionality. The source hom-set identifies any chosen unit or
    associativity path with the one stored in the category. *)

Lemma pathDiagramUnitLOfPt {ob: C.(CObj) -> HGpd}
  (F: PathDiagramData C ob) (H: PathDiagramUnitLPt F): PathDiagramUnitL C ob F.
Proof.
  intros a b f. apply functional_extensionality_dep; intro x.
  rewrite hom2RewPt, hgpd2CatI2Pt, !fEqualSym, eq_sym_involutive.
  rewrite psfUnitLPt, phomEqHapply, eq_trans_refl_l.
  exact (H a b f (C.(cidl) f) x).
Qed.

Lemma pathDiagramUnitROfPt {ob: C.(CObj) -> HGpd}
  (F: PathDiagramData C ob) (H: PathDiagramUnitRPt F): PathDiagramUnitR C ob F.
Proof.
  intros a b f. apply functional_extensionality_dep; intro x.
  rewrite hom2RewPt, hgpd2CatI2Pt, !fEqualSym, eq_sym_involutive.
  rewrite psfUnitRPt, phomEqHapply, eq_trans_refl_l.
  exact (H a b f (C.(cidr) f) x).
Qed.

Lemma pathDiagramAssocOfPt {ob: C.(CObj) -> HGpd}
  (F: PathDiagramData C ob) (H: PathDiagramAssocPt F): PathDiagramAssoc C ob F.
Proof.
  intros a b c d f g h. apply functional_extensionality_dep; intro x.
  rewrite hom2RewPt.
  cbn [hgpdAssoc eq_sym f_equal HGpd2Cat comp2 whiskerL whiskerR].
  rewrite eq_trans_refl_l, fEqualSym, phomEqHapply.
  apply (transCancelR _ _ (phomEq F (C.(cassoc) f g h) x)).
  rewrite transSymCancelR2.
  change ((f_equal (F.(phom) h) (F.(pcomp) f g x)
    • F.(pcomp) (f ⨟ g) h x) • phomEq F (C.(cassoc) f g h) x
    = F.(pcomp) g h (F.(phom) f x) • F.(pcomp) f (g ⨟ h) x).
  rewrite eqTransAssoc.
  exact (H a b c d f g h (C.(cassoc) f g h) x).
Qed.

(** Right whiskering of a conjugated comparison. Naturality of the
    compositor suffices; no associativity law is needed. *)

Lemma pcompWhiskerL {ob: C.(CObj) -> HGpd}
  (F: PathDiagramData C ob) {a c d} {g g': C.(CHom) a c} (e: g = g')
  (w: C.(CHom) c d) (X: ob a) {P Q: ob c}
  (κ: P = F.(phom) g X) (κ': Q = F.(phom) g' X):
  f_equal (F.(phom) w) (κ • (f_equal (fun z => F.(phom) z X) e • eq_sym κ'))
  = (f_equal (F.(phom) w) κ • F.(pcomp) g w X)
    • (f_equal (fun z => F.(phom) z X) (f_equal (fun z => z ⨟ w) e)
       • eq_sym (f_equal (F.(phom) w) κ' • F.(pcomp) g' w X)).
Proof. destruct e. now exact (whiskerAlg _ κ κ' (F.(pcomp) g w X)). Defined.

(** Left whiskering of a conjugated comparison, expressed through the
    three-fold compositor and the source associators. *)

Lemma pcompWhiskerR {ob: C.(CObj) -> HGpd}
  (F: PathDiagramData C ob) (FA: PathDiagramAssoc C ob F)
  {a b c d} (u: C.(CHom) a b)
  {v v': C.(CHom) b c} {w w': C.(CHom) c d}
  (e: v ⨟ w = v' ⨟ w') (X: ob a):
  F.(pcomp) v w (F.(phom) u X)
  • (f_equal (fun z => F.(phom) z (F.(phom) u X)) e
     • eq_sym (F.(pcomp) v' w' (F.(phom) u X)))
  = psfComp3 F u v w X
    • (f_equal (fun z => F.(phom) z X)
        (C.(cassoc) u v w
         • (f_equal (ccomp u) e
            • eq_sym (C.(cassoc) u v' w')))
       • eq_sym (psfComp3 F u v' w' X)).
Proof.
  rewrite !eq_trans_map_distr, fEqualSym.
  now exact (conjAlgebra _ _ _ _ _ _ _ _ _ _ (psfAssocPt F FA u v w X)
    (psfAssocPt F FA u v' w' X) (pcompNatR F u e (f_equal (ccomp u) e) X)).
Defined.

End Pointwise.
