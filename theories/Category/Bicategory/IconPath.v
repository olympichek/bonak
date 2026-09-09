(** An icon between path diagrams into 1-types is a path.

    The 2-cells of [HGpd2Cat] are homotopies, and under functional
    extensionality a homotopy is an identification. An icon therefore carries
    exactly the data of an identification of the two arrow parts, and its two
    axioms are the transport statements of the remaining fields along that
    identification: [icId] for the unit path, [icComp] for the
    compositors. Since the compositors live in a hom-h-set, the three axioms
    of a path diagram are propositions and impose nothing further.

    The proof consumes the identification of arrow parts through [homInd4],
    which reduces to the case where the two arrow parts are literally the same
    function and the icon's components are reflexivity; the two axioms then
    read off directly as equalities of the remaining fields. *)

Set Warnings "-notation-overridden".
From Bonak.Lib Require Import RewLemmas.
From Bonak Require Import HSet Notation Funext.
From Bonak Require Import νGpd.HGpd.
From Bonak.Category Require Import Category.
From Bonak.Category.Bicategory Require Import Bicategory.
From Stdlib Require Import Logic.FunctionalExtensionality.

From Bonak.Category.Bicategory Require Import PathDiagram.

From Bonak.Category.Bicategory Require Import HGpd2Cat.
Set Primitive Projections.
Set Printing Projections.

(** The identity 2-cell transported along two equalities with the same
    endpoints identifies them. *)

Lemma hom2RewId2Eq {X Y: HGpd} {u v: X -> Y} (p q: u = v)
  (H: @hom2Rew HGpd2Cat X Y u v u v p q (fun x => eq_refl) = fun _ => eq_refl):
  p = q.
Proof.
  apply happlyInj; intro x.
  refine (symTransCancel _ _ _).
  now exact (eq_sym (hom2RewPt p q (fun x => eq_refl) x) • happly H x).
Defined.

(** Equality proofs between 2-cells of [HGpd2Cat] are unique. *)

Lemma hom2UIP {X: Type} {Y: HGpd} {f g: X -> Y} (α β: forall x, f x = g x)
  (u v: α = β): u = v.
Proof. now apply (@hpiT_UIP X (fun x => hpaths (f x) (g x)) α β). Defined.

Section IconPath.
Context {C: Category} {ob: C.(CObj) -> HGpd2Cat.(BObj)}.

(** The three axioms of a path diagram are propositions: each is a
    family of equalities between 2-cells. *)

Lemma pathDiagramUnitLProp (S: PathDiagramData C ob)
  (u v: PathDiagramUnitL C ob S): u = v.
Proof.
  apply functional_extensionality_dep; intro a.
  apply functional_extensionality_dep; intro b.
  apply functional_extensionality_dep; intro f.
  now apply hom2UIP.
Defined.

Lemma pathDiagramUnitRProp (S: PathDiagramData C ob)
  (u v: PathDiagramUnitR C ob S): u = v.
Proof.
  apply functional_extensionality_dep; intro a.
  apply functional_extensionality_dep; intro b.
  apply functional_extensionality_dep; intro f.
  now apply hom2UIP.
Defined.

Lemma pathDiagramAssocProp (S: PathDiagramData C ob)
  (u v: PathDiagramAssoc C ob S): u = v.
Proof.
  apply functional_extensionality_dep; intro a.
  apply functional_extensionality_dep; intro b.
  apply functional_extensionality_dep; intro c.
  apply functional_extensionality_dep; intro d.
  apply functional_extensionality_dep; intro f.
  apply functional_extensionality_dep; intro g.
  apply functional_extensionality_dep; intro h.
  now apply hom2UIP.
Defined.

(** A path diagram is determined by its underlying [PathDiagramData]. *)

Lemma pathDiagramEqOn (F G: PathDiagram C ob)
  (H: pathData C ob F = pathData C ob G): F = G.
Proof.
  destruct F as [S uL uR aS], G as [S' uL' uR' aS']; simpl in H.
  destruct H.
  rewrite (pathDiagramUnitLProp S uL uL'), (pathDiagramUnitRProp S uR uR'),
          (pathDiagramAssocProp S aS aS').
  now reflexivity.
Defined.

(** The comparison at the level of the underlying data. The icon's components
    and its two axioms are spelled out pointwise, so that they are consumed by
    [homInd4] with no unfolding. *)

Lemma iconPathOn
  (P P': forall a b, C.(CHom) a b -> ob a -> ob b)
  (pid: forall a, P a a (C.(cid) a) = id1 (ob a))
  (pid': forall a, P' a a (C.(cid) a) = id1 (ob a))
  (pco: forall a b c (f: C.(CHom) a b) (g: C.(CHom) b c) (x: ob a),
     P b c g (P a b f x) = P a c (f ⨟ g) x)
  (pco': forall a b c (f: C.(CHom) a b) (g: C.(CHom) b c) (x: ob a),
     P' b c g (P' a b f x) = P' a c (f ⨟ g) x)
  (ic: forall a b (f: C.(CHom) a b) (x: ob a), P a b f x = P' a b f x)
  (icI: forall a,
     @hom2Rew HGpd2Cat (ob a) (ob a) (P a a (C.(cid) a)) (id1 (ob a))
       (P' a a (C.(cid) a)) (id1 (ob a)) (pid a) (pid' a)
       (fun x => ic a a (C.(cid) a) x) = fun _ => eq_refl)
  (icC: forall a b c (f: C.(CHom) a b) (g: C.(CHom) b c),
     (fun x => (f_equal (P b c g) (ic a b f x) • ic b c g (P' a b f x))
               • pco' a b c f g x)
     = (fun x => pco a b c f g x • ic a c (f ⨟ g) x)):
  Build_PathDiagramData C ob P pid pco
  = Build_PathDiagramData C ob P' pid' pco'.
Proof.
  revert pid' pco' icI icC; revert P' ic.
  refine (homInd4 (I1 := C.(CObj)) (I2 := fun _ => C.(CObj))
            (I3 := fun a b => C.(CHom) a b) (I4 := fun a _ _ => ob a)
            (B := fun _ b _ _ => ob b) P _ _).
  intros pid' pco' icI icC.
  assert (HI: pid = pid').
  { apply functional_extensionality_dep; intro a.
    now exact (hom2RewId2Eq (pid a) (pid' a) (icI a)). }
  assert (HC: pco = pco').
  { apply functional_extensionality_dep; intro a.
    apply functional_extensionality_dep; intro b.
    apply functional_extensionality_dep; intro c.
    apply functional_extensionality_dep; intro f.
    apply functional_extensionality_dep; intro g.
    apply functional_extensionality_dep; intro x.
    now exact (eq_sym (happly (icC a b c f g) x)
      • eq_trans_refl_l (pco' a b c f g x)). }
  now destruct HI, HC.
Defined.

Lemma iconPathStr (F G: PathDiagramData C ob) (I: Icon F G): F = G.
Proof.
  now exact (iconPathOn
    (fun a b (f: C.(CHom) a b) x => F.(phom) (a := a) (b := b) f x)
    (fun a b (f: C.(CHom) a b) x => G.(phom) (a := a) (b := b) f x)
    (fun a => F.(pid) a) (fun a => G.(pid) a)
    (fun a b c f g x => F.(pcomp) (a := a) (b := b) (c := c) f g x)
    (fun a b c f g x => G.(pcomp) (a := a) (b := b) (c := c) f g x)
    (fun a b f => @icCell C ob F G I a b f)
    (fun a => @icId C ob F G I a)
    (fun a b c f g => @icComp C ob F G I a b c f g)).
Defined.

Lemma iconPath (F G: PathDiagram C ob)
  (I: Icon (pathData C ob F) (pathData C ob G)): F = G.
Proof.
  now exact (pathDiagramEqOn F G
    (iconPathStr (pathData C ob F) (pathData C ob G) I)).
Defined.

End IconPath.
