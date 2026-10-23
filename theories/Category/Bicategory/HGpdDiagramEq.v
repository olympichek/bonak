(** A pseudonatural transformation of 1-type-valued diagrams whose
    components are equivalences determines an equality of diagrams. *)
Set Warnings "-notation-overridden".
From Bonak.Lib Require Import Funext Equiv RewLemmas Notation HSet.
From Bonak.νGpd Require Import HGpd.
From Bonak.Category.Bicategory Require Import HGpd2Cat Pseudonatural.
From Stdlib Require Import Logic.FunctionalExtensionality.
Set Primitive Projections.
Set Printing Projections.
Set Universe Polymorphism.

Local Lemma hgpdPsfDataEq {S: Bicategory} {ob: S.(BObj) -> HGpd}
  (F G: PsfData S HGpd2Cat ob)
  (n: forall a b (f: Hom S a b) x, F.(psHom) f x = G.(psHom) f x)
  (nc: forall a b (f g: Hom S a b) (α: Hom2 f g) x,
    F.(psCell) α x • n a b g x = n a b f x • G.(psCell) α x)
  (nu: forall a x, F.(psUnit) a x = n a a (bid a) x • G.(psUnit) a x)
  (np: forall a b c (f: Hom S a b) (g: Hom S b c) x,
    F.(psComp) f g x • n a c (bcomp f g) x =
    n b c g (F.(psHom) f x) •
      (f_equal (G.(psHom) g) (n a b f x) • G.(psComp) f g x)):
  F = G.
Proof.
  destruct F as [h c u p], G as [h' c' u' p'].
  cbn [psHom psCell psUnit psComp] in *.
  revert c' u' p' nc nu np. revert h' n.
  refine (homInd4 (I1 := S.(BObj)) (I2 := fun _ => S.(BObj))
    (I3 := fun a b => Hom S a b) (I4 := fun a _ _ => ob a)
    (B := fun _ b _ _ => ob b) h _ _).
  intros c' u' p' nc nu np.
  assert (ec: c = c').
  { repeat (apply functional_extensionality_dep; intro).
    now exact (nc _ _ _ _ _ _ • eq_trans_refl_l _). }
  assert (eu: u = u').
  { repeat (apply functional_extensionality_dep; intro).
    now exact (nu _ _ • eq_trans_refl_l _). }
  assert (ep: p = p').
  { repeat (apply functional_extensionality_dep; intro).
    now exact (np _ _ _ _ _ _ • eq_trans_refl_l _ • eq_trans_refl_l _). }
  now destruct ec, eu, ep.
Defined.

Local Lemma hgpdPsfIdentityEq {S: Bicategory} {ob: S.(BObj) -> HGpd}
  (F G: Psf S HGpd2Cat ob)
  (α: Pseudonatural (Build_Pseudofunctor S HGpd2Cat ob F)
    (Build_Pseudofunctor S HGpd2Cat ob G))
  (e: forall a x, α.(pnComponent) a x = x): F = G.
Proof.
  destruct α as [k n nc nu np]. cbn [pnComponent] in e.
  assert (ek: k = fun a x => x).
  { apply functional_extensionality_dep. intro a.
    now apply functional_extensionality_dep. }
  subst k. apply psfEqData.
  refine (hgpdPsfDataEq F.(psData) G.(psData)
    (fun a b f => (n a b f).(isoHom)) _ _ _).
  - intros a b f g β x.
    pose proof (f_equal (fun h => h x) (nc a b f g β)) as q.
    cbn in q. rewrite f_equal_id in q. now exact q.
  - intros a x.
    pose proof (f_equal (fun h => h x) (nu a)) as q.
    cbn in q. rewrite f_equal_id in q. now exact q.
  - intros a b c f g x.
    pose proof (f_equal (fun h => h x) (np a b c f g)) as q.
    cbn in q. rewrite f_equal_id in q.
    rewrite 3 eq_trans_refl_l in q. now exact q.
Defined.

Definition hgpdPseudofunctorEq {S: Bicategory}
  {F G: Pseudofunctor S HGpd2Cat} (α: Pseudonatural F G)
  (e: forall a, IsEquiv (α.(pnComponent) a)): F = G.
Proof.
  destruct F as [ob F], G as [ob' G].
  pose (E := fun a => Build_Equiv (ob a) (ob' a) (α.(pnComponent) a) (e a)).
  enough (H: forall (G: Psf S HGpd2Cat ob')
    (α: Pseudonatural (Build_Pseudofunctor S HGpd2Cat ob F)
      (Build_Pseudofunctor S HGpd2Cat ob' G)),
    (forall a x, α.(pnComponent) a x = E a x) ->
    Build_Pseudofunctor S HGpd2Cat ob F = Build_Pseudofunctor S HGpd2Cat ob' G).
  { now exact (H G α (fun a x => eq_refl)). }
  clearbody E. clear α e G.
  revert ob' E. refine (hgpdFamilyEquivInd ob _ _).
  intros G α e. apply f_equal. now exact (hgpdPsfIdentityEq F G α e).
Defined.
