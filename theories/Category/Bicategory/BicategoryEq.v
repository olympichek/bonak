(** Structure identity for bicategories. The preservation paths identify
    the 1-cell operations; preservation of unitors and associators is an
    equality of 2-cells. *)
Set Warnings "-notation-overridden".
From Bonak.Lib Require Import HSet Notation RewLemmas Funext.
From Bonak.Category Require Import CategoryEq.
From Bonak.Category.Bicategory Require Export Bicategory.
From Stdlib Require Import Logic.FunctionalExtensionality.
Set Primitive Projections.
Set Printing Projections.

Record BicategoryStructureMap (S T: Bicategory) := {
  f2obj: S.(BObj) -> T.(BObj);
  f2hom {a b}: (Hom S) a b -> (Hom T) (f2obj a) (f2obj b);
  f2id1 a: f2hom (id1 a) = id1 (f2obj a);
  f2comp1 {a b c} (f: (Hom S) a b) (g: (Hom S) b c):
    f2hom (f ⨟₁ g) = f2hom f ⨟₁ f2hom g;
  f2hom2 {a b} {f g: (Hom S) a b} (α: Hom2 f g): Hom2 (f2hom f) (f2hom g);
  f2id2 {a b} (f: (Hom S) a b): f2hom2 (id2 f) = id2 (f2hom f);
  f2comp2 {a b} {f g h: (Hom S) a b} (α: Hom2 f g) (β: Hom2 g h):
    f2hom2 (α ⨟₂ β) = f2hom2 α ⨟₂ f2hom2 β;
  f2whiskerL {a b c} (f: (Hom S) a b) {g h: (Hom S) b c} (α: Hom2 g h):
    f2hom2 (f ◁ α)
    = hom2Rew (eq_sym (f2comp1 f g)) (eq_sym (f2comp1 f h))
        (f2hom f ◁ f2hom2 α);
  f2whiskerR {a b c} {f g: (Hom S) a b} (α: Hom2 f g) (h: (Hom S) b c):
    f2hom2 (α ▷ h)
    = hom2Rew (eq_sym (f2comp1 f h)) (eq_sym (f2comp1 g h))
        (f2hom2 α ▷ f2hom h);
  f2unitL {a b} (f: Hom S a b):
    f2hom2 (S.(bunitL) f).(isoHom)
    = hom2Rew
        (eq_sym (f2comp1 (id1 a) f
          • f_equal (fun u => u ⨟₁ f2hom f) (f2id1 a))) eq_refl
        (T.(bunitL) (f2hom f)).(isoHom);
  f2unitR {a b} (f: Hom S a b):
    f2hom2 (S.(bunitR) f).(isoHom)
    = hom2Rew
        (eq_sym (f2comp1 f (id1 b)
          • f_equal (comp1 (f2hom f)) (f2id1 b))) eq_refl
        (T.(bunitR) (f2hom f)).(isoHom);
  f2assoc {a b c d} (f: Hom S a b) (g: Hom S b c) (h: Hom S c d):
    f2hom2 (S.(bassoc) f g h).(isoHom)
    = hom2Rew
        (eq_sym (f2comp1 (f ⨟₁ g) h
          • f_equal (fun u => u ⨟₁ f2hom h) (f2comp1 f g)))
        (eq_sym (f2comp1 f (g ⨟₁ h)
          • f_equal (comp1 (f2hom f)) (f2comp1 g h)))
        (T.(bassoc) (f2hom f) (f2hom g) (f2hom h)).(isoHom);
}.

Arguments f2obj {S T} _ _.
Arguments f2hom {S T} _ {a b} _.
Arguments f2id1 {S T} _ _.
Arguments f2comp1 {S T} _ {a b c} _ _.
Arguments f2hom2 {S T} _ {a b f g} _.
Arguments f2id2 {S T} _ {a b} _.
Arguments f2comp2 {S T} _ {a b f g h} _ _.
Arguments f2whiskerL {S T} _ {a b c} _ {g h} _.
Arguments f2whiskerR {S T} _ {a b c f g} _ _.

Arguments f2unitL {S T} _ {a b} _.
Arguments f2unitR {S T} _ {a b} _.
Arguments f2assoc {S T} _ {a b c d} _ _ _.

Section StructureIdentity.
Context (S: Bicategory).
Context (O: Type) (H: O -> O -> Type) (H2: forall a b, H a b -> H a b -> HSet)
  (i2: forall a b (f: H a b), H2 a b f f)
  (c2: forall a b (f g h: H a b), H2 a b f g -> H2 a b g h -> H2 a b f h)
  (l2: forall a b (f g: H a b) (α: H2 a b f g), c2 a b f f g (i2 a b f) α = α)
  (r2: forall a b (f g: H a b) (α: H2 a b f g), c2 a b f g g α (i2 a b g) = α)
  (a2: forall a b (f g h i: H a b) (α: H2 a b f g) (β: H2 a b g h) (γ: H2 a b h i),
    c2 a b f h i (c2 a b f g h α β) γ = c2 a b f g i α (c2 a b g h i β γ)).

Local Abbreviation homCategory :=
  (fun a b => catOf (H a b) (H2 a b) (i2 a b) (c2 a b) (l2 a b) (r2 a b) (a2 a b)).

Context
  (bid: forall a,
    (homCategory a a).(CObj))
  (bcomp: forall {a b c} (f: (homCategory a b).(CObj)) (g: (homCategory b c).(CObj)),
    (homCategory a c).(CObj))
  (bwhiskerL: forall {a b c} (f: (homCategory a b).(CObj)) {g h: (homCategory b c).(CObj)}
    (α: (homCategory b c).(CHom) g h),
    (homCategory a c).(CHom) (bcomp f g) (bcomp f h))
  (bwhiskerR: forall {a b c} {f g: (homCategory a b).(CObj)} (α: (homCategory a b).(CHom) f g)
    (h: (homCategory b c).(CObj)),
    (homCategory a c).(CHom) (bcomp f h) (bcomp g h))
  (bunitL: forall {a b} (f: (homCategory a b).(CObj)),
    Iso (homCategory a b) (bcomp (bid a) f) f)
  (bunitR: forall {a b} (f: (homCategory a b).(CObj)),
    Iso (homCategory a b) (bcomp f (bid b)) f)
  (bassoc: forall {a b c d} (f: (homCategory a b).(CObj)) (g: (homCategory b c).(CObj))
    (h: (homCategory c d).(CObj)),
    Iso (homCategory a d) (bcomp (bcomp f g) h) (bcomp f (bcomp g h)))
  (bwhiskerLId: forall {a b c} (f: (homCategory a b).(CObj)) (g: (homCategory b c).(CObj)),
    bwhiskerL f (cid g) = cid (bcomp f g))
  (bwhiskerRId: forall {a b c} (f: (homCategory a b).(CObj)) (g: (homCategory b c).(CObj)),
    bwhiskerR (cid f) g = cid (bcomp f g))
  (bwhiskerLComp: forall {a b c} (f: (homCategory a b).(CObj)) {g h i: (homCategory b c).(CObj)}
    (α: (homCategory b c).(CHom) g h) (β: (homCategory b c).(CHom) h i),
    bwhiskerL f (α ⨟ β) = bwhiskerL f α ⨟ bwhiskerL f β)
  (bwhiskerRComp: forall {a b c} {f g h: (homCategory a b).(CObj)}
    (α: (homCategory a b).(CHom) f g) (β: (homCategory a b).(CHom) g h)
    (i: (homCategory b c).(CObj)),
    bwhiskerR (α ⨟ β) i = bwhiskerR α i ⨟ bwhiskerR β i)
  (binterchange: forall {a b c} {f g: (homCategory a b).(CObj)} {h i: (homCategory b c).(CObj)}
    (α: (homCategory a b).(CHom) f g) (β: (homCategory b c).(CHom) h i),
    bwhiskerR α h ⨟ bwhiskerL g β = bwhiskerL f β ⨟ bwhiskerR α i)
  (bunitLNat: forall {a b} {f g: (homCategory a b).(CObj)} (α: (homCategory a b).(CHom) f g),
    bwhiskerL (bid a) α ⨟ (bunitL g).(isoHom) = (bunitL f).(isoHom) ⨟ α)
  (bunitRNat: forall {a b} {f g: (homCategory a b).(CObj)} (α: (homCategory a b).(CHom) f g),
    bwhiskerR α (bid b) ⨟ (bunitR g).(isoHom) = (bunitR f).(isoHom) ⨟ α)
  (bassocNatL: forall {a b c d} (f: (homCategory a b).(CObj)) (g: (homCategory b c).(CObj))
    {h i: (homCategory c d).(CObj)} (α: (homCategory c d).(CHom) h i),
    bwhiskerL (bcomp f g) α ⨟ (bassoc f g i).(isoHom)
    = (bassoc f g h).(isoHom) ⨟ bwhiskerL f (bwhiskerL g α))
  (bassocNatR: forall {a b c d} {f g: (homCategory a b).(CObj)} (α: (homCategory a b).(CHom) f g)
    (h: (homCategory b c).(CObj)) (i: (homCategory c d).(CObj)),
    bwhiskerR (bwhiskerR α h) i ⨟ (bassoc g h i).(isoHom)
    = (bassoc f h i).(isoHom) ⨟ bwhiskerR α (bcomp h i))
  (bassocNatM: forall {a b c d} (f: (homCategory a b).(CObj)) {g h: (homCategory b c).(CObj)}
    (α: (homCategory b c).(CHom) g h) (i: (homCategory c d).(CObj)),
    bwhiskerR (bwhiskerL f α) i ⨟ (bassoc f h i).(isoHom)
    = (bassoc f g i).(isoHom) ⨟ bwhiskerL f (bwhiskerR α i))
  (btriangle: forall {a b c} (f: (homCategory a b).(CObj)) (g: (homCategory b c).(CObj)),
    (bassoc f (bid b) g).(isoHom) ⨟ bwhiskerL f (bunitL g).(isoHom)
    = bwhiskerR (bunitR f).(isoHom) g)
  (bpentagon: forall {a b c d e} (f: (homCategory a b).(CObj)) (g: (homCategory b c).(CObj))
    (h: (homCategory c d).(CObj)) (i: (homCategory d e).(CObj)),
    (bassoc (bcomp f g) h i).(isoHom) ⨟ (bassoc f g (bcomp h i)).(isoHom)
    = bwhiskerR (bassoc f g h).(isoHom) i
      ⨟ ((bassoc f (bcomp g h) i).(isoHom) ⨟ bwhiskerL f (bassoc g h i).(isoHom))).

Local Definition target: Bicategory :=
  @Build_Bicategory O homCategory (@bid) (@bcomp) (@bwhiskerL) (@bwhiskerR) (@bunitL) (@bunitR)
    (@bassoc) (@bwhiskerLId) (@bwhiskerRId) (@bwhiskerLComp) (@bwhiskerRComp) (@binterchange)
    (@bunitLNat) (@bunitRNat) (@bassocNatL) (@bassocNatR) (@bassocNatM) (@btriangle) (@bpentagon).

Local Lemma bicategoryEqOf
  (Φ: BicategoryStructureMap S target)
  (eObj: S.(BObj) = target.(BObj))
  (eObjMap: Φ.(f2obj) = fun a => rew [fun X: Type => X] eObj in a)
  (eHom: forall a b, (Hom S) a b = (Hom target) (Φ.(f2obj) a) (Φ.(f2obj) b))
  (eHomMap: @f2hom S target Φ
            = fun a b f => rew [fun X: Type => X] (eHom a b) in f)
  (eHom2: forall a b (f g: (Hom S) a b),
     @Hom2 S a b f g = @Hom2 target (Φ.(f2obj) a) (Φ.(f2obj) b)
                         (Φ.(f2hom) f) (Φ.(f2hom) g))
  (eHom2Map: @f2hom2 S target Φ
             = fun a b f g α => rew [Dom] (eHom2 a b f g) in α):
  S = target.
Proof.
  destruct Φ as [Fo Fh Fid1 Fcomp1 Fh2 Fid2 Fcomp2 FwL FwR eUnitL eUnitR eAssoc].
  cbv beta iota zeta delta [target Hom Hom2 id1 comp1 id2 comp2 whiskerL whiskerR catOf hom2Rew] in *.
  simpl in *.
  unfold Hom in *; simpl in *.
  revert bwhiskerLId bwhiskerRId bwhiskerLComp bwhiskerRComp binterchange bunitLNat bunitRNat
    bassocNatL bassocNatR bassocNatM btriangle bpentagon.
  subst Fo; destruct eObj; cbn in *.
  subst Fh; cbn in *.
  revert H2 i2 c2 l2 r2 a2 bid bcomp bwhiskerL bwhiskerR bunitL bunitR bassoc
    eHom2 Fh2 eHom2Map Fid1 Fid2 Fcomp2 Fcomp1 FwL FwR eUnitL eUnitR eAssoc.
  pattern H, eHom.
  refine (homInd2 (Hom S) _ _ H eHom).
  intros H2 i2 c2 l2 r2 a2 bid bcomp bwhiskerL bwhiskerR bunitL bunitR bassoc
    eHom2 Fh2 eHom2Map Fid1 Fid2 Fcomp2 Fcomp1 FwL FwR eUnitL eUnitR eAssoc.
  cbn in *. subst Fh2; cbn in *.
  revert i2 c2 l2 r2 a2 bid bcomp bwhiskerL bwhiskerR bunitL bunitR bassoc Fid1 Fid2 Fcomp2 Fcomp1 FwL FwR eUnitL eUnitR eAssoc.
  pattern H2, eHom2.
  refine (homInd4 (@Hom2 S) _ _ H2 eHom2).
  intros i2 c2 l2 r2 a2 bid bcomp bwhiskerL bwhiskerR bunitL bunitR bassoc Fid1 Fid2 Fcomp2 Fcomp1 FwL FwR eUnitL eUnitR eAssoc.
  cbn in *.
  assert (Ei2: (fun a b f => @id2 S a b f) = i2).
  { repeat (apply functional_extensionality_dep; intro). apply Fid2. }
  destruct Ei2.
  assert (Ec2: (fun a b f g h α β => @comp2 S a b f g h α β) = c2).
  { repeat (apply functional_extensionality_dep; intro). apply Fcomp2. }
  destruct Ec2.
  assert (El2: (fun a b f g α => (S.(BHom) a b).(cidl) (a := f) (b := g) α) = l2).
  { repeat (apply functional_extensionality_dep; intro). apply UIP. }
  destruct El2.
  assert (Er2: (fun a b f g α => (S.(BHom) a b).(cidr) (a := f) (b := g) α) = r2).
  { repeat (apply functional_extensionality_dep; intro). apply UIP. }
  destruct Er2.
  assert (Ea2: (fun a b f g h i α β γ => (S.(BHom) a b).(cassoc) (a := f) (b := g) (c := h) (d := i) α β γ) = a2).
  { repeat (apply functional_extensionality_dep; intro). apply UIP. }
  destruct Ea2.
  revert bunitL bunitR bassoc FwL FwR eUnitL eUnitR eAssoc.
  pattern bid, Fid1.
  refine (homInd1 S.(Bicategory.bid) _ _ bid Fid1).
  intros bunitL bunitR bassoc FwL FwR eUnitL eUnitR eAssoc.
  revert bwhiskerL bwhiskerR bunitL bunitR bassoc FwL FwR eUnitL eUnitR eAssoc.
  pattern (@bcomp), Fcomp1.
  refine (homInd5 (@Bicategory.bcomp S) _ _ (@bcomp) Fcomp1).
  intros bwhiskerL bwhiskerR bunitL bunitR bassoc FwL FwR eUnitL eUnitR eAssoc.
  cbn in *.
  assert (EwL: (@Bicategory.bwhiskerL S) = (@bwhiskerL)).
  { repeat (apply functional_extensionality_dep; intro). apply FwL. }
  destruct EwL.
  assert (EwR: (@Bicategory.bwhiskerR S) = (@bwhiskerR)).
  { repeat (apply functional_extensionality_dep; intro). apply FwR. }
  destruct EwR.
  assert (EuL: (@Bicategory.bunitL S) = (@bunitL)).
  { repeat (apply functional_extensionality_dep; intro). apply isoEq. apply eUnitL. }
  destruct EuL.
  assert (EuR: (@Bicategory.bunitR S) = (@bunitR)).
  { repeat (apply functional_extensionality_dep; intro). apply isoEq. apply eUnitR. }
  destruct EuR.
  assert (Eas: (@Bicategory.bassoc S) = (@bassoc)).
  { repeat (apply functional_extensionality_dep; intro). apply isoEq. apply eAssoc. }
  destruct Eas.
  intros bwhiskerLId bwhiskerRId bwhiskerLComp bwhiskerRComp binterchange bunitLNat bunitRNat
    bassocNatL bassocNatR bassocNatM btriangle bpentagon.
  assert (E: (@Bicategory.bwhiskerLId S) = (@bwhiskerLId)).
  { repeat (apply functional_extensionality_dep; intro). apply UIP. }
  destruct E.
  assert (E: (@Bicategory.bwhiskerRId S) = (@bwhiskerRId)).
  { repeat (apply functional_extensionality_dep; intro). apply UIP. }
  destruct E.
  assert (E: (@Bicategory.bwhiskerLComp S) = (@bwhiskerLComp)).
  { repeat (apply functional_extensionality_dep; intro). apply UIP. }
  destruct E.
  assert (E: (@Bicategory.bwhiskerRComp S) = (@bwhiskerRComp)).
  { repeat (apply functional_extensionality_dep; intro). apply UIP. }
  destruct E.
  assert (E: (@Bicategory.binterchange S) = (@binterchange)).
  { repeat (apply functional_extensionality_dep; intro). apply UIP. }
  destruct E.
  assert (E: (@Bicategory.bunitLNat S) = (@bunitLNat)).
  { repeat (apply functional_extensionality_dep; intro). apply UIP. }
  destruct E.
  assert (E: (@Bicategory.bunitRNat S) = (@bunitRNat)).
  { repeat (apply functional_extensionality_dep; intro). apply UIP. }
  destruct E.
  assert (E: (@Bicategory.bassocNatL S) = (@bassocNatL)).
  { repeat (apply functional_extensionality_dep; intro). apply UIP. }
  destruct E.
  assert (E: (@Bicategory.bassocNatR S) = (@bassocNatR)).
  { repeat (apply functional_extensionality_dep; intro). apply UIP. }
  destruct E.
  assert (E: (@Bicategory.bassocNatM S) = (@bassocNatM)).
  { repeat (apply functional_extensionality_dep; intro). apply UIP. }
  destruct E.
  assert (E: (@Bicategory.btriangle S) = (@btriangle)).
  { repeat (apply functional_extensionality_dep; intro). apply UIP. }
  destruct E.
  assert (E: (@Bicategory.bpentagon S) = (@bpentagon)).
  { repeat (apply functional_extensionality_dep; intro). apply UIP. }
  destruct E.
  reflexivity.
Qed.
End StructureIdentity.

Lemma bicategoryEq (S T: Bicategory) (Φ: BicategoryStructureMap S T)
  (eObj: S.(BObj) = T.(BObj))
  (eObjMap: Φ.(f2obj) = fun a => rew [fun X: Type => X] eObj in a)
  (eHom: forall a b, (Hom S) a b = (Hom T) (Φ.(f2obj) a) (Φ.(f2obj) b))
  (eHomMap: @f2hom S T Φ
            = fun a b f => rew [fun X: Type => X] (eHom a b) in f)
  (eHom2: forall a b (f g: (Hom S) a b),
     @Hom2 S a b f g = @Hom2 T (Φ.(f2obj) a) (Φ.(f2obj) b)
                         (Φ.(f2hom) f) (Φ.(f2hom) g))
  (eHom2Map: @f2hom2 S T Φ
             = fun a b f g α => rew [Dom] (eHom2 a b f g) in α):
  S = T.
Proof.
  exact (bicategoryEqOf S T.(BObj) (Hom T) (@Hom2 T)
    (@id2 T) (@comp2 T)
    (fun a b => @cidl (T.(BHom) a b))
    (fun a b => @cidr (T.(BHom) a b))
    (fun a b => @cassoc (T.(BHom) a b))
    (@Bicategory.bid T) (@Bicategory.bcomp T) (@Bicategory.bwhiskerL T) (@Bicategory.bwhiskerR T)
    (@Bicategory.bunitL T) (@Bicategory.bunitR T) (@Bicategory.bassoc T) (@Bicategory.bwhiskerLId T)
    (@Bicategory.bwhiskerRId T) (@Bicategory.bwhiskerLComp T) (@Bicategory.bwhiskerRComp T)
    (@Bicategory.binterchange T) (@Bicategory.bunitLNat T) (@Bicategory.bunitRNat T)
    (@Bicategory.bassocNatL T) (@Bicategory.bassocNatR T) (@Bicategory.bassocNatM T)
    (@Bicategory.btriangle T) (@Bicategory.bpentagon T)
    Φ eObj eObjMap eHom eHomMap eHom2 eHom2Map).
Qed.
