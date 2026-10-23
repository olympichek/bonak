(** Groupoids, functors, and natural transformations, with no univalence
    requirement on the individual groupoids. *)
Set Warnings "-notation-overridden".
From Bonak.Lib Require Import HSet Notation RewLemmas.
From Bonak.Category Require Import Category CategoryEq Groupoid.
From Bonak.Category.Groupoid Require Import SetBased.
From Bonak.Category.Bicategory Require Import Bicategory BicategoryEq Full
  LocallyDiscrete.
Set Primitive Projections.
Set Universe Polymorphism.
Set Keyed Unification.

Local Lemma functorUnitNaturality {C: Category} {a b} (f: C.(CHom) a b):
  f ⨟ cid b = cid a ⨟ f.
Proof. now rewrite cidl, cidr. Defined.

Local Lemma functorTriangle {C D: Category} (F: Functor C D) (a: C.(CObj)):
  cid (F.(fobj) a) ⨟ cid (F.(fobj) a) = F.(fhom) (cid a).
Proof. now rewrite F.(fid), cidl. Defined.

Local Lemma functorPentagon {C D: Category} (F: Functor C D) (a: C.(CObj)):
  cid (F.(fobj) a) ⨟ cid (F.(fobj) a)
  = F.(fhom) (cid a) ⨟ (cid (F.(fobj) a) ⨟ cid (F.(fobj) a)).
Proof. now rewrite F.(fid), 2 cidl. Defined.

Definition GroupoidBicat: Bicategory := {|
  BObj := Groupoid;
  BHom G H := functorCategory G H;
  bid G := idFunctor G;
  bcomp G H K F F' := compFunctor F F';
  bwhiskerL G H K F F' F'' α := whiskerLNat F α;
  bwhiskerR G H K F F' α F'' := whiskerRNat α F'';
  bunitL G H F := Build_Iso (functorCategory G H) _ _
    (functorUnitL F) (natInvertible _);
  bunitR G H F := Build_Iso (functorCategory G H) _ _
    (functorUnitR F) (natInvertible _);
  bassoc G H K L F F' F'' := Build_Iso (functorCategory G L) _ _
    (functorAssoc F F' F'') (natInvertible _);
  bwhiskerLId G H K F F' := natTransEq
    (whiskerLNat F (idNatTrans F')) (idNatTrans (compFunctor F F'))
    (fun x => eq_refl);
  bwhiskerRId G H K F F' := natTransEq
    (whiskerRNat (idNatTrans F) F') (idNatTrans (compFunctor F F'))
    (fun x => F'.(fid) (F.(fobj) x));
  bwhiskerLComp G H K F F' F'' F''' α β := natTransEq
    (whiskerLNat F (compNatTrans α β))
    (compNatTrans (whiskerLNat F α) (whiskerLNat F β))
    (fun x => eq_refl);
  bwhiskerRComp G H K F F' F'' α β L := natTransEq
    (whiskerRNat (compNatTrans α β) L)
    (compNatTrans (whiskerRNat α L) (whiskerRNat β L))
    (fun x => L.(fcomp) (α.(ncomp) x) (β.(ncomp) x));
  binterchange G H K F F' L L' α β := natTransEq
    (compNatTrans (whiskerRNat α L) (whiskerLNat F' β))
    (compNatTrans (whiskerLNat F β) (whiskerRNat α L'))
    (fun x => β.(nnat) (α.(ncomp) x));
  bunitLNat G H F F' α := natTransEq
    (compNatTrans (whiskerLNat (idFunctor G) α) (functorUnitL F'))
    (compNatTrans (functorUnitL F) α)
    (fun x => functorUnitNaturality (α.(ncomp) x));
  bunitRNat G H F F' α := natTransEq
    (compNatTrans (whiskerRNat α (idFunctor H)) (functorUnitR F'))
    (compNatTrans (functorUnitR F) α)
    (fun x => functorUnitNaturality (α.(ncomp) x));
  bassocNatL G H K L F F' F'' F''' α := natTransEq
    (compNatTrans (whiskerLNat (compFunctor F F') α) (functorAssoc F F' F'''))
    (compNatTrans (functorAssoc F F' F'') (whiskerLNat F (whiskerLNat F' α)))
    (fun x => functorUnitNaturality (α.(ncomp) (F'.(fobj) (F.(fobj) x))));
  bassocNatR G H K L F F' α F'' F''' := natTransEq
    (compNatTrans (whiskerRNat (whiskerRNat α F'') F''') (functorAssoc F' F'' F'''))
    (compNatTrans (functorAssoc F F'' F''') (whiskerRNat α (compFunctor F'' F''')))
    (fun x => functorUnitNaturality (F'''.(fhom) (F''.(fhom) (α.(ncomp) x))));
  bassocNatM G H K L F F' F'' α F''' := natTransEq
    (compNatTrans (whiskerRNat (whiskerLNat F α) F''') (functorAssoc F F'' F'''))
    (compNatTrans (functorAssoc F F' F''') (whiskerLNat F (whiskerRNat α F''')))
    (fun x => functorUnitNaturality (F'''.(fhom) (α.(ncomp) (F.(fobj) x))));
  btriangle G H K F F' := natTransEq
    (compNatTrans (functorAssoc F (idFunctor H) F') (whiskerLNat F (functorUnitL F')))
    (whiskerRNat (functorUnitR F) F')
    (fun x => functorTriangle F' (F.(fobj) x));
  bpentagon G H K L M F F' F'' F''' := natTransEq
    (compNatTrans (functorAssoc (compFunctor F F') F'' F''')
      (functorAssoc F F' (compFunctor F'' F''')))
    (compNatTrans (whiskerRNat (functorAssoc F F' F'') F''')
      (compNatTrans (functorAssoc F (compFunctor F' F'') F''')
        (whiskerLNat F (functorAssoc F' F'' F'''))))
    (fun x => functorPentagon F''' (F''.(fobj) (F'.(fobj) (F.(fobj) x))));
|}.

Definition HSetGroupoidBicat: Bicategory :=
  fullBicategory GroupoidBicat (fun G: HSetGroupoid => G.(hsetGroupoid)).

(** Strict groupoid functors embed into the bicategory of groupoids.
    Equalities of functors act by their canonical natural transformations. *)
Local Lemma hsetFunctorPathComponent {G H: HSetGroupoid} {F K: Functor G H}
  (p: F = K) (x: G):
  (@idTo2 HSetGroupoidBicat G H F K p).(ncomp) x
  = idToHom (f_equal (fun L: Functor G H => L.(fobj) x) p).
Proof. now destruct p. Defined.

Definition hsetGroupoidDiscreteInclusion:
  BicategoryStructureMap (locallyDiscrete HSetGroupoidCat) HSetGroupoidBicat.
Proof.
  refine (@Build_BicategoryStructureMap
    (locallyDiscrete HSetGroupoidCat) HSetGroupoidBicat
    (fun G => G) (fun G H F => F) (fun G => eq_refl)
    (fun G H K F L => eq_refl)
    (fun G H F K p => @idTo2 HSetGroupoidBicat G H F K p)
    _ _ _ _ _ _ _).
  - now intros G H F.
  - intros G H F K L p q. destruct p, q.
    now apply eq_sym, (HSetGroupoidBicat.(BHom) G H).(cidl).
  - intros G H K F L M p. destruct p.
    now apply eq_sym, HSetGroupoidBicat.(bwhiskerLId).
  - intros G H K F L p M. destruct p.
    now apply eq_sym, HSetGroupoidBicat.(bwhiskerRId).
  - intros G H F. apply natTransEq; intro x.
    rewrite hsetFunctorPathComponent.
    now rewrite (@UIP H _ _ _ eq_refl).
  - intros G H F. apply natTransEq; intro x.
    rewrite hsetFunctorPathComponent.
    now rewrite (@UIP H _ _ _ eq_refl).
  - intros G H K L F R S. apply natTransEq; intro x.
    rewrite hsetFunctorPathComponent.
    now rewrite (@UIP L _ _ _ eq_refl).
Defined.
