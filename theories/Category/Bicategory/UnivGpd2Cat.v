(** The bicategory of univalent groupoids, functors, and natural transformations. *)
Set Warnings "-notation-overridden".
From Bonak.Lib Require Import HSet Notation RewLemmas.
From Bonak.Category Require Import Category CategoryEq Groupoid.
From Bonak.Category.Bicategory Require Export Bicategory.
Set Primitive Projections.
Set Printing Projections.
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

Definition UnivGpd2Cat: Bicategory := {|
  BObj := UnivalentGroupoid;
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

Definition univGpdLocallyGroupoid: IsLocallyGroupoid UnivGpd2Cat :=
  fun G H F F' α => natInvertible α.

(** Transport along functor equalities is determined by their object parts. *)
Lemma ncompHom2Rew {G H: UnivalentGroupoid} {F F' K K': Functor G H}
  (p: F = F') (q: K = K') (α: NatTrans F K) (x: G.(CObj)):
  (@hom2Rew UnivGpd2Cat G H F F' K K' p q α).(ncomp) x
  = rew [fun o => H.(CHom) (F'.(fobj) x) (o x)] (f_equal fobj q) in
    rew [fun o => H.(CHom) (o x) (K.(fobj) x)] (f_equal fobj p) in
    α.(ncomp) x.
Proof. exact (ncompRew p q α x). Qed.

Lemma ncompHom2RewOn {G H: UnivalentGroupoid} {Fo Ko: G.(CObj) -> H.(CObj)}
  (zF wF: FunctorOn Fo) (zK wK: FunctorOn Ko)
  (p: ofFunctorOn zF = ofFunctorOn wF) (q: ofFunctorOn zK = ofFunctorOn wK)
  (hp: f_equal fobj p = eq_refl) (hq: f_equal fobj q = eq_refl)
  (α: NatTrans (ofFunctorOn zF) (ofFunctorOn zK)) (x: G.(CObj)):
  (@hom2Rew UnivGpd2Cat G H _ _ _ _ p q α).(ncomp) x = α.(ncomp) x.
Proof. exact (ncompRewOn zF wF zK wK p q hp hq α x). Qed.
