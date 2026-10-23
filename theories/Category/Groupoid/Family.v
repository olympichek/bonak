(** Displayed groupoids with h-set object fibers and h-set arrows.
    Each arrow records its image in the base; no lift is required. *)
Set Warnings "-notation-overridden".
From Bonak.Category.Groupoid Require Export SetBased.
From Bonak.Lib Require Import HSet SigT Notation.
Set Primitive Projections.
Set Printing Projections.
Set Universe Polymorphism.

Record Family {G: HSetGroupoid} := {
  dobj: G -> HSet;
  dhom: forall {x y}, dobj x -> dobj y -> HSet;
  dbase: forall {x y} {a: dobj x} {b: dobj y}, dhom a b -> G.(CHom) x y;
  did: forall {x} (a: dobj x), dhom a a;
  dcomp: forall {x y z} {a: dobj x} {b: dobj y} {c: dobj z},
    dhom a b -> dhom b c -> dhom a c;
  dinv: forall {x y} {a: dobj x} {b: dobj y}, dhom a b -> dhom b a;
  didl: forall {x y} {a: dobj x} {b: dobj y} (f: dhom a b), dcomp (did a) f = f;
  didr: forall {x y} {a: dobj x} {b: dobj y} (f: dhom a b), dcomp f (did b) = f;
  dassoc: forall {w x y z} {a: dobj w} {b: dobj x} {c: dobj y} {d: dobj z}
    (f: dhom a b) (g: dhom b c) (h: dhom c d),
    dcomp (dcomp f g) h = dcomp f (dcomp g h);
  dinvL: forall {x y} {a: dobj x} {b: dobj y} (f: dhom a b), dcomp (dinv f) f = did b;
  dinvR: forall {x y} {a: dobj x} {b: dobj y} (f: dhom a b), dcomp f (dinv f) = did a;
  dbaseId: forall {x} (a: dobj x), dbase (did a) = cid x;
  dbaseComp: forall {x y z} {a: dobj x} {b: dobj y} {c: dobj z}
    (f: dhom a b) (g: dhom b c), dbase (dcomp f g) = dbase f ⨟ dbase g;
  dbaseInv: forall {x y} {a: dobj x} {b: dobj y} (f: dhom a b),
    dbase (dinv f) = ginv (dbase f);
}.
Arguments Family G : clear implicits.

Definition total {G: HSetGroupoid} (E: Family G): HSetGroupoid := {|
  hsetGroupoid := {| gcat := {|
    CObj := {x: G &T E.(dobj) x};
    CHom a b := E.(dhom) a.2 b.2;
    cid a := E.(did) a.2;
    ccomp a b c := E.(dcomp);
    cidl a b := E.(didl);
    cidr a b := E.(didr);
    cassoc a b c d := E.(dassoc) |};
    groupoidInvertibility a b f :=
      @Build_IsInvertible _ a b f (E.(dinv) f) (E.(dinvR) f) (E.(dinvL) f) |};
  hsetGroupoidUIP := @sigT_UIP G E.(dobj);
|}.

Definition proj {G: HSetGroupoid} (E: Family G): Functor (total E) G :=
  Build_Functor (total E) G (fun a => a.1) (fun a b f => E.(dbase) f)
    (fun a => E.(dbaseId) a.2) (fun a b c f g => E.(dbaseComp) f g).

Definition Over {G: HSetGroupoid} (E: Family G) {x y} (f: G.(CHom) x y)
  (a: E.(dobj) x) (b: E.(dobj) y): HSet :=
  {h: E.(dhom) a b & hEq (E.(dbase) h) f}.

Definition reindex {G H: HSetGroupoid} (E: Family H) (F: Functor G H): Family G.
Proof.
  unshelve refine {| dobj x := E.(dobj) (F.(fobj) x);
    dhom x y a b := {f: G.(CHom) x y & Over E (F.(fhom) f) a b};
    dbase x y a b f := f.1;
    did x a := (cid x; (E.(did) a; _));
    dcomp x y z a b c f g := (f.1 ⨟ g.1; (E.(dcomp) f.2.1 g.2.1; _));
    dinv x y a b f := (ginv f.1; (E.(dinv) f.2.1; _)) |}.
  - now rewrite E.(dbaseId), F.(fid).
  - now rewrite E.(dbaseComp), f.2.2, g.2.2, F.(fcomp).
  - now rewrite E.(dbaseInv), f.2.2, functorInv.
  - intros x y a b f. apply (eq_sigT_nondep_hprop (fun _ _ _ _ => UIP _)); cbn.
    + now apply G.(cidl).
    + now apply E.(didl).
  - intros x y a b f. apply (eq_sigT_nondep_hprop (fun _ _ _ _ => UIP _)); cbn.
    + now apply G.(cidr).
    + now apply E.(didr).
  - intros w x y z a b c d f g h. apply (eq_sigT_nondep_hprop (fun _ _ _ _ => UIP _)); cbn.
    + now apply G.(cassoc).
    + now apply E.(dassoc).
  - intros x y a b f. apply (eq_sigT_nondep_hprop (fun _ _ _ _ => UIP _)); cbn.
    + now apply ginvL.
    + now apply E.(dinvL).
  - intros x y a b f. apply (eq_sigT_nondep_hprop (fun _ _ _ _ => UIP _)); cbn.
    + now apply ginvR.
    + now apply E.(dinvR).
  - now intros.
  - now intros.
  - now intros.
Defined.

Definition sigma {G: HSetGroupoid} (E: Family G) (P: Family (total E)): Family G.
Proof.
  unshelve refine {| dobj x := {a: E.(dobj) x & P.(dobj) (x; a)};
    dhom x y a b := P.(dhom) a.2 b.2;
    dbase x y a b h := E.(dbase) (P.(dbase) h);
    did x a := P.(did) a.2;
    dcomp x y z a b c := P.(dcomp);
    dinv x y a b := P.(dinv);
    didl x y a b := P.(didl); didr x y a b := P.(didr);
    dassoc w x y z a b c d := P.(dassoc);
    dinvL x y a b := P.(dinvL); dinvR x y a b := P.(dinvR) |}.
  - intros x a. rewrite P.(dbaseId). now apply E.(dbaseId).
  - intros x y z a b c f g. rewrite P.(dbaseComp). now apply E.(dbaseComp).
  - intros x y a b f. rewrite P.(dbaseInv). now apply E.(dbaseInv).
Defined.

Definition const (G H: HSetGroupoid): Family G.
Proof.
  unshelve refine {| dobj _ := H;
    dhom x y a b := prodSet (G.(CHom) x y) (H.(CHom) a b);
    dbase x y a b := fst; did x a := (cid x, cid a);
    dcomp x y z a b c f g := (fst f ⨟ fst g, snd f ⨟ snd g);
    dinv x y a b f := (ginv (fst f), ginv (snd f)) |}.
  - intros. cbn. now rewrite 2 cidl; destruct f.
  - intros. cbn. now rewrite 2 cidr; destruct f.
  - intros. cbn. now rewrite 2 cassoc.
  - intros. cbn. now rewrite 2 ginvL.
  - intros. cbn. now rewrite 2 ginvR.
  - now intros.
  - now intros.
  - now intros.
Defined.

(** Reassociation of total dependent sums. *)
Definition totalAssoc {G: HSetGroupoid} (E: Family G) (P: Family (total E)):
  Functor (total (sigma E P)) (total P) :=
  Build_Functor (total (sigma E P)) (total P) (fun a => ((a.1; a.2.1); a.2.2))
    (fun a b f => f) (fun a => eq_refl) (fun a b c f g => eq_refl).

Definition totalUnassoc {G: HSetGroupoid} (E: Family G) (P: Family (total E)):
  Functor (total P) (total (sigma E P)) :=
  Build_Functor (total P) (total (sigma E P)) (fun a => (a.1.1; (a.1.2; a.2)))
    (fun a b f => f) (fun a => eq_refl) (fun a b c f g => eq_refl).

Declare Scope displayed_gpd_scope.
Delimit Scope displayed_gpd_scope with dgpd.
Notation "'∫ᵍ' E" := (total E) (at level 20): displayed_gpd_scope.
Notation "E '[ᵍ' F ']'" := (reindex E F) (at level 1): displayed_gpd_scope.
Infix "Σᵍ" := sigma (at level 35, right associativity): displayed_gpd_scope.

(** [Gpd] denotes h-set-based groupoids. The family arrow denotes displayed
    groupoid structure over the whole base, and the total-groupoid notation
    makes that base explicit. *)
Notation "'Gpd'" := HSetGroupoid: displayed_gpd_scope.
Notation "'unitᵍ'" := unitGroupoid: displayed_gpd_scope.
Notation "'!ᵍ'" := (terminalFunctor _): displayed_gpd_scope.
Local Set Warnings "-postfix-notation-not-level-1".
Notation "G '⇝' 'Gpd'" := (Family G)
  (at level 99, right associativity): displayed_gpd_scope.
Notation "{ G &ᵍ E }" := (@total G E)
  (G at level 99, E at level 200,
   format "{ '[ ' G  &ᵍ  '/' E ']' }"): displayed_gpd_scope.
