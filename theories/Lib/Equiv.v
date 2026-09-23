(** Equivalences as bi-invertible maps: a function carrying a left and a
    right inverse. This is the standard well-behaved form; a quasi-inverse, one
    map serving as both, is what one actually supplies, and converts into it in
    one step. A canonical inverse and its two round trips are read off from
    there.

    The delicate construction is adjointification, needed wherever a proof must
    cancel transports along the round trips: the section is corrected until it
    agrees with the retraction under the map. The rest of the file is the usual
    kit for building and combining equivalences.

    Terminology follows the HoTT book (The Univalent Foundations Program,
    "Homotopy Type Theory: Univalent Foundations of Mathematics", 2013);
    numbered references below are to it. *)

Import Logic.EqNotations.

Set Warnings "-notation-overridden".
From Bonak Require Import SigT HSet Notation RewLemmas.

Set Primitive Projections.
Set Printing Projections.
Set Universe Polymorphism.

(** Bi-invertible maps (Definition 4.3.1) *)

Record IsEquiv {A B: Type} (f: A -> B) := {
  linv: B -> A;
  linvEq a: linv (f a) = a;
  rinv: B -> A;
  rinvEq b: f (rinv b) = b;
}.

Arguments linv {A B f} _ _.
Arguments linvEq {A B f} _ _.
Arguments rinv {A B f} _ _.
Arguments rinvEq {A B f} _ _.

Record Equiv (A B: Type) := {
  eqvFun: A -> B;
  eqvIsEquiv: IsEquiv eqvFun;
}.

Arguments eqvFun {A B} _ _.
Arguments eqvIsEquiv {A B} _.

Coercion eqvFun: Equiv >-> Funclass.

(** Build an equivalence from a quasi-inverse (Definition 2.4.6). *)

Definition qinvEquiv {A B} (f: A -> B) (g: B -> A)
  (Hgf: forall a, g (f a) = a) (Hfg: forall b, f (g b) = b): Equiv A B := {|
  eqvFun := f;
  eqvIsEquiv := {| linv := g; linvEq := Hgf; rinv := g; rinvEq := Hfg |};
|}.

(** The canonical inverse: the left inverse, which is also a right inverse
    up to [secEq]. *)

Definition invEq {A B} (e: Equiv A B): B -> A := e.(eqvIsEquiv).(linv).

Definition retEq {A B} (e: Equiv A B) (a: A): invEq e (e a) = a :=
  e.(eqvIsEquiv).(linvEq) a.

Definition linvRinvEq {A B} (e: Equiv A B) (b: B):
  invEq e b = e.(eqvIsEquiv).(rinv) b :=
  eq_sym (f_equal (invEq e) (e.(eqvIsEquiv).(rinvEq) b))
    • e.(eqvIsEquiv).(linvEq) (e.(eqvIsEquiv).(rinv) b).

Definition secEq {A B} (e: Equiv A B) (b: B): e (invEq e b) = b :=
  f_equal e.(eqvFun) (linvRinvEq e b) • e.(eqvIsEquiv).(rinvEq) b.

(** Identity, composition, inverse *)

Definition idEquiv {A}: Equiv A A :=
  qinvEquiv id id (fun _ => eq_refl) (fun _ => eq_refl).

Definition compEquiv {A B C} (e: Equiv A B) (e': Equiv B C): Equiv A C := {|
  eqvFun := fun a => e' (e a);
  eqvIsEquiv := {|
    linv := fun c => e.(eqvIsEquiv).(linv) (e'.(eqvIsEquiv).(linv) c);
    linvEq := fun a =>
      f_equal e.(eqvIsEquiv).(linv) (e'.(eqvIsEquiv).(linvEq) (e a))
        • e.(eqvIsEquiv).(linvEq) a;
    rinv := fun c => e.(eqvIsEquiv).(rinv) (e'.(eqvIsEquiv).(rinv) c);
    rinvEq := fun c =>
      f_equal e'.(eqvFun) (e.(eqvIsEquiv).(rinvEq) (e'.(eqvIsEquiv).(rinv) c))
        • e'.(eqvIsEquiv).(rinvEq) c;
  |};
|}.

Definition symEquiv {A B} (e: Equiv A B): Equiv B A :=
  qinvEquiv (invEq e) e.(eqvFun) (secEq e) (retEq e).

(** Adjointification

    [IsHAE f] is Definition 4.2.1's [ishae f] written as a record, field for
    field: the inverse [haeInv], the two homotopies [haeRet] and [haeSec] —
    the book's η and ε — and the coherence [haeAdj], its τ. [haeAdj] is
    stated at [f]; Lemma 4.2.2 derives the corresponding coherence at
    [haeInv]. This asymmetry is what *half* adjoint refers to. *)

Record IsHAE {A B: Type} (f: A -> B) := {
  haeInv: B -> A;
  haeRet a: haeInv (f a) = a;
  haeSec b: f (haeInv b) = b;
  haeAdj a: f_equal f (haeRet a) = haeSec (f a);
}.

Arguments haeInv {A B f} _ _.
Arguments haeRet {A B f} _ _.
Arguments haeSec {A B f} _ _.
Arguments haeAdj {A B f} _ _.

(** A quasi-inverse adjusts to a half adjoint equivalence (Theorem 4.2.3):
    keep the retraction, correct the section. *)

Lemma qinvAdj {A B} (u: A -> B) (v: B -> A)
  (Hvu: forall a, v (u a) = a) (Huv: forall b, u (v b) = b) (a: A):
  f_equal u (Hvu a)
  = eq_sym (Huv (u (v (u a)))) • (f_equal u (Hvu (v (u a))) • Huv (u a)).
Proof.
  apply eq_trans_shift_l.
  rewrite (eq_trans_nat_id Huv (f_equal u (Hvu a))), f_equal_compose.
  rewrite <- (eq_id_comm_r (fun a => v (u a)) Hvu a).
  now exact (f_equal (fun p => p • Huv (u a))
    (eq_sym (f_equal_compose (fun a => v (u a)) u (Hvu a)))).
Qed.

Definition toIsHAE {A B} (e: Equiv A B): IsHAE e.(eqvFun) := {|
  haeInv := invEq e;
  haeRet := retEq e;
  haeSec := fun b => eq_sym (secEq e (e (invEq e b)))
    • (f_equal e.(eqvFun) (retEq e (invEq e b)) • secEq e b);
  haeAdj := qinvAdj e.(eqvFun) (invEq e) (retEq e) (secEq e);
|}.

(** Lifting through Σ *)

Definition sigTEquivSnd {A: Type} {B B': A -> Type}
  (eB: forall a, Equiv (B a) (B' a)):
  Equiv {a: A &T B a} {a: A &T B' a} :=
  qinvEquiv
    (fun x => (x.1; eB x.1 x.2))
    (fun x => (x.1; invEq (eB x.1) x.2))
    (fun x => (= eq_refl; retEq (eB x.1) x.2))
    (fun x => (= eq_refl; secEq (eB x.1) x.2)).

Lemma sigTEquivFstRet {A A': Type} {B: A' -> Type} (eA: Equiv A A')
  (a: A) (b: B (eA a)):
  rew [fun a => B (eA a)] ((toIsHAE eA).(haeRet) a) in
    (rew <- [B] ((toIsHAE eA).(haeSec) (eA a)) in b) = b.
Proof.
  rewrite rew_map with (P := B) (f := eA.(eqvFun)).
  rewrite ((toIsHAE eA).(haeAdj) a).
  now apply rew_opp_r.
Qed.

Definition sigTEquivFst {A A': Type} {B: A' -> Type} (eA: Equiv A A'):
  Equiv {a: A &T B (eA a)} {a': A' &T B a'} :=
  qinvEquiv (A := {a: A &T B (eA a)}) (B := {a': A' &T B a'})
    (fun x => (eA x.1; x.2))
    (fun x => ((toIsHAE eA).(haeInv) x.1;
      rew <- [B] ((toIsHAE eA).(haeSec) x.1) in x.2))
    (fun x => (= (toIsHAE eA).(haeRet) x.1; sigTEquivFstRet eA x.1 x.2))
    (fun x => (= (toIsHAE eA).(haeSec) x.1;
      rew_opp_r B ((toIsHAE eA).(haeSec) x.1) x.2)).

Definition sigTEquiv {A A': Type} {B: A -> Type} {B': A' -> Type}
  (eA: Equiv A A') (eB: forall a, Equiv (B a) (B' (eA a))):
  Equiv {a: A &T B a} {a': A' &T B' a'} :=
  compEquiv (sigTEquivSnd eB) (sigTEquivFst eA).

(** Transport as an equivalence *)

Definition rewEquiv {A: Type} (P: A -> Type) {x y: A} (e: x = y):
  Equiv (P x) (P y) :=
  qinvEquiv (fun a => rew [P] e in a) (fun b => rew [P] (eq_sym e) in b)
    (fun a => rew_sym_cancel e a) (fun b => rew_sym_cancel_r e b).

(** The equivalence-based injectivity of a map on paths *)

Definition eqvInj {A B: Type} (e: Equiv A B) {x y: A} (q: e x = e y):
  x = y :=
  eq_sym (retEq e x) • (f_equal (invEq e) q • retEq e y).

(** All path types in HSets are propositions, so an equivalence between
    them needs only the two maps *)

Definition pathEquiv {A: HSet} {x y x' y': A}
  (f: x = y -> x' = y') (g: x' = y' -> x = y):
  Equiv (x = y) (x' = y') :=
  qinvEquiv f g (fun p => A.(UIP)) (fun q => A.(UIP)).

Definition pathEquiv2 {A B: HSet} {x y: A} {x' y': B}
  (f: x = y -> x' = y') (g: x' = y' -> x = y):
  Equiv (x = y) (x' = y') :=
  qinvEquiv f g (fun p => A.(UIP)) (fun q => B.(UIP)).

(** The based-pair space over a fixed point of an HSet contracts onto the
    fibre *)

Definition baseContract {FrB: HSet} (E: FrB -> HSet) (D: FrB):
  Equiv {t: {D0: FrB &T E D0} &T D = t.1} (E D).
Proof.
  unshelve refine (qinvEquiv
    (fun x => rew [fun D0 => E D0] (eq_sym x.2) in x.1.2)
    (fun c => ((D; c); eq_refl)) _ _).
  - intros ((D0, c0), e). cbn in e. now destruct e.
  - intros c. now reflexivity.
Defined.

(** The contraction of a candidate total space: pairs of a point [D] of an
    HSet with a cell whose canonical image is identified with [D] project
    equivalently onto the cells (the fibres are singletons; [UIP] of the
    HSet collapses the identification component). *)

Lemma fillerContract {A B: HSet} (F: A -> B)
  (x: {D: B &T {d': A &T D = F d'}}):
  ((F x.2.1; (x.2.1; eq_refl)): {D: B &T {d': A &T D = F d'}}) = x.
Proof.
  destruct x as (D, (d', e)). cbn.
  refine (eq_existT_curried (eq_sym e) _).
  etransitivity.
  { now exact (rew_sigT_fst_const (eq_sym e) d' eq_refl). }
  now exact (f_equal (fun h => (d'; h)) (B.(UIP))).
Qed.

Definition fillerEquiv {A B: HSet} (F: A -> B):
  Equiv {D: B &T {d': A &T D = F d'}} A :=
  qinvEquiv (fun x => x.2.1) (fun a => (F a; (a; eq_refl)))
    (fillerContract F) (fun a => eq_refl).

(** Equivalences between path types, without truncation

    The combinators below are the truncation-free counterparts of the [HSet]
    ones above: the same equivalences, with round trips proved rather than
    read off from [UIP]. They are stated over arbitrary types, hence apply at
    every truncation level, and are transparent, so the equivalences they
    build still compute. *)

(** Composing with a fixed path.

    Post-composition with [e] is inverted by post-composition with
    [eq_sym e]; the two cancellation lemmas are the computation rules of the
    resulting equivalence. *)

Lemma eqTransCancelR {A: Type} {x y z: A} (e: y = z) (q: x = y):
  (q • e) • eq_sym e = q.
Proof.
  now destruct e.
Defined.

Lemma eqTransCancelL {A: Type} {x y z: A} (e: y = z) (q: x = z):
  (q • eq_sym e) • e = q.
Proof.
  now destruct e.
Defined.

Definition eqTransEquiv {A: Type} {x y z: A} (e: y = z):
  Equiv (x = y) (x = z) :=
  qinvEquiv (fun q => q • e) (fun q => q • eq_sym e)
    (eqTransCancelR e) (eqTransCancelL e).

(** Composing with the image of a path under a map. Both directions are
    kept in [f_equal] form: [f_equal f (eq_sym r)] and [eq_sym (f_equal f r)]
    agree only propositionally, so which of the two a combinator produces
    decides whether it matches a given call site definitionally. *)

Lemma eqTransMapCancelR {A B: Type} (f: A -> B) {u: B} {a b: A} (r: a = b)
  (q: u = f b): (q • f_equal f (eq_sym r)) • f_equal f r = q.
Proof.
  now destruct r.
Defined.

Lemma eqTransMapCancelL {A B: Type} (f: A -> B) {u: B} {a b: A} (r: a = b)
  (q: u = f a): (q • f_equal f r) • f_equal f (eq_sym r) = q.
Proof.
  now destruct r.
Defined.

Definition eqTransMapEquiv {A B: Type} (f: A -> B) {u: B} {a b: A} (r: a = b):
  Equiv (u = f b) (u = f a) :=
  qinvEquiv (fun q => q • f_equal f (eq_sym r)) (fun q => q • f_equal f r)
    (eqTransMapCancelR f r) (eqTransMapCancelL f r).

(** Injectivity on paths as an equivalence

    [f_equal] of an equivalence is an equivalence, inverted by [eqvInj]. The
    round trip at the source is naturality of the retraction; the one at the
    target consumes the half adjoint coherence, so it is stated at [IsHAE]
    and specialised through [toIsHAE]. *)

Lemma haeInjSec {A B: Type} {f: A -> B} (H: IsHAE f) {x y: A} (q: f x = f y):
  f_equal f (eq_sym (H.(haeRet) x) • (f_equal H.(haeInv) q • H.(haeRet) y))
  = q.
Proof.
  rewrite 2 eq_trans_map_distr, <- eq_sym_map_distr.
  rewrite 2 H.(haeAdj), f_equal_compose.
  rewrite <- (eq_trans_nat_id H.(haeSec) q).
  now apply eq_trans_sym_cancel_l.
Defined.

Lemma fEqualRet {A B: Type} (e: Equiv A B) {x y: A} (p: x = y):
  eqvInj e (f_equal e.(eqvFun) p) = p.
Proof.
  unfold eqvInj.
  rewrite f_equal_compose.
  rewrite <- (eq_trans_nat_id (retEq e) p).
  now apply eq_trans_sym_cancel_l.
Defined.

Lemma fEqualSec {A B: Type} (e: Equiv A B) {x y: A} (q: e x = e y):
  f_equal e.(eqvFun) (eqvInj e q) = q.
Proof.
  now exact (haeInjSec (toIsHAE e) q).
Defined.

Definition eqvInjEquiv {A B: Type} (e: Equiv A B) {x y: A}:
  Equiv (e x = e y) (x = y) :=
  qinvEquiv (fun q: e x = e y => eqvInj e q) (fun p => f_equal e.(eqvFun) p)
    (fEqualSec e) (fEqualRet e).

(** Path induction with the right endpoint fixed

    [eq] is an inductive family in its right argument, so the eliminator
    generalises that argument. A path whose right endpoint must stay fixed —
    because it is a compound term the motive mentions elsewhere — is
    eliminated by generalising the left endpoint instead. *)

Lemma eqIndL {A: Type} {c: A} (P: forall D: A, D = c -> Type) (p: P c eq_refl)
  {D: A} (e: D = c): P D e.
Proof.
  now destruct e.
Defined.

(** The total space of the graph of [F] projects equivalently onto the
    domain: for each [d'] the based path space [{D &T D = F d'}] is
    contractible, so the pair of a point with an identification of it with a
    canonical image carries no information beyond that point. *)

Lemma graphContract {A B: Type} (F: A -> B)
  (x: {D: B &T {d': A &T D = F d'}}):
  ((F x.2.1; (x.2.1; eq_refl)): {D: B &T {d': A &T D = F d'}}) = x.
Proof.
  destruct x as (D, (d', e)); cbn.
  now exact (eqIndL (fun D0 e0 =>
    ((F d'; (d'; eq_refl)): {D1: B &T {d: A &T D1 = F d}}) = (D0; (d'; e0)))
    eq_refl e).
Defined.

Definition graphEquiv {A B: Type} (F: A -> B):
  Equiv {D: B &T {d': A &T D = F d'}} A :=
  qinvEquiv (fun x => x.2.1) (fun a => (F a; (a; eq_refl)))
    (graphContract F) (fun a => eq_refl).

(** The based-pair space over a fixed point contracts onto the fibre. *)

Definition basePairEquiv {A: Type} (E: A -> Type) (D: A):
  Equiv {t: {D0: A &T E D0} &T D = t.1} (E D).
Proof.
  unshelve refine (qinvEquiv
    (fun x => rew [E] (eq_sym x.2) in x.1.2)
    (fun c => ((D; c); eq_refl)) _ _).
  - intros ((D0, c0), e); cbn in e. now destruct e.
  - intros c. now reflexivity.
Defined.
