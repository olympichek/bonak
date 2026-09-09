(** Associativity and unit laws for the word compositor.

    [WordAction.v] constructs naturality [applyWNat] and the compositor
    [applyWComp] from face maps satisfying [CohOf]. The hexagon [Coh2Of]
    makes these homotopies coherent: [applyWNatTwo] compares two families
    of top faces along a word, [applyWNatComp] makes naturality compatible
    with composition, and [applyWAssoc] proves associativity. The unit laws
    [applyWCompIdL] and [applyWCompIdR] compare composition with identity words.

    Each inductive step is proved over abstract types, functions and paths,
    then specialized to the word action. This leaves endpoints free for
    path induction; the concrete endpoints are function applications and
    cannot be generalized independently. *)

Set Warnings "-notation-overridden".
From Bonak Require Import HSet Notation LeSProp RewLemmas.

From Bonak.Presheaf Require Import νSemiShape WordAction.

Set Primitive Projections.
Set Printing Projections.

(** The abstract shape of the data

    [applyWNat] runs on a family [T] of maps lowering the level by one that
    commutes with every face of the structure. [Exch] names that hypothesis,
    and [exchShift] transports it to the shifted structure, where [T] is
    re-indexed but stays the same family of maps. *)

Definition Exch {A: HSet} (R: FaceStr A)
  (V: forall k (ε: A), R.(S0) (S k) -> R.(S0) k): Type :=
  forall k q (Hq: q <= k) (ε ω: A) (X: R.(S0) (S (S k))),
    V k ε (R.(SFace) (S k) q (↑ Hq) ω X) = R.(SFace) k q Hq ω (V (S k) ε X).

Definition exchShift {A: HSet} {R: FaceStr A} {V} (H: Exch R V):
  Exch (shiftStr R) (fun k => V (S k)) :=
  fun k q Hq ε ω X => H (S k) q (↑ Hq) ε ω X.

(** [Slide T U Ub] is the exchange law between two such families, [T] and the
    pair formed by [U] and its shifted companion [Ub]. The pair is needed
    because [U] at level [k] and [U] at level [S k] are related by [T] through
    two different maps. *)

Definition Slide {A: HSet} {R: FaceStr A}
  (T U: forall k (ε: A), R.(S0) (S k) -> R.(S0) k)
  (Ub: forall k (ε: A), (shiftStr R).(S0) (S k) -> (shiftStr R).(S0) k): Type :=
  forall k (ε a: A) (X: R.(S0) (S (S k))),
    T k ε (Ub k a X) = U k a (T (S k) ε X).

Definition slideShift {A: HSet} {R: FaceStr A} {T U Ub}
  (H: Slide T U Ub): Slide (R := shiftStr R) (fun k => T (S k))
                       (fun k => U (S k)) (fun k => Ub (S k)) :=
  fun k ε a X => H (S k) ε a X.

(** The instance of [Slide] where [U] is the top face of [R]: it is the
    exchange law [Exch] read at the top index. *)

Definition topSlide {A: HSet} {Q: FaceStr A}
  {T: forall k (ε: A), Q.(S0) (S k) -> Q.(S0) k} (HT: Exch Q T):
  Slide T (sTop Q) (sTop (shiftStr Q)) :=
  fun k ε a X => HT k k leR_refl ε a X.

(** The hexagon [applyWNatTwo] runs on: the six exchange 2-cells between [T],
    the pair [U]/[Ub] and one face of [R] paste to the identity. *)

Definition Hex {A: HSet} {R: FaceStr A} {T U Ub}
  (HT: Exch R T) (HU: Exch R U) (HUb: Exch (shiftStr R) Ub)
  (HTU: Slide T U Ub): Type :=
  forall k q (Hq: q <= k) (ε a b: A) (x: R.(S0) (S (S (S k)))),
    f_equal (U k a) (HT (S k) q (↑ Hq) ε b x)
    • (HU k q Hq a b (T (S (S k)) ε x)
       • (f_equal (R.(SFace) k q Hq b) (eq_sym (HTU (S k) ε a x))
          • (eq_sym (HT k q Hq ε b (Ub (S k) a x))
             • eq_sym (f_equal (T k ε) (HUb k q Hq a b x)))))
    = eq_sym (HTU k ε a (R.(SFace) (S (S k)) q (↑ (↑ Hq)) b x)).

Definition hexShift {A: HSet} {R: FaceStr A} {T U Ub}
  {HT: Exch R T} {HU: Exch R U} {HUb: Exch (shiftStr R) Ub}
  {HTU: Slide T U Ub} (H: Hex HT HU HUb HTU):
  Hex (R := shiftStr R) (exchShift HT) (exchShift HU) (exchShift HUb)
    (slideShift HTU) :=
  fun k q Hq ε a b x => H (S k) q (↑ Hq) ε a b x.

(** The shift-stable hexagon for an abstract family of top faces

    [applyWNatComp] recurses through [wkeep] into the shifted structure, where
    the family of top faces becomes [fun k => T (S k)] while [sTop] becomes the
    top face of the shifted structure: the two are different maps, so the
    hexagon [Hex] instantiated at [sTop] does not reproduce itself along the
    recursion. [ExchHex] is the hexagon with the index of the [sTop] leg left
    free, subject only to [q <= p <= k]. Raising [k] by one leaves that
    constraint satisfied, which is what makes [exchHexShift] typecheck, and
    taking [p] to be [k] recovers the instance [applyWNatTwo] consumes. *)

Definition ExchHex {A: HSet} {Q: FaceStr A} (HQ: CohOf Q)
  {T: forall k (ε: A), Q.(S0) (S k) -> Q.(S0) k} (HT: Exch Q T): Type :=
  forall k p (Hp: p <= k) q (Hq: q <= p) (ε a b: A) (x: Q.(S0) (S (S (S k)))),
    f_equal (Q.(SFace) k p Hp a) (HT (S k) q (↑ (Hq ↕ Hp)) ε b x)
    • (HQ k p Hp q Hq a b (T (S (S k)) ε x)
       • (f_equal (Q.(SFace) k q (Hq ↕ Hp) b)
            (eq_sym (HT (S k) (S p) (⇑ Hp) ε a x))
          • (eq_sym (HT k q (Hq ↕ Hp) ε b
                       (Q.(SFace) (S (S k)) (S p) (↑ (⇑ Hp)) a x))
             • eq_sym (f_equal (T k ε) (HQ (S k) p (↑ Hp) q Hq a b x)))))
    = eq_sym (HT k p Hp ε a (Q.(SFace) (S (S k)) q (↑ (↑ (Hq ↕ Hp))) b x)).

Definition exchHexShift {A: HSet} {Q: FaceStr A} {HQ: CohOf Q} {T}
  {HT: Exch Q T} (H: ExchHex HQ HT):
  ExchHex (cohShift HQ) (exchShift HT) :=
  fun k p Hp q Hq ε a b x => H (S k) p (↑ Hp) q Hq ε a b x.

Definition topHex {A: HSet} {Q: FaceStr A} {HQ: CohOf Q} {T}
  {HT: Exch Q T} (H: ExchHex HQ HT):
  Hex HT (topCoh HQ) (topCoh (cohShift HQ)) (topSlide HT) :=
  fun k q Hq ε a b x => H k k leR_refl q Hq ε a b x.

(** [Coh2Of] read with the outermost of the three faces taken to be the top
    one is [ExchHex] for the family of top faces. *)

Definition topExchHex {A: HSet} {Q: FaceStr A} {HQ: CohOf Q}
  (HQ2: Coh2Of HQ): ExchHex HQ (topCoh HQ).
Proof.
  intros k p Hp q Hq ε a b x.
  rewrite <- (eq_sym_map_distr (Q.(SFace) k q (Hq ↕ Hp) b)
    (topCoh HQ (S k) (S p) (⇑ Hp) ε a x)).
  now exact (hexRotate _ _ _ _ _ _ (HQ2 k k leR_refl p Hp q Hq ε a b x)).
Defined.

(** Two families of top faces along a word

    The step lemma for a [wskip]. Once the three paths [A2], [A4] and [A5]
    that relate the arguments of the two naturality homotopies are killed by
    path induction, the hexagon [hx] collapses to the identification of [B]
    with the composite [A1 • eq_sym A3], and the goal is the induction
    hypothesis reassociated. *)

Lemma natTwoSkipStep {M SM N SN: Type}
  (AW: M -> N) (AWs: SM -> SN)
  (Tm Um sR: SM -> M) (Tn Un: SN -> N)
  (p1 p2 q1 q2 r1 r2: SM) (d1 d2: SN)
  (A1: Um p1 = sR p2) (A2: q2 = p2) (A3: Tm q1 = sR q2)
  (A4: r2 = q1) (A5: r1 = p1)
  (B: Tm r2 = Um r1) (C: Tn d1 = Un d2)
  (NU: forall z, AW (Um z) = Un (AWs z))
  (NT: forall z, AW (Tm z) = Tn (AWs z))
  (D: AWs r2 = d1) (E: AWs r1 = d2)
  (hx: f_equal Um A5 • (A1 • (f_equal sR (eq_sym A2)
        • (eq_sym A3 • eq_sym (f_equal Tm A4)))) = eq_sym B)
  (ih: eq_sym (NU r1) • (f_equal AW (eq_sym B) • (NT r2 • f_equal Tn D))
       = f_equal Un E • eq_sym C):
  eq_sym (f_equal AW (eq_sym A1) • NU p1)
  • (f_equal (fun z => AW (sR z)) (eq_sym A2)
     • (f_equal AW (eq_sym A3) • NT q1
        • f_equal Tn (f_equal AWs (eq_sym A4) • D)))
  = f_equal Un (f_equal AWs (eq_sym A5) • E) • eq_sym C.
Proof.
  destruct A5, A2, A4. simpl in hx |- *.
  rewrite !eq_trans_refl_l in hx |- *.
  rewrite <- hx in ih.
  rewrite eq_trans_map_distr in ih.
  rewrite eq_trans_sym_distr, eq_sym_map_distr, eq_sym_involutive.
  rewrite <- !eq_trans_assoc in ih |- *.
  rewrite (eq_trans_refl_l E).
  rewrite <- (eq_trans_assoc (f_equal AW (eq_sym A3)) (NT r2) (f_equal Tn D)).
  now exact ih.
Defined.

(** Sliding [T] past [U] commutes with the action of a word: the naturality
    homotopies of [T] and of the pair [U]/[Ub] paste to the naturality
    homotopy of [T] on the shifted structure, at the cost of one hexagon per
    letter deleted by the word. *)

Lemma applyWNatTwo {A: HSet} (m: nat): forall n (w: Word A n m) (R: FaceStr A)
  (T U: forall k (ε: A), R.(S0) (S k) -> R.(S0) k)
  (Ub: forall k (ε: A), (shiftStr R).(S0) (S k) -> (shiftStr R).(S0) k)
  (HT: Exch R T) (HU: Exch R U) (HUb: Exch (shiftStr R) Ub)
  (HTU: Slide T U Ub) (HX: Hex HT HU HUb HTU)
  (ε a: A) (x: R.(S0) (S (S m))),
  eq_sym (applyWNat m n w R U HU a (T (S m) ε x))
  • (f_equal (applyW m w R) (eq_sym (HTU m ε a x))
     • (applyWNat m n w R T HT ε (Ub m a x)
        • f_equal (T n ε) (applyWNat m n w (shiftStr R) Ub HUb a x)))
  = f_equal (U n a)
      (applyWNat m n w (shiftStr R) (fun k => T (S k)) (exchShift HT) ε x)
    • eq_sym (HTU n ε a (applyW m w (shiftStr (shiftStr R)) x)).
Proof.
  induction m as [|m IHm]; intros n w R T U Ub HT HU HUb HTU HX ε a x.
  - destruct n as [|n]; [|now destruct w]. destruct w.
    assert (E1: applyWNat 0 0 tt R U HU a (T 1 ε x) = eq_refl)
      by now reflexivity.
    assert (E2: applyWNat 0 0 tt R T HT ε (Ub 0 a x) = eq_refl)
      by now reflexivity.
    assert (E3: applyWNat 0 0 tt (shiftStr R) Ub HUb a x = eq_refl)
      by now reflexivity.
    assert (E4: applyWNat 0 0 tt (shiftStr R) (fun k => T (S k))
                  (exchShift HT) ε x = eq_refl) by now reflexivity.
    rewrite E1, E2, E3, E4; simpl.
    now destruct (HTU 0 ε a x).
  - destruct w as [(b, w)|w].
    + now exact (natTwoSkipStep (applyW m w R) (applyW m w (shiftStr R))
        (T m ε) (U m a) (sTop R m b) (T n ε) (U n a)
        _ _ _ _ _ _ _ _
        (HU m m leR_refl a b (T (S (S m)) ε x))
        (HTU (S m) ε a x)
        (HT m m leR_refl ε b (Ub (S m) a x))
        (HUb m m leR_refl a b x)
        (exchShift HT m m leR_refl ε b x)
        (HTU m ε a (sTop (shiftStr (shiftStr R)) m b x))
        (HTU n ε a
           (applyW m w (shiftStr (shiftStr R))
              (sTop (shiftStr (shiftStr R)) m b x)))
        (applyWNat m n w R U HU a)
        (applyWNat m n w R T HT ε)
        (applyWNat m n w (shiftStr R) Ub HUb a
           (sTop (shiftStr (shiftStr R)) m b x))
        (applyWNat m n w (shiftStr R) (fun k => T (S k)) (exchShift HT) ε
           (sTop (shiftStr (shiftStr R)) m b x))
        (HX m m leR_refl ε a b x)
        (IHm n w R T U Ub HT HU HUb HTU HX ε a
           (sTop (shiftStr (shiftStr R)) m b x))).
    + destruct n as [|n]; [now destruct w|].
      now exact (IHm n w (shiftStr R) (fun k => T (S k)) (fun k => U (S k))
        (fun k => Ub (S k)) (exchShift HT) (exchShift HU) (exchShift HUb)
        (slideShift HTU) (hexShift HX) ε a x).
Defined.

(** The compositor against naturality

    The step for an outer [wskip]: the letter is deleted before either word
    acts, so the whole configuration is the induction hypothesis translated
    along one exchange cell. *)

Lemma natCompSkipStep {X Y Z: Type} (F1: X -> Y) (F2: Y -> Z) (G: X -> Z)
  (AC: forall z, F2 (F1 z) = G z) {u v: X} (e: u = v)
  {c: Z} (NG: G v = c) {d: Y} (NF1: F1 v = d) (Rest: F2 d = c)
  (ih: AC v • NG = f_equal F2 NF1 • Rest):
  AC u • (f_equal G e • NG) = f_equal F2 (f_equal F1 e • NF1) • Rest.
Proof.
  destruct e. rewrite !eq_trans_refl_l. now exact ih.
Defined.

(** The step where the outer word keeps the top letter and the inner word
    deletes it: the two words then act on different levels, and the hexagon
    enters through [two], which is [applyWNatTwo] for the outer word. *)

Lemma natCompKeepSkipStep {XP XM XN SM SN: Type}
  (AWg: XP -> XM) (AWf: XM -> XN) (AWgf: XP -> XN)
  (TM: SM -> XM) (TN: SN -> XN) (AWfs: SM -> SN) (sTopM: SM -> XM)
  (AC: forall z, AWf (AWg z) = AWgf z)
  (NTf: forall z, AWf (TM z) = TN (AWfs z))
  (u v: XP) (e: u = v) (m1 m2 m3 m4: SM) (s: SN)
  (NUgt: AWg u = sTopM m1) (ng: m1 = m2) (eM: TM m3 = sTopM m2)
  (nub: m4 = m3) (NTg: AWg v = TM m4) (NGF: AWgf v = TN s)
  (ACs: AWfs m4 = s)
  (two: eq_sym NUgt • (f_equal AWg e • (NTg • f_equal TM nub))
        = f_equal sTopM ng • eq_sym eM)
  (ih: AC v • NGF = f_equal AWf NTg • (NTf m4 • f_equal TN ACs)):
  f_equal AWf (eq_sym NUgt) • AC u • (f_equal AWgf e • NGF)
  = f_equal (fun z => AWf (sTopM z)) ng
    • (f_equal AWf (eq_sym eM) • NTf m3
       • f_equal TN (f_equal AWfs (eq_sym nub) • ACs)).
Proof.
  destruct e, ng, nub, ACs. simpl in two, ih |- *.
  rewrite !eq_trans_refl_l in two |- *.
  rewrite <- two, eq_trans_map_distr, <- !eq_trans_assoc, ih.
  now reflexivity.
Defined.

(** The compositor of two words is compatible with the naturality of a family
    of top faces along them. *)

Lemma applyWNatComp {A: HSet} (P: nat): forall M N (g: Word A M P)
  (f: Word A N M) (Q: FaceStr A) (HQ: CohOf Q)
  (T: forall k (ε: A), Q.(S0) (S k) -> Q.(S0) k) (HT: Exch Q T)
  (HX: ExchHex HQ HT) (ε: A) (x: Q.(S0) (S P)),
  applyWComp P M N g f Q HQ (T P ε x)
  • applyWNat P N (wcomp g f) Q T HT ε x
  = f_equal (applyW M f Q) (applyWNat P M g Q T HT ε x)
    • (applyWNat M N f Q T HT ε (applyW P g (shiftStr Q) x)
       • f_equal (T N ε) (applyWComp P M N g f (shiftStr Q) (cohShift HQ) x)).
Proof.
  induction P as [|P IHP]; intros M N g f Q HQ T HT HX ε x.
  - destruct M as [|M]; [|now destruct g].
    destruct N as [|N]; [|now destruct f].
    destruct g, f. now reflexivity.
  - destruct g as [(b, g)|g].
    + now exact (natCompSkipStep (applyW P g Q) (applyW M f Q)
        (applyW P (wcomp g f) Q) (applyWComp P M N g f Q HQ)
        (eq_sym (HT P P leR_refl ε b x))
        (applyWNat P N (wcomp g f) Q T HT ε (sTop (shiftStr Q) P b x))
        (applyWNat P M g Q T HT ε (sTop (shiftStr Q) P b x))
        (applyWNat M N f Q T HT ε
           (applyW P g (shiftStr Q) (sTop (shiftStr Q) P b x))
         • f_equal (T N ε) (applyWComp P M N g f (shiftStr Q) (cohShift HQ)
                              (sTop (shiftStr Q) P b x)))
        (IHP M N g f Q HQ T HT HX ε (sTop (shiftStr Q) P b x))).
    + destruct M as [|M]; [now destruct g|].
      destruct f as [(a, f)|f].
      * now exact (natCompKeepSkipStep (applyW P g Q) (applyW M f Q)
          (applyW P (wcomp g f) Q) (T M ε) (T N ε) (applyW M f (shiftStr Q))
          (sTop Q M a) (applyWComp P M N g f Q HQ) (applyWNat M N f Q T HT ε)
          _ _ (eq_sym (HT P P leR_refl ε a x)) _ _ _ _ _
          (applyWNat P M g Q (sTop Q) (topCoh HQ) a (T (S P) ε x))
          (applyWNat P M g (shiftStr Q) (fun k => T (S k)) (exchShift HT) ε x)
          (HT M M leR_refl ε a (applyW P g (shiftStr (shiftStr Q)) x))
          (applyWNat P M g (shiftStr Q) (sTop (shiftStr Q))
             (topCoh (cohShift HQ)) a x)
          (applyWNat P M g Q T HT ε (sTop (shiftStr Q) P a x))
          (applyWNat P N (wcomp g f) Q T HT ε (sTop (shiftStr Q) P a x))
          (applyWComp P M N g f (shiftStr Q) (cohShift HQ)
             (sTop (shiftStr Q) P a x))
          (applyWNatTwo P M g Q T (sTop Q) (sTop (shiftStr Q)) HT (topCoh HQ)
             (topCoh (cohShift HQ)) (topSlide HT) (topHex HX) ε a x)
          (IHP M N g f Q HQ T HT HX ε (sTop (shiftStr Q) P a x))).
      * destruct N as [|N]; [now destruct f|].
        now exact (IHP M N g f (shiftStr Q) (cohShift HQ) (fun k => T (S k))
          (exchShift HT) (exchHexShift HX) ε x).
Defined.

(** Associativity of the compositor

    The step where [h] keeps the top position and [g] deletes it. The
    naturality path for [h] changes the point at which the induction
    hypothesis is evaluated. *)

Lemma assocKeepSkipStep {XP XM XN: Type} (AWg: XP -> XM) (AWf: XM -> XN)
  (AWgf: XP -> XN) (AC2: forall w, AWf (AWg w) = AWgf w)
  {u v: XP} (e: u = v) {c1: XM} (ACh: AWg v = c1) {c2: XN} (ACcomp: AWf c1 = c2)
  {d: XN} (AChcomp: AWgf v = d) (FA: d = c2)
  (ih: f_equal AWf ACh • ACcomp = AC2 v • (AChcomp • FA)):
  f_equal AWf (f_equal AWg e • ACh) • ACcomp
  = AC2 u • (f_equal AWgf e • AChcomp • FA).
Proof.
  destruct e. rewrite !eq_trans_refl_l. now exact ih.
Defined.

(** The step where [h] and [g] keep the top position and [f] deletes it.
    The hypothesis [two] is [applyWNatComp] for [h] and [g]. *)

Lemma assocKeepKeepSkipStep {XP XM XN SM: Type}
  (AWg: XP -> XM) (AWf: XM -> XN) (AWgf: XP -> XN) (sTopM: SM -> XM)
  (AC2: forall w, AWf (AWg w) = AWgf w)
  {A' B': XP} (Nh: A' = B') {s1 s2: SM} (ACs: s1 = s2)
  (Ng: AWg B' = sTopM s1) {c1: XM} (ACh: AWg A' = c1) (Nhg: c1 = sTopM s2)
  {c2: XN} (ACcomp: AWf c1 = c2) {d: XN} (AChcomp: AWgf A' = d) (FA: d = c2)
  (two: ACh • Nhg = f_equal AWg Nh • (Ng • f_equal sTopM ACs))
  (ih: f_equal AWf ACh • ACcomp = AC2 A' • (AChcomp • FA)):
  f_equal (fun w => AWf (sTopM w)) ACs • (f_equal AWf (eq_sym Nhg) • ACcomp)
  = f_equal AWf (eq_sym Ng) • AC2 B' • (f_equal AWgf (eq_sym Nh) • AChcomp • FA).
Proof.
  destruct Nh, ACs. simpl in two |- *.
  rewrite (eq_trans_refl_l Ng) in two.
  rewrite (eq_trans_refl_l (f_equal AWf (eq_sym Nhg) • ACcomp)).
  rewrite (eq_trans_refl_l AChcomp).
  rewrite <- (eq_trans_assoc (f_equal AWf (eq_sym Ng)) (AC2 A') (AChcomp • FA)).
  rewrite <- ih.
  rewrite (eq_trans_assoc (f_equal AWf (eq_sym Ng)) (f_equal AWf ACh) ACcomp).
  rewrite <- eq_trans_map_distr, <- two, eq_trans_sym_distr.
  rewrite <- eq_trans_assoc, eq_trans_sym_inv_l.
  now reflexivity.
Defined.

(** The two ways of contracting a composable triple of words agree over
    [wcompAssoc]. At each inductive step, [tailSubst] and
    [f_equal_compose] identify the image of [wcompAssoc] under prefixing
    with its image under the prefixed word action. *)

Lemma applyWAssoc {A: HSet} (r: nat): forall p m n (h: Word A p r)
  (g: Word A m p) (f: Word A n m) (Q: FaceStr A) (HQ: CohOf Q)
  (HQ2: Coh2Of HQ) (x: Q.(S0) r),
  f_equal (applyW m f Q) (applyWComp r p m h g Q HQ x)
  • applyWComp r m n (wcomp h g) f Q HQ x
  = applyWComp p m n g f Q HQ (applyW r h Q x)
    • (applyWComp r p n h (wcomp g f) Q HQ x
       • f_equal (fun w => applyW r w Q x) (wcompAssoc h g f)).
Proof.
  induction r as [|r IHr]; intros p m n h g f Q HQ HQ2 x.
  - destruct p as [|p]; [|now destruct h].
    destruct m as [|m]; [|now destruct g].
    destruct n as [|n]; [|now destruct f].
    destruct h, g, f. now reflexivity.
  - destruct h as [(b, h)|h].
    + now exact (tailSubst _ _ _ _ _
        (eq_sym (f_equal_compose (@wskip A n r b)
           (fun w: Word A n (S r) => applyW (S r) w Q x) (wcompAssoc h g f)))
        (IHr p m n h g f Q HQ HQ2 (sTop Q r b x))).
    + destruct p as [|p]; [now destruct h|].
      destruct g as [(a, g)|g].
      * now exact (tailSubst _ _ _ _ _
          (eq_sym (f_equal_compose (@wskip A n r a)
             (fun w: Word A n (S r) => applyW (S r) w Q x) (wcompAssoc h g f)))
          (assocKeepSkipStep (applyW p g Q) (applyW m f Q)
            (applyW p (wcomp g f) Q) (applyWComp p m n g f Q HQ)
            (eq_sym (applyWNat r p h Q (sTop Q) (topCoh HQ) a x))
            (applyWComp r p m h g Q HQ (sTop Q r a x))
            (applyWComp r m n (wcomp h g) f Q HQ (sTop Q r a x))
            (applyWComp r p n h (wcomp g f) Q HQ (sTop Q r a x))
            (f_equal (fun w => applyW r w Q (sTop Q r a x)) (wcompAssoc h g f))
            (IHr p m n h g f Q HQ HQ2 (sTop Q r a x)))).
      * destruct m as [|m]; [now destruct g|].
        destruct f as [(c, f)|f].
        -- now exact (tailSubst _ _ _ _ _
             (eq_sym (f_equal_compose (@wskip A n r c)
                (fun w: Word A n (S r) => applyW (S r) w Q x)
                (wcompAssoc h g f)))
             (assocKeepKeepSkipStep (applyW p g Q) (applyW m f Q)
               (applyW p (wcomp g f) Q) (sTop Q m c)
               (applyWComp p m n g f Q HQ)
               (applyWNat r p h Q (sTop Q) (topCoh HQ) c x)
               (applyWComp r p m h g (shiftStr Q) (cohShift HQ) x)
               (applyWNat p m g Q (sTop Q) (topCoh HQ) c
                  (applyW r h (shiftStr Q) x))
               (applyWComp r p m h g Q HQ (sTop Q r c x))
               (applyWNat r m (wcomp h g) Q (sTop Q) (topCoh HQ) c x)
               (applyWComp r m n (wcomp h g) f Q HQ (sTop Q r c x))
               (applyWComp r p n h (wcomp g f) Q HQ (sTop Q r c x))
               (f_equal (fun w => applyW r w Q (sTop Q r c x))
                  (wcompAssoc h g f))
               (applyWNatComp r p m h g Q HQ (sTop Q) (topCoh HQ)
                  (topExchHex HQ2) c x)
               (IHr p m n h g f Q HQ HQ2 (sTop Q r c x)))).
        -- destruct n as [|n]; [now destruct f|].
           now exact (tailSubst _ _ _ _ _
             (eq_sym (f_equal_compose (@wkeep A n r)
                (fun w: Word A (S n) (S r) => applyW (S r) w Q x)
                (wcompAssoc h g f)))
             (IHr p m n h g f (shiftStr Q) (cohShift HQ) (cohShift2 HQ2) x)).
Defined.

Section WordUnits.
Context (A: HSet).

(** The unit laws of the compositor *)

(** Sliding the identity word past a top face is the identity of the action,
    read on the shifted structure. *)

Lemma applyWNatId (m: nat): forall (Q: FaceStr A)
  (T: forall k (ε: A), Q.(S0) (S k) -> Q.(S0) k)
  (HT: forall k q (Hq: q <= k) (ε ω: A) (X: Q.(S0) (S (S k))),
    T k ε (Q.(SFace) (S k) q (↑ Hq) ω X) = Q.(SFace) k q Hq ω (T (S k) ε X))
  (ε: A) (x: Q.(S0) (S m)),
  applyWNat m m (wid m) Q T HT ε x
  = applyW_id Q (T m ε x) • eq_sym (f_equal (T m ε) (applyW_id (shiftStr Q) x)).
Proof.
  induction m as [|m IHm]; intros Q T HT ε x.
  - now reflexivity.
  - now exact (IHm (shiftStr Q) (fun k => T (S k))
      (fun k q Hq ε ω X => HT (S k) q (↑ Hq) ε ω X) ε x).
Defined.

Lemma compIdLSkipStep {X Y Z: Type} (F: X -> Y) (G: Z -> X) {z0 z1: Z}
  (μ: z0 = z1) {a0: X} (ι: a0 = G z1) (Nt: a0 = G z0)
  (HNt: ι • eq_sym (f_equal G μ) = Nt) {b1: Y} (Θ: F a0 = b1)
  (τ: b1 = F (G z1)) (IH: Θ • τ = f_equal F ι):
  (f_equal F (eq_sym Nt) • Θ) • τ = f_equal (fun y => F (G y)) μ.
Proof. destruct HNt, μ. now exact (symCancelF F ι Θ τ IH). Defined.

Lemma applyWCompIdR (p: nat): forall m (g: Word A m p) (Q: FaceStr A)
  (HQ: CohOf Q) (x: Q.(S0) p),
  applyWComp p m m g (wid m) Q HQ x
  • f_equal (fun w => applyW p w Q x) (wcompIdr g)
  = applyW_id Q (applyW p g Q x).
Proof.
  induction p as [|p IHp]; intros m g Q HQ x.
  - destruct m as [|m]; [|now destruct g]. destruct g. now reflexivity.
  - destruct g as [(b, g)|g].
    + now exact (fEqualCompEq (wskip b) (fun w => applyW (S p) w Q x)
        (wcompIdr g) _ _ (IHp m g Q HQ (sTop Q p b x))).
    + destruct m as [|m]; [now destruct g|].
      now exact (fEqualCompEq (@wkeep A m p) (fun w => applyW (S p) w Q x)
        (wcompIdr g) _ _ (IHp m g (shiftStr Q) (cohShift HQ) x)).
Defined.

Lemma applyWCompIdL (m: nat): forall n (f: Word A n m) (Q: FaceStr A)
  (HQ: CohOf Q) (x: Q.(S0) m),
  applyWComp m m n (wid m) f Q HQ x
  • f_equal (fun w => applyW m w Q x) (wcompIdl f)
  = f_equal (applyW m f Q) (applyW_id Q x).
Proof.
  induction m as [|m IHm]; intros n f Q HQ x.
  - destruct n as [|n]; [|now destruct f]. destruct f. now reflexivity.
  - destruct f as [(a, f)|f].
    + now exact (fEqualCompEq (wskip a) (fun w => applyW (S m) w Q x)
        (wcompIdl f) _ _
        (compIdLSkipStep (applyW m f Q) (sTop Q m a)
           (applyW_id (shiftStr Q) x) (applyW_id Q (sTop Q m a x))
           (applyWNat m m (wid m) Q (sTop Q) (topCoh HQ) a x)
           (eq_sym (applyWNatId m Q (sTop Q) (topCoh HQ) a x))
           (applyWComp m m n (wid m) f Q HQ (sTop Q m a x))
           (f_equal (fun w => applyW m w Q (sTop Q m a x)) (wcompIdl f))
           (IHm n f Q HQ (sTop Q m a x)))).
    + destruct n as [|n]; [now destruct f|].
      now exact (fEqualCompEq (@wkeep A n m) (fun w => applyW (S m) w Q x)
        (wcompIdl f) _ _ (IHm n f (shiftStr Q) (cohShift HQ) x)).
Defined.

End WordUnits.
