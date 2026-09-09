(** The action of generating cofaces respects the exchange law of faces.
    The result compares the compositor across the coface exchange with the
    supplied face exchange, including the homotopies identifying generators. *)

Set Warnings "-notation-overridden".
From Bonak.Lib Require Import HSet Notation LeSProp.
From Bonak.Lib Require Import RewLemmas NatLemmas BoolLemmas.
From Bonak.Presheaf Require Import νSemiShape WordAction WordCoherence.

Set Primitive Projections.
Set Printing Projections.

Lemma natGenTopStep {T: Type} {y0 y1 y2 y3 y4 y5 y6: T}
  (a1: y0 = y1) (c: y1 = y2) (i6: y2 = y3) (d1: y4 = y3) (d2: y5 = y4)
  (i5: y1 = y6) (s: y6 = y3) (H: c • i6 = i5 • s):
  a1 • ((c • (i6 • eq_sym d1)) • eq_sym d2)
  = (a1 • i5) • (s • eq_sym (d2 • d1)).
Proof.
  destruct d1, d2.
  now exact (f_equal (fun z => a1 • z) H • eq_sym (eqTransAssoc a1 i5 s)).
Defined.

Lemma sqTopStep {T: Type} (F0: T -> T) (i: forall z, F0 z = z)
  {e1 z1 s1 y0 m0 c1 c2: T}
  (g1: e1 = s1) (K: z1 = e1) (α': z1 = s1) (Hα': K • g1 = α')
  (T1: F0 e1 = c1) (a: c1 = e1) (H1: T1 • a = i e1)
  (T2: z1 = c2) (b: c2 = e1) (Hom: T2 • b = K)
  (Wc: c1 = c2) (HW: a • eq_sym b = Wc)
  (d: y0 = m0) (h: m0 = s1) (Nt: e1 = y0)
  (HNt: g1 • (eq_sym h • eq_sym d) = Nt):
  ((f_equal F0 (eq_sym Nt) • T1) • (Wc • eq_sym T2)) • α'
  = (i y0 • d) • h.
Proof.
  destruct HW, HNt, Hα', d, h, g1, b, a, Hom, T2.
  now exact (eq_trans_refl_l _ • H1).
Defined.

Section GeneratorCoherence.
Context (A: HSet).

(** The action of a generating coface

    The two recursion equations of [applyWgen]: the coface deleting the top
    dimension acts as the top face after the identity word, and any other
    coface is a [wkeep] whose action is that of the shifted structure. *)

Lemma applyWgenTopEq (Q: FaceStr A) (n: nat) (Hq: n <= n) (ε: A)
  (x: Q.(S0) (S n)):
  applyWgen A Q n n Hq ε x
  = f_equal (fun w => applyW (S n) w Q x) (wgenTop n ε)
    • applyW_id Q (sTop Q n ε x).
Proof.
  destruct n as [|n].
  - now reflexivity.
  - unfold applyWgen; cbn [nat_ind].
    rewrite (boolConvoyTrue _ _ (natEqbRefl (S n))).
    rewrite (NatLemmas.natUIP (natEqbEq (S n) (S n) (natEqbRefl (S n))) eq_refl).
    now exact (eqIndRPath (fun w => applyW (S (S n)) w Q x) (wgenTop (S n) ε)
      (applyW_id Q (sTop Q (S n) ε x))).
Qed.

Lemma applyWgenLiftEq (Q: FaceStr A) (n q: nat) (Hq: q <= n) (ε: A)
  (x: Q.(S0) (S (S n))) (HqS: q <= S n):
  applyWgen A Q (S n) q HqS ε x
  = f_equal (fun w => applyW (S (S n)) w Q x) (wgenLift Hq ε)
    • applyWgen A (shiftStr Q) n q Hq ε x.
Proof.
  unfold applyWgen; cbn [nat_ind].
  rewrite (boolConvoyFalse _ _ (leRNeqS q n Hq)).
  now exact (eqIndRPath (fun w => applyW (S (S n)) w Q x) (wgenLift Hq ε)
    (applyWgen A (shiftStr Q) n q Hq ε x)).
Qed.

(** The naturality cell at a generating coface

    Sliding a generating coface past a top face is, under the identification
    of the action of the coface with the corresponding face, the instance of
    the exchange law that the top face satisfies. *)

Lemma applyWNatNatW (m n: nat) {w w': Word A n m} (e: w = w') (Q: FaceStr A)
  (T: forall k (ε: A), Q.(S0) (S k) -> Q.(S0) k)
  (HT: forall k q (Hq: q <= k) (ε ω: A) (X: Q.(S0) (S (S k))),
    T k ε (Q.(SFace) (S k) q (↑ Hq) ω X) = Q.(SFace) k q Hq ω (T (S k) ε X))
  (ε: A) (x: Q.(S0) (S m)):
  applyWNat m n w Q T HT ε x
  = f_equal (fun z => applyW m z Q (T m ε x)) e
    • (applyWNat m n w' Q T HT ε x
       • eq_sym (f_equal (fun z => T n ε (applyW m z (shiftStr Q) x)) e)).
Proof.
  destruct e. now exact (eq_sym (eq_trans_refl_l (applyWNat m n w Q T HT ε x))).
Defined.

Lemma applyWNatGenTop (n: nat) (Q: FaceStr A)
  (T: forall k (ε: A), Q.(S0) (S k) -> Q.(S0) k)
  (HT: forall k q (Hq: q <= k) (ε ω: A) (X: Q.(S0) (S (S k))),
    T k ε (Q.(SFace) (S k) q (↑ Hq) ω X) = Q.(SFace) k q Hq ω (T (S k) ε X))
  (Hn: n <= n) (ε ω: A) (x: Q.(S0) (S (S n))):
  applyWNat (S n) n (wgen n n ω) Q T HT ε x
  = applyWgen A Q n n Hn ω (T (S n) ε x)
    • (eq_sym (HT n n Hn ε ω x)
       • eq_sym (f_equal (T n ε) (applyWgen A (shiftStr Q) n n Hn ω x))).
Proof.
  rewrite (applyWNatNatW (S n) n (wgenTop n ω) Q T HT ε x).
  rewrite (applyWNatSkip n n ω (wid n) Q T HT ε x).
  rewrite (applyWNatId A n Q T HT ε (sTop (shiftStr Q) n ω x)).
  rewrite (applyWgenTopEq Q n Hn ω (T (S n) ε x)).
  rewrite (applyWgenTopEq (shiftStr Q) n Hn ω x).
  rewrite eq_trans_map_distr.
  rewrite <- (f_equal_compose (fun w => applyW (S n) w (shiftStr Q) x) (T n ε)
                (wgenTop n ω)).
  now exact (natGenTopStep
    (f_equal (fun z: Word A n (S n) => applyW (S n) z Q (T (S n) ε x))
       (wgenTop n ω))
    (f_equal (applyW n (wid n) Q) (eq_sym (HT n n leR_refl ε ω x)))
    (applyW_id Q (T n ε (sTop (shiftStr Q) n ω x)))
    (f_equal (T n ε) (applyW_id (shiftStr Q) (sTop (shiftStr Q) n ω x)))
    (f_equal (T n ε)
       (f_equal (fun w: Word A n (S n) => applyW (S n) w (shiftStr Q) x)
          (wgenTop n ω)))
    (applyW_id Q (sTop Q n ω (T (S n) ε x)))
    (eq_sym (HT n n Hn ε ω x))
    (homotopyNat (applyW n (wid n) Q) (fun z => z) (@applyW_id A n Q)
       (eq_sym (HT n n Hn ε ω x))
     • f_equal (fun u => applyW_id Q (sTop Q n ω (T (S n) ε x)) • u)
         (f_equal_id (eq_sym (HT n n Hn ε ω x))))).
Qed.

Lemma applyWNatGen (n: nat): forall (Q: FaceStr A)
  (T: forall k (ε: A), Q.(S0) (S k) -> Q.(S0) k)
  (HT: forall k q (Hq: q <= k) (ε ω: A) (X: Q.(S0) (S (S k))),
    T k ε (Q.(SFace) (S k) q (↑ Hq) ω X) = Q.(SFace) k q Hq ω (T (S k) ε X))
  (r: nat) (Hr: r <= n) (ε ω: A) (x: Q.(S0) (S (S n))),
  applyWNat (S n) n (wgen n r ω) Q T HT ε x
  = applyWgen A Q n r Hr ω (T (S n) ε x)
    • (eq_sym (HT n r Hr ε ω x)
       • eq_sym (f_equal (T n ε) (applyWgen A (shiftStr Q) n r Hr ω x))).
Proof.
  induction n as [|n IHn]; intros Q T HT r Hr ε ω x.
  - pose proof (leR0Eq Hr) as Er; subst r.
    now exact (applyWNatGenTop 0 Q T HT Hr ε ω x).
  - destruct (Nat.eqb r (S n)) eqn:E.
    + pose proof (natEqbEq r (S n) E) as Er; subst r.
      now exact (applyWNatGenTop (S n) Q T HT Hr ε ω x).
    + assert (Hr': r <= n) by now exact (leRDown r n Hr E).
      rewrite (applyWNatNatW (S (S n)) (S n) (wgenLift Hr' ω) Q T HT ε x).
      rewrite (applyWNatKeep (S n) n (wgen n r ω) Q T HT ε x).
      rewrite (IHn (shiftStr Q) (fun k => T (S k))
                 (fun k q Hq ε ω X => HT (S k) q (↑ Hq) ε ω X) r Hr' ε ω x).
      rewrite (applyWgenLiftEq Q n r Hr' ω (T (S (S n)) ε x) Hr).
      rewrite (applyWgenLiftEq (shiftStr Q) n r Hr' ω x Hr).
      rewrite eq_trans_map_distr.
      rewrite <- (f_equal_compose (fun w => applyW (S (S n)) w (shiftStr Q) x)
                    (T (S n) ε) (wgenLift Hr' ω)).
      now exact (assoc5S _ _ _ _ _).
Qed.

(** The commuting square between the two exchange laws

    [SqOf] is the square at a chosen presentation of the two composable pairs
    of words: the compositor of the pair, conjugated by the equality of words
    that presents the exchange relation, against the exchange law of the face
    structure, read through the identifications [α], [α'] of the iterated
    action with the iterated face. *)

Definition SqOf (Q: FaceStr A) (HQ: CohOf Q) (n q: nat) (Hq: q <= n) (r: nat)
  (Hr: r <= q) (ε ω: A) (X: Q.(S0) (S (S n)))
  (u u': Word A (S n) (S (S n))) (v v': Word A n (S n))
  (e: wcomp u v = wcomp u' v')
  (α: applyW (S n) v Q (applyW (S (S n)) u Q X)
      = Q.(SFace) n q Hq ε (Q.(SFace) (S n) r (Hr ↕ (↑ Hq)) ω X))
  (α': applyW (S n) v' Q (applyW (S (S n)) u' Q X)
       = Q.(SFace) n r (Hr ↕ Hq) ω (Q.(SFace) (S n) (S q) (⇑ Hq) ε X)): Type :=
  (applyWComp (S (S n)) (S n) n u v Q HQ X
   • (f_equal (fun w => applyW (S (S n)) w Q X) e
      • eq_sym (applyWComp (S (S n)) (S n) n u' v' Q HQ X))) • α'
  = α • HQ n q Hq r Hr ε ω X.

(** The comparison of the iterated actions of two presentations of the same
    composable pair. *)

Definition sqCmp (Q: FaceStr A) (n: nat) (X: Q.(S0) (S (S n)))
  {u u0: Word A (S n) (S (S n))} (eu: u = u0)
  {v v0: Word A n (S n)} (ev: v = v0):
  applyW (S n) v Q (applyW (S (S n)) u Q X)
  = applyW (S n) v0 Q (applyW (S (S n)) u0 Q X) :=
  f_equal (fun w => applyW (S n) w Q (applyW (S (S n)) u Q X)) ev
  • f_equal (applyW (S n) v0 Q)
      (f_equal (fun w => applyW (S (S n)) w Q X) eu).

Lemma sqAlphaEq (Q: FaceStr A) (HQ: CohOf Q) (n q: nat) (Hq: q <= n) (r: nat)
  (Hr: r <= q) (ε ω: A) (X: Q.(S0) (S (S n)))
  (u u': Word A (S n) (S (S n))) (v v': Word A n (S n))
  (e: wcomp u v = wcomp u' v') α β α' β' (Hα: α = β) (Hα': α' = β')
  (H: SqOf Q HQ n q Hq r Hr ε ω X u u' v v' e β β'):
  SqOf Q HQ n q Hq r Hr ε ω X u u' v v' e α α'.
Proof. now destruct Hα, Hα'. Defined.

(** The square is insensitive to the presentation of the words: equalities of
    words are unique, and the two iterated actions differ by [sqCmp]. *)

Lemma sqNat (Q: FaceStr A) (HQ: CohOf Q) (n q: nat) (Hq: q <= n) (r: nat)
  (Hr: r <= q) (ε ω: A) (X: Q.(S0) (S (S n)))
  {u u0 u' u0': Word A (S n) (S (S n))} {v v0 v' v0': Word A n (S n)}
  (eu: u = u0) (ev: v = v0) (eu': u' = u0') (ev': v' = v0')
  (e: wcomp u v = wcomp u' v') (e0: wcomp u0 v0 = wcomp u0' v0')
  (α0: applyW (S n) v0 Q (applyW (S (S n)) u0 Q X)
       = Q.(SFace) n q Hq ε (Q.(SFace) (S n) r (Hr ↕ (↑ Hq)) ω X))
  (α0': applyW (S n) v0' Q (applyW (S (S n)) u0' Q X)
        = Q.(SFace) n r (Hr ↕ Hq) ω (Q.(SFace) (S n) (S q) (⇑ Hq) ε X))
  (H: SqOf Q HQ n q Hq r Hr ε ω X u0 u0' v0 v0' e0 α0 α0'):
  SqOf Q HQ n q Hq r Hr ε ω X u u' v v' e
    (sqCmp Q n X eu ev • α0) (sqCmp Q n X eu' ev' • α0').
Proof.
  destruct eu, ev, eu', ev'.
  unfold SqOf in *.
  rewrite (wordUIP A (S (S n)) n (wcomp u v) (wcomp u' v') e e0).
  now exact (f_equal (fun z => applyWComp (S (S n)) (S n) n u v Q HQ X
       • (f_equal (fun w: Word A n (S (S n)) => applyW (S (S n)) w Q X) e0
          • eq_sym (applyWComp (S (S n)) (S n) n u' v' Q HQ X)) • z)
       (eq_trans_refl_l α0')
     • (H • eq_sym (f_equal (fun z => z • HQ n q Hq r Hr ε ω X)
                      (eq_trans_refl_l α0)))).
Qed.

(** A square all of whose words keep the top dimension is the square of the
    shifted structure. *)

Lemma sqKeep (Q: FaceStr A) (HQ: CohOf Q) (n q: nat) (Hq: q <= n) (r: nat)
  (Hr: r <= q) (ε ω: A) (X: Q.(S0) (S (S (S n))))
  (u u': Word A (S n) (S (S n))) (v v': Word A n (S n))
  (e: wcomp u v = wcomp u' v') α α'
  (H: SqOf (shiftStr Q) (cohShift HQ) n q Hq r Hr ε ω X u u' v v' e α α'):
  SqOf Q HQ (S n) q (↑ Hq) r Hr ε ω X (wkeep u) (wkeep u') (wkeep v) (wkeep v')
    (f_equal wkeep e) α α'.
Proof.
  unfold SqOf in *.
  now exact (f_equal (fun z =>
      (applyWComp (S (S (S n))) (S (S n)) (S n) (wkeep u) (wkeep v) Q HQ X
       • (z • eq_sym (applyWComp (S (S (S n))) (S (S n)) (S n) (wkeep u')
                        (wkeep v') Q HQ X))) • α')
      (f_equal_compose (@wkeep A n (S (S n)))
         (fun w: Word A (S n) (S (S (S n))) => applyW (S (S (S n))) w Q X) e)
    • H).
Qed.

(** The square at a coface deleting the top dimension. *)

Lemma sqTop (Q: FaceStr A) (HQ: CohOf Q) (n r: nat) (Hn: n <= n) (Hr: r <= n)
  (ε ω: A) (X: Q.(S0) (S (S n))):
  SqOf Q HQ n n Hn r Hr ε ω X
    (wkeep (wgen n r ω)) (wskip ε (wid (S n))) (wskip ε (wid n)) (wgen n r ω)
    (f_equal (wskip ε)
       (wcompIdr (wgen n r ω) • eq_sym (wcompIdl (wgen n r ω))))
    (applyW_id Q (sTop Q n ε (applyW (S n) (wgen n r ω) (shiftStr Q) X))
     • f_equal (sTop Q n ε) (applyWgen A (shiftStr Q) n r Hr ω X))
    (applyWgen A Q n r Hr ω (applyW (S n) (wid (S n)) Q (sTop Q (S n) ε X))
     • f_equal (Q.(SFace) n r (Hr ↕ Hn) ω)
         (applyW_id Q (sTop Q (S n) ε X))).
Proof.
  unfold SqOf.
  now exact (sqTopStep (applyW n (wid n) Q) (@applyW_id A n Q)
    (applyWgen A Q n r Hr ω (sTop Q (S n) ε X))
    (f_equal (applyW (S n) (wgen n r ω) Q) (applyW_id Q (sTop Q (S n) ε X)))
    (applyWgen A Q n r Hr ω (applyW (S n) (wid (S n)) Q (sTop Q (S n) ε X))
     • f_equal (Q.(SFace) n r (Hr ↕ Hn) ω) (applyW_id Q (sTop Q (S n) ε X)))
    (homotopyNat (applyW (S n) (wgen n r ω) Q)
       (Q.(SFace) n r (Hr ↕ Hn) ω) (applyWgen A Q n r Hr ω)
       (applyW_id Q (sTop Q (S n) ε X)))
    (applyWComp (S n) n n (wgen n r ω) (wid n) Q HQ (sTop Q (S n) ε X))
    (f_equal (fun w => applyW (S n) w Q (sTop Q (S n) ε X))
       (wcompIdr (wgen n r ω)))
    (applyWCompIdR A (S n) n (wgen n r ω) Q HQ (sTop Q (S n) ε X))
    (applyWComp (S n) (S n) n (wid (S n)) (wgen n r ω) Q HQ
       (sTop Q (S n) ε X))
    (f_equal (fun w => applyW (S n) w Q (sTop Q (S n) ε X))
       (wcompIdl (wgen n r ω)))
    (applyWCompIdL A (S n) n (wgen n r ω) Q HQ (sTop Q (S n) ε X))
    (f_equal (fun w: Word A n (S (S n)) => applyW (S (S n)) w Q X)
       (f_equal (wskip ε)
          (wcompIdr (wgen n r ω) • eq_sym (wcompIdl (wgen n r ω)))))
    (eq_sym (fEqualSkipSplit (@wskip A n (S n) ε)
       (fun w: Word A n (S (S n)) => applyW (S (S n)) w Q X)
       (wcompIdr (wgen n r ω)) (wcompIdl (wgen n r ω))))
    (f_equal (sTop Q n ε) (applyWgen A (shiftStr Q) n r Hr ω X))
    (HQ n n Hn r Hr ε ω X)
    (applyWNat (S n) n (wgen n r ω) Q (sTop Q) (topCoh HQ) ε X)
    (eq_sym (applyWNatGen n Q (sTop Q) (topCoh HQ) r Hr ε ω X))).
Qed.

(** Reading the identification of an iterated action with an iterated face
    through a change of presentation of the two words. *)

Lemma alphaGlue (Q: FaceStr A) (n q: nat) (Hq: q <= n) (r: nat)
  (Hrq: r <= S n) (ε ω: A) (X: Q.(S0) (S (S n)))
  {u0: Word A (S n) (S (S n))} (eu: wgen (S n) r ω = u0)
  {v0: Word A n (S n)} (ev: wgen n q ε = v0)
  (hv0: forall z, applyW (S n) v0 Q z = Q.(SFace) n q Hq ε z)
  (hu0: applyW (S (S n)) u0 Q X = Q.(SFace) (S n) r Hrq ω X)
  (Hpv: forall z, applyWgen A Q n q Hq ε z
        = f_equal (fun w => applyW (S n) w Q z) ev • hv0 z)
  (Hpu: applyWgen A Q (S n) r Hrq ω X
        = f_equal (fun w => applyW (S (S n)) w Q X) eu • hu0):
  applyWgen A Q n q Hq ε (applyW (S (S n)) (wgen (S n) r ω) Q X)
  • f_equal (Q.(SFace) n q Hq ε) (applyWgen A Q (S n) r Hrq ω X)
  = sqCmp Q n X eu ev
    • (hv0 (applyW (S (S n)) u0 Q X) • f_equal (Q.(SFace) n q Hq ε) hu0).
Proof.
  rewrite (Hpv (applyW (S (S n)) (wgen (S n) r ω) Q X)), Hpu, eq_trans_map_distr.
  now exact (prependEq _ _ _ _ _
    (alphaTrans (applyW (S n) v0 Q) (Q.(SFace) n q Hq ε) hv0
       (f_equal (fun w => applyW (S (S n)) w Q X) eu) hu0)).
Qed.

(** The square at the generating cofaces, in the top case. *)

Lemma sqTopWgen (Q: FaceStr A) (HQ: CohOf Q) (n: nat) (Hn: n <= n) (r: nat)
  (Hr: r <= n) (ε ω: A) (X: Q.(S0) (S (S n))):
  SqOf Q HQ n n Hn r Hr ε ω X (wgen (S n) r ω) (wgen (S n) (S n) ε)
    (wgen n n ε) (wgen n r ω) (wgenExchange n n Hn r Hr ε ω)
    (applyWgen A Q n n Hn ε (applyW (S (S n)) (wgen (S n) r ω) Q X)
     • f_equal (Q.(SFace) n n Hn ε)
         (applyWgen A Q (S n) r (Hr ↕ (↑ Hn)) ω X))
    (applyWgen A Q n r (Hr ↕ Hn) ω (applyW (S (S n)) (wgen (S n) (S n) ε) Q X)
     • f_equal (Q.(SFace) n r (Hr ↕ Hn) ω)
         (applyWgen A Q (S n) (S n) (⇑ Hn) ε X)).
Proof.
  now exact (sqAlphaEq Q HQ n n Hn r Hr ε ω X
    (wgen (S n) r ω) (wgen (S n) (S n) ε) (wgen n n ε) (wgen n r ω)
    (wgenExchange n n Hn r Hr ε ω) _ _ _ _
    (alphaGlue Q n n Hn r (Hr ↕ (↑ Hn)) ε ω X
       (wgenLift (Hr ↕ Hn) ω) (wgenTop n ε)
       (fun z => applyW_id Q (sTop Q n ε z))
       (applyWgen A (shiftStr Q) n r Hr ω X)
       (fun z => applyWgenTopEq Q n Hn ε z)
       (applyWgenLiftEq Q n r (Hr ↕ Hn) ω X (Hr ↕ (↑ Hn))))
    (alphaGlue Q n r (Hr ↕ Hn) (S n) (⇑ Hn) ω ε X
       (wgenTop (S n) ε) (@eq_refl _ (wgen n r ω))
       (fun z => applyWgen A Q n r (Hr ↕ Hn) ω z)
       (applyW_id Q (sTop Q (S n) ε X))
       (fun z => eq_sym (eq_trans_refl_l (applyWgen A Q n r (Hr ↕ Hn) ω z)))
       (applyWgenTopEq Q (S n) (⇑ Hn) ε X))
    (sqNat Q HQ n n Hn r Hr ε ω X
       (wgenLift (Hr ↕ Hn) ω) (wgenTop n ε) (wgenTop (S n) ε)
       (@eq_refl _ (wgen n r ω)) (wgenExchange n n Hn r Hr ε ω)
       (f_equal (wskip ε)
          (wcompIdr (wgen n r ω) • eq_sym (wcompIdl (wgen n r ω))))
       _ _ (sqTop Q HQ n r Hn Hr ε ω X))).
Qed.

(** The square at the generating cofaces: the exchange law read off the
    compositor at two generating cofaces is the exchange law of the face
    structure, under the identification of the action of a coface with the
    corresponding face. *)

Lemma applyWgenCoh (n: nat): forall (Q: FaceStr A) (HQ: CohOf Q) (q: nat)
  (Hq: q <= n) (r: nat) (Hr: r <= q) (ε ω: A) (X: Q.(S0) (S (S n))),
  SqOf Q HQ n q Hq r Hr ε ω X (wgen (S n) r ω) (wgen (S n) (S q) ε)
    (wgen n q ε) (wgen n r ω) (wgenExchange n q Hq r Hr ε ω)
    (applyWgen A Q n q Hq ε (applyW (S (S n)) (wgen (S n) r ω) Q X)
     • f_equal (Q.(SFace) n q Hq ε)
         (applyWgen A Q (S n) r (Hr ↕ (↑ Hq)) ω X))
    (applyWgen A Q n r (Hr ↕ Hq) ω (applyW (S (S n)) (wgen (S n) (S q) ε) Q X)
     • f_equal (Q.(SFace) n r (Hr ↕ Hq) ω)
         (applyWgen A Q (S n) (S q) (⇑ Hq) ε X)).
Proof.
  induction n as [|n IHn]; intros Q HQ q Hq r Hr ε ω X.
  - pose proof (leR0Eq Hq) as Eq; subst q.
    now exact (sqTopWgen Q HQ 0 Hq r Hr ε ω X).
  - destruct (Nat.eqb q (S n)) eqn:E.
    + pose proof (natEqbEq q (S n) E) as Eq; subst q.
      now exact (sqTopWgen Q HQ (S n) Hq r Hr ε ω X).
    + assert (Hq': q <= n) by now exact (leRDown q n Hq E).
      now exact (sqAlphaEq Q HQ (S n) q Hq r Hr ε ω X
        (wgen (S (S n)) r ω) (wgen (S (S n)) (S q) ε) (wgen (S n) q ε)
        (wgen (S n) r ω) (wgenExchange (S n) q Hq r Hr ε ω) _ _ _ _
        (alphaGlue Q (S n) q Hq r (Hr ↕ (↑ Hq)) ε ω X
           (wgenLift (Hr ↕ Hq) ω) (wgenLift Hq' ε)
           (fun z => applyWgen A (shiftStr Q) n q Hq' ε z)
           (applyWgen A (shiftStr Q) (S n) r (Hr ↕ Hq) ω X)
           (fun z => applyWgenLiftEq Q n q Hq' ε z Hq)
           (applyWgenLiftEq Q (S n) r (Hr ↕ Hq) ω X (Hr ↕ (↑ Hq))))
        (alphaGlue Q (S n) r (Hr ↕ Hq) (S q) (⇑ Hq) ω ε X
           (wgenLift (⇑ Hq') ε) (wgenLift (Hr ↕ Hq') ω)
           (fun z => applyWgen A (shiftStr Q) n r (Hr ↕ Hq') ω z)
           (applyWgen A (shiftStr Q) (S n) (S q) (⇑ Hq') ε X)
           (fun z => applyWgenLiftEq Q n r (Hr ↕ Hq') ω z (Hr ↕ Hq))
           (applyWgenLiftEq Q (S n) (S q) (⇑ Hq') ε X (⇑ Hq)))
        (sqNat Q HQ (S n) q Hq r Hr ε ω X
           (wgenLift (Hr ↕ Hq) ω) (wgenLift Hq' ε) (wgenLift (⇑ Hq') ε)
           (wgenLift (Hr ↕ Hq') ω) (wgenExchange (S n) q Hq r Hr ε ω)
           (f_equal wkeep (wgenExchange n q Hq' r Hr ε ω)) _ _
           (sqKeep Q HQ n q Hq' r Hr ε ω X
              (wgen (S n) r ω) (wgen (S n) (S q) ε) (wgen n q ε)
              (wgen n r ω) (wgenExchange n q Hq' r Hr ε ω) _ _
              (IHn (shiftStr Q) (cohShift HQ) q Hq' r Hr ε ω X)))).
Qed.

End GeneratorCoherence.
