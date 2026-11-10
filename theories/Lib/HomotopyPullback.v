(** Paths in homotopy-pullback cones, with their base and cell components. *)
Set Warnings "-notation-overridden".
Set Universe Polymorphism.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Bonak.Lib Require Import SigT Notation RewLemmas.
Set Primitive Projections.
Set Printing Projections.
Import Logic.EqNotations.

Local Lemma attachmentPairPathBase {T: Type} {P: T -> Type} {x y: T}
  {u: P x} {v: P y} (p: x = y) (q: rew [P] p in u = v):
  projT1_eq (= p; q) = p.
Proof. now destruct q, p. Defined.

Section AttachmentPaths.
Context {I W T B: Type} (r: I -> W -> B) (d: T -> B).
Local Definition Attachment: Type :=
  {w: W &T forall a: I, {t: T &T r a w = d t}}.

Local Definition attachmentFiberEq {w} (a: I)
  (u v: {t: T &T r a w = d t}) (h: u.1 = v.1)
  (s: eq_refl • v.2 = u.2 • f_equal d h): u = v.
Proof.
  destruct u as [t u], v as [t' v]; cbn in h, s.
  refine (eq_existT_curried h _). destruct h.
  change (u = v). change (eq_refl • v = u) in s.
  now exact (eq_sym s • eq_trans_refl_l v).
Defined.

Local Lemma attachmentFiberEqBase {w} (a: I)
  (u v: {t: T &T r a w = d t}) (h: u.1 = v.1)
  (s: eq_refl • v.2 = u.2 • f_equal d h):
  projT1_eq (attachmentFiberEq a u v h s) = h.
Proof. destruct u, v. unfold attachmentFiberEq. now apply attachmentPairPathBase. Defined.

(** Both the point paths and the square relating the attachment paths are
    needed to identify two homotopy-pullback cones. *)
Definition attachmentEq (u v: Attachment) (p: u.1 = v.1)
  (h: forall a, (u.2 a).1 = (v.2 a).1)
  (s: forall a, f_equal (r a) p • (v.2 a).2 = (u.2 a).2 • f_equal d (h a)):
  u = v.
Proof.
  destruct u as [w u], v as [w' v]; cbn in p, h, s. destruct p.
  now exact (f_equal (fun f => (w; f))
    (functional_extensionality_dep_good u v
      (fun a => attachmentFiberEq a (u a) (v a) (h a) (s a)))).
Defined.

Lemma attachmentEqBase (u v: Attachment) (p: u.1 = v.1)
  (h: forall a, (u.2 a).1 = (v.2 a).1)
  (s: forall a, f_equal (r a) p • (v.2 a).2 = (u.2 a).2 • f_equal d (h a)):
  projT1_eq (attachmentEq u v p h s) = p.
Proof.
  destruct u as [w u], v as [w' v]; cbn in p, h, s. destruct p.
  unfold attachmentEq, projT1_eq.
  rewrite f_equal_compose. now apply fEqualConst.
Defined.

Lemma attachmentEqTop (u v: Attachment) (p: u.1 = v.1)
  (h: forall a, (u.2 a).1 = (v.2 a).1)
  (s: forall a, f_equal (r a) p • (v.2 a).2 = (u.2 a).2 • f_equal d (h a)) a:
  f_equal (fun z: Attachment => (z.2 a).1) (attachmentEq u v p h s) = h a.
Proof.
  destruct u as [w u], v as [w' v]; cbn in p, h, s. destruct p.
  unfold attachmentEq. rewrite f_equal_compose.
  refine (eq_sym (f_equal_compose (fun f => f a) (@projT1 _ _)
    (functional_extensionality_dep_good u v
      (fun a => attachmentFiberEq a (u a) (v a) (h a) (s a)))) • _).
  refine (f_equal (fun q => f_equal (@projT1 _ _) q)
    (f_equal__functional_extensionality_dep_good
      (fun a => attachmentFiberEq a (u a) (v a) (h a) (s a)) a) • _).
  now apply attachmentFiberEqBase.
Defined.

End AttachmentPaths.
