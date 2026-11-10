(** Restricting the inhabited levels of a coherent face presentation.
    A downward-closed strict proposition marks the retained levels. *)

Set Warnings "-notation-overridden".
From Bonak.Lib Require Import HSet HGpd SigT Equiv Funext Notation LeSProp RewLemmas CohShapes.
From Bonak.Presheaf.Gpd Require Import Presentation.

Set Primitive Projections.
Set Printing Projections.

Local Lemma boxEq {S: SProp} (x y: sBox S): x = y.
Proof. destruct x, y. now reflexivity. Defined.

Local Definition boxHSet (S: SProp): HSet := {|
  Dom := sBox S;
  UIP := fun x y p q => eq_hprop_UIP boxEq p q;
|}.

Section Bounded.
Context {A: HSet} (B: nat -> SProp)
  (down: forall k, B (S k) -> B k) (P: νGpdPresentation A).

Definition boundCell k: HGpd :=
  {_: hgpdOfHSet (boxHSet (B k)) & P.(G0) k}.

Definition boundInclude k (h: B k) (x: P.(G0) k): boundCell k := (sbox h; x).

Definition boundCellEquiv k (h: B k): Equiv (boundCell k) (P.(G0) k).
Proof.
  refine (qinvEquiv (fun z => z.2) (boundInclude k h) _ _).
  - now intros [[h'] x].
  - now intro x.
Defined.

Lemma boundPathInjective {k} {x y: boundCell k} (p q: x = y)
  (h: f_equal (fun z: boundCell k => z.2) p =
      f_equal (fun z: boundCell k => z.2) q): p = q.
Proof.
  now exact (eqvInj (symEquiv (eqvInjEquiv (boundCellEquiv k (unbox x.1)))) h).
Defined.

Definition boundFace n q (Hq: q <= n) a (z: boundCell n.+1): boundCell n :=
  boundInclude n (down n (unbox z.1)) (P.(GFace) n q Hq a z.2).

Definition boundFaceCoh n q (Hq: q <= n) r (Hr: r <= q) a b (z: boundCell n.+2):
  boundFace n q Hq a (boundFace n.+1 r (Hr ↕ ↑ Hq) b z) =
    boundFace n r (Hr ↕ Hq) b (boundFace n.+1 q.+1 (⇑ Hq) a z) :=
  f_equal (boundInclude n (down n (down n.+1 (unbox z.1))))
    (P.(GFaceCoh) n q Hq r Hr a b z.2).

Lemma boundFaceCohProject n q (Hq: q <= n) r (Hr: r <= q) a b (z: boundCell n.+2):
  f_equal (fun w: boundCell n => w.2) (boundFaceCoh n q Hq r Hr a b z) =
    P.(GFaceCoh) n q Hq r Hr a b z.2.
Proof.
  exact (f_equal_compose (boundInclude n (down n (down n.+1 (unbox z.1))))
    (fun w: boundCell n => w.2) (P.(GFaceCoh) n q Hq r Hr a b z.2)
    • f_equal_id (P.(GFaceCoh) n q Hq r Hr a b z.2)).
Defined.

Lemma boundFacePathProject n q (Hq: q <= n) a
  {x y: boundCell n.+1} (p: x = y):
  f_equal (fun z: boundCell n => z.2) (f_equal (boundFace n q Hq a) p) =
    f_equal (P.(GFace) n q Hq a) (f_equal (fun z: boundCell n.+1 => z.2) p).
Proof. now destruct p. Defined.

Lemma boundFaceCoh2 n q (Hq: q <= n) r (Hr: r <= q) s (Hs: s <= r)
  a b c (z: boundCell n.+3):
  hexagonal_coherence
    (boundFace n q Hq a) (boundFace n s (Hs ↕ (Hr ↕ Hq)) c) (boundFace n r (Hr ↕ Hq) b)
    (boundFaceCoh n.+1 r (Hr ↕ ↑ Hq) s Hs b c z)
    (boundFaceCoh n.+1 q.+1 (⇑ Hq) r.+1 (⇑ Hr) a b z)
    (boundFaceCoh n.+1 q.+1 (⇑ Hq) s (↑ (Hs ↕ Hr)) a c z)
    (boundFaceCoh n q Hq s (Hs ↕ Hr) a c
      (boundFace n.+2 r.+1 (⇑ (Hr ↕ ↑ Hq)) b z))
    (boundFaceCoh n q Hq r Hr a b
      (boundFace n.+2 s (↑ (↑ (Hs ↕ (Hr ↕ Hq)))) c z))
    (boundFaceCoh n r (Hr ↕ Hq) s Hs b c
      (boundFace n.+2 q.+2 (⇑ (⇑ Hq)) a z)).
Proof.
  unfold hexagonal_coherence. apply boundPathInjective.
  rewrite 4 eq_trans_map_distr, 3 boundFacePathProject.
  refine (f_equal2 (fun p q => p • q)
    (f_equal2 (fun p q => p • q)
      (f_equal (fun p => f_equal (P.(GFace) n q Hq a) p)
        (boundFaceCohProject n.+1 r (Hr ↕ ↑ Hq) s Hs b c z))
      (boundFaceCohProject n q Hq s (Hs ↕ Hr) a c
        (boundFace n.+2 r.+1 (⇑ (Hr ↕ ↑ Hq)) b z)))
    (f_equal (fun p => f_equal (P.(GFace) n s (Hs ↕ (Hr ↕ Hq)) c) p)
      (boundFaceCohProject n.+1 q.+1 (⇑ Hq) r.+1 (⇑ Hr) a b z)) • _).
  refine (P.(GFaceCoh2) n q Hq r Hr s Hs a b c z.2 • _).
  exact (eq_sym (f_equal2 (fun p q => p • q)
    (boundFaceCohProject n q Hq r Hr a b
      (boundFace n.+2 s (↑ (↑ (Hs ↕ (Hr ↕ Hq)))) c z))
    (f_equal2 (fun p q => p • q)
      (f_equal (fun p => f_equal (P.(GFace) n r (Hr ↕ Hq) b) p)
        (boundFaceCohProject n.+1 q.+1 (⇑ Hq) s (↑ (Hs ↕ Hr)) a c z))
      (boundFaceCohProject n r (Hr ↕ Hq) s Hs b c
        (boundFace n.+2 q.+2 (⇑ (⇑ Hq)) a z))))).

Defined.

Definition boundPresentation: νGpdPresentation A := {|
  G0 := boundCell;
  GFace := boundFace;
  GFaceCoh := boundFaceCoh;
  GFaceCoh2 := boundFaceCoh2;
|}.

End Bounded.

Definition cutCell {A: HSet} N (P: νGpdPresentation A) k: HGpd :=
  boundCell (fun l => leR (S l) N) P k.

Definition cutPresentation {A: HSet} N (P: νGpdPresentation A): νGpdPresentation A :=
  boundPresentation (fun l => leR (S l) N) (fun l h => ↓ h) P.

