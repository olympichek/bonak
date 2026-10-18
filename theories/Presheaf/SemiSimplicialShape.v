(** The augmented semi-simplicial shape category has natural numbers
    as objects. A morphism [n -> m] is a strictly monotone injection from
    [n] positions into [m] positions, represented by its kept and skipped
    positions. Object zero supplies the augmentation.

    Words store the top position first. A [wskip] deletes that position
    and [wkeep] preserves it. Recursion on the codomain makes a word a sum,
    so its case analysis needs no dependent inversion. *)

Set Warnings "-notation-overridden".
From Bonak Require Import HSet Notation LeSProp NatLemmas.
From Bonak.Category Require Import Category.

Set Primitive Projections.
Set Printing Projections.

Unset Universe Minimization ToSet.

Section SemiSimplicialShape.

(** [Word n m] is the type of morphisms [n -> m] of the semi-simplicial shape
    category. *)

Fixpoint Word (n m: nat): Type :=
  match m with
  | 0 => match n with 0 => unit | S _ => Empty_set end
  | S m => Word n m + (match n with 0 => Empty_set | S n => Word n m end)
  end.

Definition wnil: Word 0 0 := tt.
Definition wskip {n m} (w: Word n m): Word n (S m) := inl w.
Definition wkeep {n m} (w: Word n m): Word (S n) (S m) := inr w.

(** Identities and composition. [wcomp g f] is [g] after [f]; the semi-simplicial shape
    category is written in diagrammatic order, so it is the composite [f ⨟
    g]. *)

Fixpoint wid (n: nat): Word n n :=
  match n with 0 => wnil | S n => wkeep (wid n) end.

Fixpoint wcomp (p: nat) {struct p}:
  forall m n, Word m p -> Word n m -> Word n p :=
  match p as p return forall m n, Word m p -> Word n m -> Word n p with
  | 0 =>
    fun m =>
      match m as m return forall n, Word m 0 -> Word n m -> Word n 0 with
      | 0 => fun n _ f => f
      | S m => fun n g _ => match g return Word n 0 with end
      end
  | S p =>
    fun m n g f =>
      match g with
      | inl g => wskip (wcomp p m n g f)
      | inr g =>
        (match m as m return
           (match m return Type with 0 => Empty_set | S m => Word m p end) ->
           Word n m -> Word n (S p)
         with
         | 0 => fun g _ => match g return Word n (S p) with end
         | S m => fun g f =>
           match f with
           | inl f => wskip (wcomp p m n g f)
           | inr f =>
             (match n as n return
                (match n return Type with 0 => Empty_set | S n => Word n m end) ->
                Word n (S p)
              with
              | 0 => fun f => match f return Word 0 (S p) with end
              | S n => fun f => wkeep (wcomp p m n g f)
              end) f
           end
         end) g f
      end
  end.

Arguments wcomp {p m n} g f.

(** The three computation rules of composition, in the shape used below. *)

Lemma wcomp_skip {m n p} (g: Word m p) (f: Word n m):
  wcomp (wskip g) f = wskip (wcomp g f).
Proof. now reflexivity. Defined.

Lemma wcomp_keep_skip {m n p} (g: Word m p) (f: Word n m):
  wcomp (wkeep g) (wskip f) = wskip (wcomp g f).
Proof. now reflexivity. Defined.

Lemma wcomp_keep_keep {m n p} (g: Word m p) (f: Word n m):
  wcomp (wkeep g) (wkeep f) = wkeep (wcomp g f).
Proof. now reflexivity. Defined.

(** The hom-types are sets: words are finite trees of kept and skipped
    positions. *)

Fixpoint wordUIP (m n: nat) {struct m}:
  forall (w w': Word n m) (h g: w = w'), h = g.
Proof.
  destruct m as [|m].
  - destruct n as [|n]; intros w w' h g.
    + now apply unit_UIP.
    + now destruct w.
  - destruct n as [|n]; intros w w' h g.
    + now exact (@sumUIP {| Dom := Word 0 m; UIP := wordUIP m 0 |}
                         hEmpty w w' h g).
    + now exact (@sumUIP
        {| Dom := Word (S n) m; UIP := wordUIP m (S n) |}
        {| Dom := Word n m; UIP := wordUIP m n |} w w' h g).
Defined.

Definition wordSet (n m: nat): HSet := {|
  Dom := Word n m;
  UIP := wordUIP m n;
|}.

(** The category laws *)

Lemma wcompIdl {m n} (f: Word n m): wcomp (wid m) f = f.
Proof.
  revert n f; induction m as [|m IHm]; intros n f.
  - destruct n as [|n]; [now destruct f | now destruct f].
  - destruct f as [f|f].
    + now exact (f_equal wskip (IHm n f)).
    + destruct n as [|n]; [now destruct f|].
      now exact (f_equal (@wkeep n m) (IHm n f)).
Defined.

Lemma wcompIdr {n p} (g: Word n p): wcomp g (wid n) = g.
Proof.
  revert n g; induction p as [|p IHp]; intros n g.
  - destruct n as [|n]; [now destruct g | now destruct g].
  - destruct g as [g|g].
    + now exact (f_equal wskip (IHp n g)).
    + destruct n as [|n]; [now destruct g|].
      now exact (f_equal (@wkeep n p) (IHp n g)).
Defined.

Lemma wcompAssoc {q p m n} (h: Word p q) (g: Word m p) (f: Word n m):
  wcomp h (wcomp g f) = wcomp (wcomp h g) f.
Proof.
  revert p m n h g f; induction q as [|q IHq]; intros p m n h g f.
  - destruct p as [|p]; [|now destruct h].
    destruct m as [|m]; [|now destruct g].
    destruct n as [|n]; [|now destruct f].
    now destruct h, g, f.
  - destruct h as [h|h].
    + now exact (f_equal wskip (IHq p m n h g f)).
    + destruct p as [|p]; [now destruct h|].
      destruct g as [g|g].
      * now exact (f_equal wskip (IHq p m n h g f)).
      * destruct m as [|m]; [now destruct g|].
        destruct f as [f|f].
        -- now exact (f_equal wskip (IHq p m n h g f)).
        -- destruct n as [|n]; [now destruct f|].
           now exact (f_equal (@wkeep n q) (IHq p m n h g f)).
Defined.

(** The object [n] represents [n] positions, corresponding to geometric
    dimension [n - 1] for positive [n]. Object [0] is the empty shape,
    giving the augmentation. *)

Definition SemiSimplicialShape: Category := {|
  CObj := nat;
  CHom := wordSet;
  cid := wid;
  ccomp a b c f g := wcomp g f;
  cidl a b f := wcompIdr f;
  cidr a b f := wcompIdl f;
  cassoc a b c d f g h := wcompAssoc h g f;
|}.

(** Generating cofaces

    [wgen n q] deletes position [q] when [q <= n]. It compares [q] with
    the current top position while keeping the positions above it, then
    deletes that position and keeps the remainder. The definition takes no
    bound proof; the two computation lemmas state its behavior under [q <= n]. *)

Fixpoint wgen (n q: nat) {struct n}: Word n (S n) :=
  match n with
  | 0 => wskip wnil
  | S n => if Nat.eqb q (S n) then wskip (wid (S n)) else wkeep (wgen n q)
  end.

Lemma wgenTop (n: nat): wgen n n = wskip (wid n).
Proof.
  destruct n as [|n]. now reflexivity. simpl. now rewrite natEqbRefl.
Defined.

Lemma wgenLift {n q} (Hq: q <= n): wgen (S n) q = wkeep (wgen n q).
Proof.
  simpl. now rewrite (leRNeqS q n Hq).
Defined.

(** The exchange relation for two generating cofaces, with the index shift
    accounting for the position removed by the first deletion. *)

Lemma wgenExchange: forall n q (Hq: q <= n) r (Hr: r <= q),
  wcomp (wgen (S n) r) (wgen n q)
  = wcomp (wgen (S n) (S q)) (wgen n r).
Proof.
  induction n as [|n IHn]; intros q Hq r Hr.
  - pose proof (leR0Eq Hq) as Eq; subst q.
    pose proof (leR0Eq Hr) as Er; subst r. now reflexivity.
  - destruct (Nat.eqb q (S n)) eqn:E.
    + pose proof (natEqbEq q (S n) E) as Eq; subst q.
      rewrite (wgenLift Hr), (wgenTop (S n)), (wgenTop (S (S n))).
      rewrite wcomp_keep_skip, wcomp_skip, wcompIdl, wcompIdr.
      now reflexivity.
    + assert (Hq': q <= n) by now exact (leRDown q n Hq E).
      assert (Hrn: r <= n) by now exact (Hr ↕ Hq').
      refine (_ • (f_equal wkeep (IHn q Hq' r Hr) • _)).
      * rewrite (wgenLift (↑ Hrn)), (wgenLift Hq').
        now exact (wcomp_keep_keep _ _).
      * rewrite (wgenLift (⇑ Hq')), (wgenLift Hrn).
        now exact (eq_sym (wcomp_keep_keep _ _)).
Defined.

(** Prefixing a word with the top coface is [wskip]. *)

Lemma wgenSkip {n m} (w: Word n m): wcomp (wgen m m) w = wskip w.
Proof.
  rewrite (wgenTop m). now exact (f_equal wskip (wcompIdl w)).
Defined.

(** The shift endofunctor on the opposite semi-simplicial shape category raises
    each object by one and prefixes each word with [wkeep]. It preserves
    the indices of the deleted positions. *)

Definition SemiSimplicialShapeShift: Functor (Op SemiSimplicialShape) (Op SemiSimplicialShape) :=
  Build_Functor (Op SemiSimplicialShape) (Op SemiSimplicialShape) (fun n => S n) (fun a b w => wkeep w)
    (fun a => eq_refl) (fun a b c f g => eq_sym (wcomp_keep_keep f g)).

End SemiSimplicialShape.

Arguments wskip {n m} w.
Arguments wkeep {n m} w.
Arguments wcomp {p m n} g f.
Arguments wgenSkip {n m} w.
Arguments wgenLift {n q} Hq.
Arguments wcompIdl {m n} f.
Arguments wcompIdr {n p} g.
Arguments wcompAssoc {q p m n} h g f.
Arguments wcomp_skip {m n p} g f.
Arguments wcomp_keep_skip {m n p} g f.
Arguments wcomp_keep_keep {m n p} g f.
