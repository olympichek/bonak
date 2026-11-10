(** Telescope limits with a contractible initial stage are sequential limits. *)

Set Warnings "-notation-overridden".
From Bonak.Lib Require Import SigT Notation LeSProp Equiv Contractible Limit SequentialLimit.

Set Primitive Projections.
Set Printing Projections.

Definition limitToSequential {T: Telescope} {s: T.(stage) 0}
  (L: Limit T 0 s): SequentialLimit T.(stage) (fun n => @bond T n) :=
  (fun n => L.(approx) n leR_O;
   fun n => L.(approxS) n leR_O leR_O).

Section ContractibleInitialStage.
Context (T: Telescope) (s: T.(stage) 0) (c: Contr (T.(stage) 0)).

Definition sequentialToLimit (X: SequentialLimit T.(stage) (fun n => @bond T n)):
  Limit T 0 s :=
  @limit T 0 s (fun n _ => X.1 n)
    (eq_sym (c.2 (X.1 0)) • c.2 s) (fun n _ _ => X.2 n).

Lemma sequentialToFromLimit (L: Limit T 0 s):
  sequentialToLimit (limitToSequential L) = L.
Proof.
  destruct L as [a o h]. unfold sequentialToLimit, limitToSequential; cbn.
  assert (e: eq_sym (c.2 (a 0 leR_O)) • c.2 s = o) by now apply (contrUIP c).
  now destruct e.
Defined.

Lemma limitToFromSequential (X: SequentialLimit T.(stage) (fun n => @bond T n)):
  limitToSequential (sequentialToLimit X) = X.
Proof. now reflexivity. Defined.

Definition telescopeLimitEquiv:
  Equiv (Limit T 0 s) (SequentialLimit T.(stage) (fun n => @bond T n)) :=
  qinvEquiv limitToSequential sequentialToLimit sequentialToFromLimit limitToFromSequential.

End ContractibleInitialStage.
