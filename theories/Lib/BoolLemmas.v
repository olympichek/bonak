(** Eliminating a Boolean test while retaining its equality witness. *)

Set Warnings "-notation-overridden".
From Bonak.Lib Require Import HSet.

(** The equality witness carried by a dependent Boolean conditional is
    unique, so a supplied proof of its outcome selects the same branch. *)

Lemma boolConvoyTrue {T: Type} {b: bool} (ft: b = true -> T)
  (ff: b = false -> T) (E: b = true):
  (if b as b0 return (b = b0 -> T) then ft else ff) eq_refl = ft E.
Proof.
  revert ft ff E; destruct b; intros ft ff E.
  - now exact (f_equal ft (bool_UIP _ _ eq_refl E)).
  - now discriminate E.
Qed.

Lemma boolConvoyFalse {T: Type} {b: bool} (ft: b = true -> T)
  (ff: b = false -> T) (E: b = false):
  (if b as b0 return (b = b0 -> T) then ft else ff) eq_refl = ff E.
Proof.
  revert ft ff E; destruct b; intros ft ff E.
  - now discriminate E.
  - now exact (f_equal ff (bool_UIP _ _ eq_refl E)).
Qed.

