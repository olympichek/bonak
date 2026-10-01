(** Eliminating a Boolean test while retaining its equality witness. *)

Set Warnings "-notation-overridden".

(** Path induction on a supplied equality selects the matching branch
    and its equality witness together. *)

Lemma boolConvoyTrue {T: Type} {b: bool} (ft: b = true -> T)
  (ff: b = false -> T) (E: b = true):
  (if b as b0 return (b = b0 -> T) then ft else ff) eq_refl = ft E.
Proof. now subst b. Qed.

Lemma boolConvoyFalse {T: Type} {b: bool} (ft: b = true -> T)
  (ff: b = false -> T) (E: b = false):
  (if b as b0 return (b = b0 -> T) then ft else ff) eq_refl = ff E.
Proof. now subst b. Qed.

