(** Transport of a map along equivalences of its domain and codomain.
    Mere surjectivity of the transported map is equivalent to mere
    surjectivity of the original one. *)
Set Warnings "-notation-overridden".
From Bonak.Lib Require Import HSet SigT Equiv Notation Truncation.
Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Module CompletionTransport (Tr: PropositionalTruncation).
  Import Tr.
  Module TF := TruncationFacts Tr.

  Section TransportMap.
  Context {S S' W W': Type} (eS: Equiv S' S) (eW: Equiv W' W) (c: S -> W).

  Definition transportMap (x: S'): W' := invEq eW (c (eS x)).

  Definition transportMapSurjective
    (surjective: forall y', merely {x': S' &T transportMap x' = y'}):
    forall y, merely {x: S &T c x = y}.
  Proof.
    intro y. refine (TF.trMap _ (surjective (invEq eW y))).
    intros [x' e]. exists (eS x').
    now exact (eq_sym (secEq eW (c (eS x'))) • (f_equal eW e • secEq eW y)).
  Defined.

  Definition surjectiveTransportMap
    (surjective: forall y, merely {x: S &T c x = y}):
    forall y', merely {x': S' &T transportMap x' = y'}.
  Proof.
    intro y'. refine (TF.trMap _ (surjective (eW y'))).
    intros [x e]. exists (invEq eS x).
    now exact (f_equal (fun s => invEq eW (c s)) (secEq eS x)
      • (f_equal (invEq eW) e • retEq eW y')).
  Defined.

  Definition transportMapSurjectiveEquiv:
    Equiv (forall y', merely {x': S' &T transportMap x' = y'})
      (forall y, merely {x: S &T c x = y}) :=
    qinvEquiv transportMapSurjective surjectiveTransportMap
      (fun _ => piHProp (fun y' => merelyProp _) _ _)
      (fun _ => piHProp (fun y => merelyProp _) _ _).

  End TransportMap.
End CompletionTransport.
