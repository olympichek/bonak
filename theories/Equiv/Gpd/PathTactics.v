(** Normalize compositions, inverses, and dependent-pair paths.

    The replacement tactics are parameters: each proof chooses how to
    insert the resulting transport, including whether to delay conversion
    checks through a cut. The normalization rules themselves use only
    generic path identities. *)

From Bonak Require Import SigT RewLemmas Notation.
From Bonak.Equiv.Gpd Require Import PathAlgebra.

Ltac totalMoreNormalize TC TE TM :=
  repeat match goal with
  | |- context [@eq_existT_curried ?AA ?PP] =>
    first [progress rewrite (@totalPathRew AA PP)
          |progress rewrite <- (@eq_trans_eq_existT_curried AA PP)
          |progress rewrite (@totalPathSym AA PP)
          |progress rewrite (@TC _ AA PP)
          |progress rewrite (@TE AA PP)
          |progress rewrite (@TM _ AA _ PP)]
  end.

Ltac totalMapExplicit TM :=
  repeat match goal with
  | |- context [@sigT_map_eq ?AA ?BB ?PP ?QQ ?ff ?gg ?xx ?yy ?uu ?vv ?pp ?qq] =>
    let EQ := fresh "EQmap" in
    pose proof (@TM AA BB PP QQ ff gg xx yy uu vv pp qq) as EQ;
    cbv beta in EQ;
    progress rewrite EQ; clear EQ
  end.

Ltac totalComposeExplicit :=
  repeat match goal with
  | |- context [@f_equal ?AA ?BB ?ff ?xx ?yy
       (@f_equal ?CC ?DD ?gg ?uu ?vv ?pp)] =>
    progress rewrite (@f_equal_compose CC DD BB uu vv gg ff pp)
  end.

Ltac totalFlatten replaceWith :=
  repeat match goal with
  | |- context C [@eq_trans ?A ?x ?y ?z
       (@eq_trans ?B ?u ?v ?w ?p ?q) ?r] =>
    let L := constr:(eq_sym (@eq_trans_assoc A u v w z p q r)) in
    replaceWith C L
  end.

Ltac totalReflEncode replaceWith TR :=
  repeat match goal with
  | |- context C [@eq_existT_curried ?A ?P ?x ?y ?u ?v (@eq_refl _ _) ?q] =>
    let L := constr:(@TR A P x u v q) in replaceWith C L
  end.

Ltac totalSymMaps replaceWith :=
  repeat match goal with
  | |- context C [@f_equal ?A ?B ?f ?x ?y (@eq_sym _ ?u ?v ?p)] =>
    let L := constr:(eq_sym (@eq_sym_f_equal A B f u v p)) in replaceWith C L
  end.

Ltac totalSymChains replaceWith PS :=
  repeat match goal with
  | |- context C [@eq_sym ?A ?x ?y (@eq_trans ?B ?u ?v ?w ?p ?q)] =>
    let L := constr:(@PS B u v w p q) in replaceWith C L
  end.

Ltac totalFinishNegativeSafe replaceWith TF :=
  repeat match goal with
  | |- context C [@eq_existT_curried ?A ?P ?x ?y ?u ?v ?p
       (@eq_sym ?B ?a ?b ?q)] =>
    lazymatch p with
    | @eq_refl _ _ => fail
    | _ => let L := constr:(@TF A P x y u v p (@eq_sym B a b q)) in
      replaceWith C L
    end
  end.

Ltac totalCancel replaceWith PR :=
  repeat first
  [ match goal with
    | |- context C [@eq_trans ?A ?x ?y ?z (@eq_sym _ ?u ?v ?p)
         (@eq_trans _ _ _ _ ?p0 ?q)] =>
      unify p p0;
      let L := constr:(@eq_trans_sym_cancel_l A u v z p q) in replaceWith C L
    end
  | match goal with
    | |- context C [@eq_trans ?A ?x ?y ?z ?p
         (@eq_trans _ _ _ _ (@eq_sym _ ?u ?v ?p0) ?q)] =>
      unify p p0;
      let L := constr:(@PR A u v z p q) in replaceWith C L
    end
  | match goal with
    | |- context C [@eq_sym ?A ?x ?y (@eq_sym _ ?u ?v ?p)] =>
      let L := constr:(@eq_sym_involutive A u v p) in replaceWith C L
    end ].

Ltac totalComposeContext replaceWith :=
  repeat match goal with
  | |- context C [@f_equal ?AA ?BB ?ff ?xx ?yy
       (@f_equal ?CC ?DD ?gg ?uu ?vv ?pp)] =>
    let L := constr:(@f_equal_compose CC DD BB uu vv gg ff pp) in
    replaceWith C L
  end.

Ltac totalMapChains replaceWith :=
  repeat match goal with
  | |- context C [@f_equal ?A ?B ?f ?x ?y (@eq_trans _ ?u ?v ?w ?p ?q)] =>
    let L := constr:(@eq_trans_map_distr A B u v w f p q) in replaceWith C L
  end.

Ltac totalNormalizeHyp replaceWith H TM TR :=
  repeat match type of H with
  | context C [@eq_existT_curried ?A ?P ?x ?y ?u ?v ?p ?q] =>
    first
    [ lazymatch q with
      | @sigT_trans_eq ?A0 ?P0 ?x0 ?y0 ?z0 ?u0 ?v0 ?w0 ?p0 ?q0 ?p1 ?q1 =>
        let L := constr:(eq_sym (@eq_trans_eq_existT_curried A0 P0 x0 y0 z0 u0 v0 w0 p0 q0 p1 q1)) in
        replaceWith H C L
      end
    | lazymatch q with
      | @sigT_map_eq ?A0 ?B0 ?P0 ?Q0 ?f0 ?g0 ?x0 ?y0 ?u0 ?v0 ?p0 ?q0 =>
        let L := constr:(@TM A0 B0 P0 Q0 f0 g0 x0 y0 u0 v0 p0 q0) in
        replaceWith H C L
      end
    | lazymatch q with
      | @eq_trans ?T0 ?a0 ?b0 ?c0 ?q0 ?r0 =>
        let L := constr:(@TR A P x y u b0 v p q0 r0) in replaceWith H C L
      end
    | lazymatch q with
      | @projT2_eq ?A0 ?P0 ?u0 ?v0 ?h0 =>
        let L := constr:(@totalPathReencode A0 P0 u0 v0 h0) in replaceWith H C L
      end ]
  end.
