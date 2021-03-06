Require Import Relation_Definitions.
Require Import Nat.

Section fromrodin_simple.
(*
not x |-> y: k
Q <: P
k~ [{c}]=P \ {c}
x /= y
x: Q
|-
c /= y
 *)
  (* simplified:
not y |-> x: kinv
kinv [{c}] = P \ {c}
x /= y
x: P
y: P
|-
c /= y
*)
  (* more simplified:
not y |-> x: kinv
kinv [{c}] = nat \ {c}
x /= y
x: nat
y: nat
|-
c /= y
*)
  
  Lemma cisinty:
    forall x y c: nat, forall kinv: relation nat,
      not (kinv y x) ->
      (forall e: nat, e <> c -> kinv c e) ->
      x <> y ->
      c <> y.
  Proof.
    intros x y c kinv nkinv a2 df.
    intros Heq.
    apply nkinv. clear nkinv.
    rewrite <- Heq.
    apply a2. clear a2.
    intro Heq2.
    apply df. clear df.
    apply (eq_trans Heq2 Heq).
  Qed.

  Parameter (x y c: nat).
  Parameter kinv: relation nat.

  Axiom nkinv: not (kinv y x).
  Axiom a2: forall e: nat, e <> c -> kinv c e.
  Axiom df: x <> y.

  Lemma cisnty': c <> y.
  Proof.
    intros Heq.
    apply nkinv.
    rewrite <- Heq.
    apply a2.
    intro Heq2.
    apply df.
    apply (eq_trans Heq2 Heq).
  Qed.
  
(*
Axiom df: x <> y.
Axiom comp: forall v: nat, P v. (* -> Q v.*)
Axiom nk: (x, y)  kinv.
Axiom a2: kinv {c} = nat \ {c}.
*)
End fromrodin_simple.
