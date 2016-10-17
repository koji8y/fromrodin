Require Import Nat.

Eval compute in (1, 2).
Section fromrodin.
(*
not x |-> y: k
Q <: P
k~ [{c}]=P \ {c}
x /= y
x: Q
|-
c /= y
 *)
  (*
not y |-> x: kinv
kinv [{c}] = P \ {c}
x /= y
x: P
y: P
|-
c /= y
*)
  
Parameter (x y c: nat).
Parameter kinv: nat * nat.
Definition P (v: nat): Prop.
Definition Q (v: nat): Prop.
  
Axiom df: x <> y.
Axiom comp: forall v: nat, P v. (* -> Q v.*)
Axiom nk: (x, y)  kinv.
Axiom a2: kinv {c} = nat \ {c}.
