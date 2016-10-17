Require Import Relation_Definitions.
Require Import Nat.

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
  (* simplified:
not y |-> x: kinv
kinv [{c}] = P \ {c}
x /= y
x: P
y: P
|-
c /= y
*)
  Parameter someType: Type (* someType is, for examle, nat.*).
  Parameter propForP: someType -> Prop.
  Definition P:= {x: someType | propForP x}.
  Parameter kinv: relation P.

  (* x $B":(B P *)
  (* y $B":(B P *)
  (* c $B":(B P *)
  Parameter x y c: P.
  (* $B"L(B y |-> x: k~ *)
  Axiom nkinv: not (kinv y x).
  (* k~[{c}] = P \ {c} *)
  Axiom a2: forall e: P, e <> c -> kinv c e.
  (* x $B!b(B y *)
  Axiom df: x <> y.

  (* c $B!b(B y *)
  Lemma c_isnot_y: c <> y.
  Proof.
    intros Heq.
    apply nkinv.
    rewrite <- Heq.
    apply a2.
    intro Heq2.
    apply df.
    apply (eq_trans Heq2 Heq).
  Qed.
End fromrodin.
