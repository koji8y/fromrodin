Require Import Relation_Definitions.
(* Require Import Nat. *)

Section fromrodin.
(* ↓ 元のシーケント
not x |-> y: k
Q <: P
k~ [{c}]=P \ {c}
x /= y
x: Q
|-
c /= y
 *)
  (* simplified:
   ↓ 少し単純化したシーケント
not y |-> x: kinv
kinv [{c}] = P \ {c}
x /= y
x: P
y: P
|-
c /= y
*)
  Parameter someSet: Set (* someSet is, for examle, nat.*).
  Parameter propForP: someSet -> Prop.
  Definition P:= {x: someSet | propForP x} (* equiv to sig prppForP *).

  (* 上記シーケントの証明 *)
  Lemma c_isnot_y:
    forall kinv: relation P, forall x y c: P,
      not (kinv y x) ->
      (forall e: P, e <> c -> kinv c e) ->
      x <> y ->
      c <> y.
  Proof.
    intros kinv x y c nkinv a2 df.
    intros Heq.
    apply nkinv.
    rewrite <- Heq.
    apply a2.
    intro Heq2.
    apply df.
    apply (eq_trans Heq2 Heq).
  Qed.
    
  Parameter kinv: relation P.

  (* x ∈ P
     y ∈ P
     c ∈ P *)
  Parameter x y c: P.
  (* ¬ y |-> x: k~ *)
  Axiom nkinv: not (kinv y x).
  (* k~[{c}] = P \ {c} *)
  Axiom a2: forall e: P, e <> c -> kinv c e.
  (* x ≠ y *)
  Axiom df: x <> y.

  (* c ≠ y の証明 *)
  Lemma c_isnot_y': c <> y.
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
