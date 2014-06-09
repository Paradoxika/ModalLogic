(* Maximal Modal Logic *)

(* A logic where (dia A) is valid. *)

Require Import Modal.

Definition complete (w: i) := forall A: o, (A w) \/ ~(A w).

Axiom completeness : forall w: i, (complete w).

(* ToDo: This definition is wrong. *)
Definition consistent (B: o)(w: i) := forall A: o, (A w) -> ~ ( (m~ (A m/\ B)) w ).

Definition consistent2 (B: o)(w: i) := forall A: o, (A w) -> exists M, M models (A and B).


Definition extends (w1 w: i) := forall A:o, (A w) -> (A w1).

Definition max (w: i)(B: o) := (consistent B w) -> exists w1, (r w w1) /\ (extends w1 w) /\ (B w1) .

Axiom maximality: forall w, forall B, (max w B).


Theorem test: [ mforall A, dia A ].
Proof.
mv.
intro.
assert (max w x).
apply maximality.
unfold max in H.
cut (exists w1 : i, r w w1 /\ extends w1 w /\ x w1).
  intro H1.
  destruct H1 as [w1 [H2 [H3 H4]]].
  dia_i w1.
  exact H4.

  apply H.
  intro A.
  intro H1.
  intro H2.
  apply H2.
  split.
    exact H1.
 
assert (consistent x w).


apply maximality in w.
dia_i.