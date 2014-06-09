(* Modal Logics with Neighbourhood Semantics *)

(* Authors: Bruno Woltzenlogel Paleo (bruno@logic.at) *)


Require Import Modal.


(* Neighbourhood function *)
Parameter n: i -> ((i -> Prop) -> Prop).

(* Since in this HOL encoding a set is identified with its characteristic predicate,
   'truthset' is just the identity function. Therefore, it could be ommitted.
   Nevertheless, it is used here in order to conform to wikipedia's notation. *)
Definition truthset (p: o) := fun u: i => (p u).

Definition inn (p: o)(q: o -> Prop) := (q p).
Notation "p 'in' q" := (inn p q) (at level 79).

Definition subseteqn (p: o)(q: o) := (forall w: i, (p w) -> (q w)).
Notation "p 'subseteq' q" := (subseteqn p q)  (at level 79).


(* Modal operator for 'neighborhood box' *)
Definition nbox (p: o) := fun w:i => ((truthset p) in (n w)).


Definition empty_world_set (w: i) := False.

Definition full_world_set (w: i) := True.

Axiom upclosed: forall w, forall p q: o, (p in (n w)) -> (p subseteq q) -> (q in (n w)).

Axiom empty_not_in_neighbourhood: forall w: i, ~ (empty_world_set in (n w)).

Axiom full_in_neighbourhood: forall w: i, (full_world_set in (n w)).

Axiom world_set_ext : forall p1 p2, forall w:i, ((p1 w) <-> (p2 w)) -> p1 = p2.

Hint Unfold nbox truthset inn empty_world_set full_world_set subseteqn : modal.

Hint Resolve upclosed 
             empty_not_in_neighbourhood 
             full_in_neighbourhood 
             world_set_ext : modal.



Theorem necessitation: forall p, [p] -> [nbox p].
Proof.
eauto with modal.
unfold V. unfold nbox. unfold truthset. unfold inn.
firstorder with modal.
assert (p = full_world_set).
  apply world_set_ext with (w := w).
  firstorder with modal.

  rewrite H0.
  firstorder with modal.
Qed.

Theorem neg_necessitation: forall p, [m~ p] -> [m~ (nbox p)].
Proof.
unfold  V; unfold nbox; unfold truthset; unfold inn.
firstorder with modal.
assert (p = empty_world_set).
  apply world_set_ext with (w := w).
  firstorder with modal.

  rewrite H0.
  firstorder with modal.
Qed.

Theorem boxing_implication: forall p q, [p m-> q] -> [(nbox p) m-> (nbox q)].
Proof.
intros p q H.
unfold V; unfold mimplies.
intros w H1.
apply upclosed with (p := p).
  apply H1.

  firstorder with modal.
Qed.


Hint Resolve necessitation
             neg_necessitation
             boxing_implication : modal.


Theorem box_true: forall p q, [(nbox (p m/\ q)) m-> (nbox p)].
Proof.
intros p q.
apply boxing_implication.
firstorder with modal.
Qed.