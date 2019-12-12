From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* This is a scratch pad for dealing with Chapter 2 of Using Z: Specification, Refinement, Proof *)
Theorem and_comm : forall P Q : Prop, P /\ Q -> Q /\ P.
Proof.
  intros P Q [HP HQ].
  split.
  - apply HQ.
  - apply HP.
Qed.


(* Here's an attempt to redo it using SSReflect *)
Theorem and_comm' : forall P Q : Prop, P /\ Q -> Q /\ P.
Proof.
  move => P Q [HP HQ].
  by split.
Qed.


Theorem disj_comm : forall P Q : Prop, P \/ Q -> Q \/ P.
Proof.
  intros P Q H.
  destruct H. right. apply H.
  left. apply H.
Qed.

(* and here's disj_comm in ssreflect *)
Lemma disj_comm' : forall P Q : Prop, P \/ Q -> Q \/ P.
Proof. move => P Q. by case; [right | left]. Qed.

(* Here's another proof from Using Z *)
Theorem paqir_implies_piqir : forall P Q R : Prop, (P /\ Q -> R) -> (P -> (Q -> R)).
Proof.
  intros P Q R H HP HQ.
  assert (HPQ: P /\ Q).
  split. exact HP. exact HQ.
  pose (HR := H HPQ).
  exact HR.
  (* I worry this is on the ugly side for what I'm trying to do. *)
Qed.

(* These two were stolen from a tutorial *)

Theorem backward_small : (forall A B : Prop,  A -> (A -> B) -> B).
Proof.
  intros A B.
  intros proof_of_A A_implies_B.
  refine (A_implies_B _).
  exact proof_of_A.
Qed.

Theorem forward_small : forall A B : Prop, A -> (A -> B) -> B.
Proof.
  intros A B proof_of_A A_implies_B.
  pose (proof_of_B := A_implies_B proof_of_A).
  exact proof_of_B.
Qed.
