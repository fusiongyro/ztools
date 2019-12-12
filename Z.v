From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* This is a scratch pad for dealing with Chapter 2 of Using Z: Specification, Refinement, Proof *)
Theorem and_comm : forall P Q : Prop, P /\ Q -> Q /\ P.
Proof.
  (* TYLER: Ok, I'm doing this in CoqIDE, like a god-damn Caveman... 
            I switched to vim a while ago, and I just really dont want
            to jack with anything.

            So before I critique (hmm, no spelling... just bare with me)
            let's just write this out by hand:
       Assuming I know P and Q, can I show Q and P?
         to show Q and P, I must first show Q, then P
         I know Q
         I know P
         QED.

      What does this look like in Coq?*)
  intros P Q [HP HQ].
  split.
  - apply HQ.
  - apply HP.
Qed.


(* Here's an attempt to redo it using SSReflect *)
Theorem and_comm' : forall P Q : Prop, P /\ Q -> Q /\ P.
Proof.
  (* TYLER: Yeah, I've... literally never used ssreflect before, so
            reading up really quick...
  *)
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
Theorem disj_comm' : forall P Q : Prop, P \/ Q -> Q \/ P.
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

(* TYLER: Yeah, that was ugly. Let me try: *)
Theorem paqir_implies_piqir' : forall P Q R : Prop, (P /\ Q -> R) -> (P -> (Q -> R)).
Proof.
  intros P Q R H HP HQ.
  assert (HPQ: P /\ Q). split. exact HP. exact HQ.
  apply H. exact HPQ.
Qed.
(* TYLER: So I have never used pose before. Seems fine. So bassically the same *)

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
