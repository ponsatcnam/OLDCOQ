(** 
    Adaptation des exemples du papier :
    "Generalization in Type Theory Based Proof Assistants"
    Olivier Pons, TYPES 2000.
    
    Ce fichier teste la validité des généralisations proposées dans le papier
    sur une version moderne de Coq (Rocq).
*)

Require Import Arith Logic.

Open Scope nat_scope.
Import Nat.

(* Section 2.1 : Abstraction d'un opérateur (Mult -> F)              *)
(* ================================================================= *)

(* Théorème de base sur la multiplication (exemple du papier) *)
Lemma mult_permute : forall n m p : nat, n * (m * p) = m * (n * p).
Proof.
  intros n m p.
  rewrite mul_assoc.
  rewrite (mul_comm n m).
  rewrite  mul_assoc.
  reflexivity.
Qed.

(* Généralisation manuelle (résultat attendu par l'outil du papier) *)
(* On abstrait 'mult' par 'f', et on ajoute les hypothèses d'associativité et commutativité *)
Lemma f_permute : 
  forall (A : Type) (f : A -> A -> A),
  (forall x y z : A, f x (f y z) = f (f x y) z) ->  (* Associativité *)
  (forall x y : A, f x y = f y x) ->                (* Commutativité *)
  forall n m p : A,
  f n (f m p) = f m (f n p).
Proof.
  intros A f assoc comm n m p.
  rewrite assoc.
  rewrite (comm n m).
  rewrite  assoc.
  reflexivity.
Qed.

(* Instantiation avec l'addition (Section 2.2) *)
Lemma plus_permute_inst : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  (* On applique le théorème généralisé f_permute avec plus, plus_assoc et plus_comm *)
  apply (f_permute nat plus add_assoc add_comm).
Qed.
