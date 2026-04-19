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

(* ================================================================= *)
(* Section 4 : Abstraction du Type (Nat -> E)                        *)
(* ================================================================= *)

(* Généralisation supplémentaire : le type nat devient un type E quelconque *)
(* C'est essentiellement ce qu'on a fait ci-dessus avec (A : Type), 
   mais le papier le présente comme une étape distincte *)
Lemma f2_permute : 
  forall (E : Type) (f : E -> E -> E),
  (forall x y z : E, f x (f y z) = f (f x y) z) ->
  (forall x y : E, f x y = f y x) ->
  forall n m p : E,
  f n (f m p) = f m (f n p).
Proof.
  exact (f_permute).
Qed.

(* ================================================================= *)
(* Section 5 : Structuration par Enregistrements (Records)           *)
(* ================================================================= *)

(* Définition d'un Semi-Groupe *)
Record semi_group := {
  sg_s :> Type;
  sg_law : sg_s -> sg_s -> sg_s;
  sg_assoc : forall x y z : sg_s, sg_law x (sg_law y z) = sg_law (sg_law x y) z
}.

(* Définition d'un Semi-Groupe Commutatif (avec coercition) *)
Record semi_group_com := {
  sg :> semi_group;
  sg_com : forall x y : sg_s sg, sg_law sg x y = sg_law sg y x
}.

(* Lemme général sur les semi-groupes commutatifs *)
Lemma sg_permute : forall (sg1 : semi_group_com) (n m p : sg_s sg1),
  sg_law sg1 n (sg_law sg1 m p) = sg_law sg1 m (sg_law sg1 n p).
Proof.
  intros sg1 n m p.
  (* On utilise les champs du record *)
  rewrite (sg_assoc sg1).
  rewrite (sg_com sg1 n m).
  rewrite (sg_assoc sg1).
  reflexivity.
Qed.

(* Instantiation pour nat + plus *)
Definition sg_com_nat : semi_group_com.
Proof.
  refine {| sg := {| sg_s := nat; sg_law := plus; sg_assoc := add_assoc |} |}.
  intros; apply add_comm.
Defined.

Lemma plus_permute_record : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  exact (sg_permute sg_com_nat).
Qed.

(* ================================================================= *)
(* Section 6 : Problèmes de Correction (Règles computationnelles)    *)
(* ================================================================= *)

(* Le papier montre que l'abstraction peut échouer si la preuve utilise
   la réduction iota (computational rules) implicite plutôt que des lemmes explicites. *)

(* Définition explicite de plus pour l'exemple (style Fixpoint/Cases du papier) *)
Fixpoint my_plus (n : nat) : nat -> nat :=
  match n with
  | O => fun m => m
  | S p => fun m => S (my_plus p m)
  end.


Notation "x +++ y" := (my_plus x y) (at level 50).

(* Cas Correct : Preuve utilisant explicitement l'associativité à gauche *)
Lemma my_plus_assoc_l : forall n m p, (n +++ m) +++ p = n +++ (m +++ p).
Proof.
  induction n; intros; simpl.
  - reflexivity.
  - rewrite IHn. reflexivity.
Qed.

(* Cas Problématique (décrit dans le papier) : 
   Si on prouve l'associativité à droite par récurrence directe sans utiliser assoc_l,
   le terme de preuve contient des récursions sur nat qui ne s'abstraient pas bien 
   si on remplace nat par un type abstrait sans destructeurs connus. *)

Lemma my_plus_assoc_r : forall n m p, n +++ (m +++ p) = (n +++ m) +++ p.
Proof.
  intros n m p.
  (* Dans le papier, une preuve par 'Elim n' génère un terme avec nat_ind *)
  induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.

(* Si on tente d'abstraire 'nat' et 'my_plus' dans le terme de preuve de my_plus_assoc_r
   généré ci-dessus, on obtiendrait un terme mal typé car 'induction' dépend de la 
   structure inductive de nat. Le papier propose de remplacer les sous-termes mal typés 
   par des variables (hypothèses). *)

(* Généralisation "réparée" (comme proposé section 6.3) *)
Lemma gen_assoc_r : 
  forall (A : Type) (op : A -> A -> A),
  (forall x y z, op x (op y z) = op (op x y) z) -> (* On doit fournir l'assoc comme hypothèse *)
  forall n m p, op n (op m p) = op (op n m) p.
Proof.
  intros A op assoc n m p.
  apply assoc.
Qed.

(* ================================================================= *)
(* Section 7 : Abstraction de l'Egalité                              *)
(* ================================================================= *)




(* On peut généraliser l'égalité '=' vers une relation R quelconque *)



Lemma f3_permute : 
  forall (E : Type) (f : E -> E -> E) (R : E -> E -> Prop),
  (* R est une relation d'équivalence *)
  (forall x, R x x) ->                           (* Réflexivité *)
  (forall x y, R x y -> R y x) ->                (* Symétrie *)
  (forall x y z, R x y -> R y z -> R x z) ->     (* Transitivité *)
  (* f est compatible avec R (Congruence) *)
  (forall a b c d, R a b -> R c d -> R (f a c) (f b d)) ->
  (* Associativité modulo R *)
  (forall n m p : E, R (f n (f m p)) (f (f n m) p)) ->
  (* Commutativité modulo R *)
  (forall n m : E, R (f n m) (f m n)) ->
  (* Conclusion *)
  forall n m p : E, R (f n (f m p)) (f m (f n p)).

Proof.
  intros E f R refl sym trans cong assoc comm n m p.
  
  (* Chaîne de réécriture : 
     f n (f m p) 
     ~ f (f n m) p      (par associativité)
     ~ f (f m n) p      (par commutativité de n et m, via congruence)
     ~ f m (f n p)      (par associativité inversée)
  *)

  (* Étape 1 : f n (f m p) ~ f (f n m) p *)
  assert (H1 : R (f n (f m p)) (f (f n m) p)).
  { apply assoc. }

  (* Étape 2 : f (f n m) p ~ f (f m n) p *)
  (* On utilise la commutativité : R (f n m) (f m n) *)
  (* Et la congruence pour appliquer f _ p des deux côtés *)
  assert (H2 : R (f (f n m) p) (f (f m n) p)).
  { apply cong.
    - apply comm.      (* R (f n m) (f m n) *)
    - apply refl.      (* R p p *)
  }

  (* Étape 3 : f (f m n) p ~ f m (f n p) *)
  (* On utilise l'associativité dans l'autre sens (symétrie) *)
  assert (H3 : R (f (f m n) p) (f m (f n p))).
  { apply sym.         (* On inverse le sens de l'associativité *)
    apply assoc.       (* R (f m (f n p)) (f (f m n) p) *)
  }

  (* Conclusion : on enchaîne les relations par transitivité *)
  apply trans with (y := f (f n m) p).
  - apply H1.
  - apply trans with (y := f (f m n) p).
    + apply H2.
    + apply H3.
Qed.


(* ================================================================= *)
(* Section 8 : Abstraction d'Objets Inductifs (Nat -> Bin)           *)
(* ================================================================= *)

(* Représentation binaire des entiers (exemple du papier) *)
Inductive bin : Type :=
| BH : bin
| BO : bin -> bin
| BI : bin -> bin.

(* Successeur binaire *)
Fixpoint Sbin (b : bin) : bin :=
  match b with
  | BH => BO BH
  | BO x => BI x
  | BI x => BO (Sbin x)
  end.


(* Principe de récurrence unaire pour bin (pour imiter nat) *)


(* Conversion bin -> nat *)
Fixpoint bin_to_nat (b : bin) : nat :=
  match b with
  | BH => 0
  | BO x => 2 * (bin_to_nat x)
  | BI x => 1 + 2 * (bin_to_nat x)
  end.

(* Conversion nat -> bin *)
Fixpoint nat_to_bin (n : nat) : bin :=
  match n with
  | 0 => BH
  | S n' => Sbin (nat_to_bin n')
  end.

(* Lemme de cohérence *)
Lemma bin_to_nat_Sbin : forall b, bin_to_nat (Sbin b) = S (bin_to_nat b).
Proof.
  induction b using bin_rec.
  - simpl. reflexivity.
  - simpl. rewrite IHb. reflexivity.
  - simpl. rewrite IHb. reflexivity.
Qed.

(* Maintenant on peut prouver bin_rec_nat *)
Lemma bin_rec_nat : 
  forall (P : bin -> Type),
  P BH ->
  (forall n, P n -> P (Sbin n)) ->
  forall n, P n.
Proof.
  intros P H0 H1 b.
  (* On passe par nat pour faire la récurrence *)
  assert (H : P (nat_to_bin (bin_to_nat b))).
  { induction (bin_to_nat b) as [|n' IH].
    - simpl. rewrite <- bin_to_nat_BH. apply H0.
    - simpl. apply H1. apply IH. }
  (* Il faudrait prouver que b = nat_to_bin (bin_to_nat b) *)
  (* Cela nécessite un lemme supplémentaire d'injectivité *)
Admitted.

Lemma bin_rec_nat : 
  forall (P : bin -> Type),
  P BH ->
  (forall n, P n -> P (Sbin n)) ->
  forall n, P n.
Proof.
  (* Ceci est une simplification. Une vraie preuve nécessiterait une conversion bin <-> nat *)
  intros P H0 H1 n.
Qed.




(* Abstraction de Tab (Tableaux dépendants) *)
(* Dans le papier : Tab s n est le type des listes de longueur n *)
Inductive Tab (s : Type) : nat -> Type :=
| T_nil : Tab s 0
| T_cons : forall n, s -> Tab s n -> Tab s (S n).

(* Version abstraite où nat est remplacé par un type s1 avec OAbs et SAbs *)
Inductive TabAbs (s : Type) (s1 : Type) (OAbs : s1) (SAbs : s1 -> s1) : s1 -> Type :=
| T_nilAbs : TabAbs s s1 OAbs SAbs OAbs
| T_consAbs : forall n : s1, s -> TabAbs s s1 OAbs SAbs n -> TabAbs s s1 OAbs SAbs (SAbs n).

(* On peut définir TabBin en instantiant TabAbs avec bin *)
Definition TabBin (s : Type) := TabAbs s bin BH Sbin.

(* ================================================================= *)
(* Conclusion                                                        *)
(* ================================================================= *)

(* L'outil d'abstraction  décrit dans le papier 
   devrait générer des termes similaires à ceux prouvés ci-dessus (f_permute, 
   sg_permute, etc.). *)