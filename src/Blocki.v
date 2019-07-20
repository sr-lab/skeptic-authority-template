Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.

Require Import Coq.Lists.List.
Require Import Coq.Lists.ListSet.

Require Import Coq.QArith.QArith.


(* Import leaves this scope open. *)
Close Scope Q_scope.


(** Fundamental types (assumptions).
  *)
Section FundamentalTypes.

(** Assume that a password is a string of ASCII characters.
  *)
Definition Password := string.

End FundamentalTypes.


(** Types from Blocki et al.
  *)
Section BlockiTypes.

(** A rule, per Blocki et al. is a set of passwords.
  *)
Definition Rule := set Password.

(* No formalisation of singleton rules seems to be required. *)

(** An activation, per Blocki et al. is the index of a rule in a rule set that has been activated.
  *)
Definition Activation := nat. (* This is 1-indexed in Blocki et al. but 0-indexed here. *)

(** A policy, per Blocki et al. is a set of passwords.
  *)
Definition Policy := set Password.

End BlockiTypes.


(** Our types (moving away from infinite sets by introducing an attack model).
  *)
Section SkepticTypes.

(** A meta-rule is a mapping from a password to a Boolean.
  *)
Definition MetaRule := Password -> bool.

(** An attack is a set of (guessed) passwords.
  *)
Definition Attack := set Password.

(* Going from our types to types from Blocki et al. *)

(** Applies a meta-rule to an attack to yield a rule under that attack.
    - [a] is the attack under which to consider the meta-rule `r`
    - [r] is the meta-rule to use to form a rule under attack `a`
  *)
Definition get_rule (a : Attack) (r : MetaRule) : Rule :=
  filter r a.

(** Applies a list of meta-rules to an attack `a` to yield a list of rules under that attack.
    - [a] is the attack under which to consider the list of meta-rules `r`
    - [r] is the list of meta-rules to use to form a list of rules under attack `a`
  *)
Definition get_rule_list (a : Attack) (r : list MetaRule) : list Rule :=
  map (get_rule a) r.

End SkepticTypes.


Section Blocki.

(** Applies `nth` to a list for many indices, returning a list of results.
    - [n] is the list of indices at which to retrieve members
    - [l] is the list from which to retrieve members
    - [default] is the value to use in case an index is out of bounds
  *)
Fixpoint nths {A : Type} (n : list nat) (l : list A) (default : A) {struct n} : list A :=
  match n with
  | i :: n' => nth i l default :: nths n' l default
  | _ => nil
  end. (* TODO: Move this somewhere else. *)

(** Gets a policy using the positive scheme from a rule list given a set of rule activations.
    - [r] is the rule list from which to get concerned passwords
    - [n] is the set of rule activations to use to get concerned passwords
  *)
Definition activate (r : list Rule) (act : set Activation) : Policy :=
  fold_left (set_union string_dec) (nths act r nil) nil.

(** Gets a policy using the negative scheme from a rule list given a set of rule activations.
    - [r] is the rule list from which to get concerned passwords
    - [n] is the set of rule activations to use to get concerned passwords
  *)
Definition activate_neg (att : Attack) (r : list Rule) (act : set Activation) : Policy :=
  set_diff string_dec att (activate r act).

(** Boolean equality for ASCII characters.
    - [a] is the first character
    - [b] is the second character
  *)
Definition beq_ascii (a b : ascii) : bool :=
  beq_nat (nat_of_ascii a) (nat_of_ascii b). (* TODO: Move somewhere else. *)

(** Boolean equality for strings.
    - [a] is the first string
    - [b] is the second string
  *)
Fixpoint beq_string (a b : string) : bool :=
  match a, b with
  | String x a', String y b' => beq_ascii x y && beq_string a' b'
  | EmptyString, EmptyString => true
  | _, _ => false
  end. (* TODO: Move somewhere else. *)

(** Boolean policy compliance for password `pwd` with policy `p`.
    - [p] is the policy to check for compliance with
    - [pwd] is the password to check for compliance with `p`
  *)
Definition compliesb (p : Policy) (pwd : Password) : bool :=
  existsb (beq_string pwd) p.

Local Open Scope Q_scope.

(* So, for Pwned Passwords, the probability function `f` would count the number of occurrences of a the given password
 * in Pwned Passwords and divide this by the number of entries in Pwned Passwords in total. This yields a probabilty.
 *
 * Not all passwords are represented in the attack, so we cannot merely rank passwords in the attack as a user might
 * choose them. Users may prefer passwords that are not in the attack!
 *)

(** Calculates the probability of a password under a policy according to some function.
    - [p] is the policy under which to compute password probability
    - [f] is the probabilty calculation function
    - [pwd] is the password to compute the probability for
  *)
Definition probability (p : Policy) (f : Password -> Q) (pwd : Password) : Q :=
  if compliesb p pwd then f pwd else 0. (* Users might come in via `f`. *)

(** Calculates the probabilities of a set of passwords under a policy according to come function.
    - [p] is the policy under which to compute password probability
    - [f] is the probabilty calculation function
    - [pwds] is the set of passwords to compute the probability for
  *)
Definition probabilities (p : Policy) (f : Password -> Q) (pwds : set Password) : list Q :=
  map (probability p f) pwds.

(** Computes the sum of all probabilities for a set of passwords under a policy.
    - [p] is the policy under which to compute password probability
    - [f] is the probabilty calculation function
    - [pwds] is the set of passwords to compute the probability for
  *)
Definition sum_probabilities (p : Policy) (f : Password -> Q) (pwds : set Password) : Q :=
  fold_left Qplus (probabilities p f pwds) 0.

(* Intuitively, sum_probabilities p f pwds will yield the probability that an attacker will be able to guess a password
 * using `pwds`. [Blocki et al. 2013 p.6]
 *)

End Blocki.
