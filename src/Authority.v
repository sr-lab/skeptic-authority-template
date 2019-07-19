Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Io.All.
Require Import Io.System.All.
Require Import ListString.All.

Require Import NumberRendering.
Require Import Blocki.

Import ListNotations.
Import C.Notations.

Open Scope string_scope.

Definition Configuration : Type :=
  ({{ config_params }}).

Definition transform (config : Configuration) : list MetaRule :=
  [].

Fixpoint complies_all (mr : list MetaRule) (p : string) : bool :=
  match mr with
  | x :: mr' => x p && complies_all mr' p
  | _ => true
  end.

Fixpoint determine (p : list MetaRule) (n : nat) : C.t System.effect unit :=
  match n with
  | S n' =>
    let! pwd := System.read_line in
    match pwd with
    | None => ret tt
    | Some pwd' =>
    do! System.log (if complies_all p (LString.to_string pwd') then (LString.s "permitted") else (LString.s "Prohibited")) in
          determine p n'
    end
  
  | Z =>
    System.log (LString.s "End of input.")
  end.

Definition lookup_config (name : string) : option Configuration :=
  match name with
  {{ config_lookups }}
  | _ => None
  end.

Definition authority (argv : list LString.t) : C.t System.effect unit :=
  match argv with
  | _ :: policy :: count :: [] =>
    match lookup_config (LString.to_string policy) with
      | Some dd =>
        determine (transform dd) (nat_of_string (LString.to_string count))
      | None => ret tt
    end
  | _ => ret tt
  end.


Definition main := Extraction.launch authority.
Extraction "authority" main.
