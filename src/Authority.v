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

Fixpoint complies_all (rules : list MetaRule) (pwd : string) : bool :=
  match rules with
  | rule :: rules' => rule pwd && complies_all rules' pwd
  | _ => true
  end.

Fixpoint determine (rules : list MetaRule) (n : nat) : C.t System.effect unit :=
  match n with
  | S n' =>
    let! pwd_in := System.read_line in
    match pwd_in with
    | None => ret tt
    | Some pwd_in' =>
      let pwd := LString.to_string pwd_in' in
      let msg := if complies_all rules pwd then "true" else "false" in
      do! System.log (LString.s msg) in
      determine rules n'
    end
  | Z => ret tt
  end.

Definition lookup_config (name : string) : option Configuration :=
  match name with
  {{ config_lookups }}
  | _ => None
  end.

Definition authority (argv : list LString.t) : C.t System.effect unit :=
  match argv with
  | _ :: config_name :: count :: [] =>
    match lookup_config (LString.to_string config_name) with
      | Some config =>
        determine (transform config) (nat_of_string (LString.to_string count))
      | None => ret tt
    end
  | _ => ret tt
  end.


Definition main := Extraction.launch authority.
Extraction "authority" main.
