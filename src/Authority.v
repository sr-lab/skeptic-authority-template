Require Import Coq.Lists.List.
Require Import Io.All.
Require Import Io.System.All.
Require Import ListString.All.

Require Import NumberRendering.
Require Import Blocki.

Import ListNotations.
Import C.Notations.


Definition Configuration : Type :=
  ({{ config_params }}).

Definition transform (config : Configuration) : list MetaRule :=
  [].

Fixpoint determine (n : nat) : C.t System.effect unit :=
  match n with
  | S n' =>
    let! pwd := System.read_line in
    do! System.log (LString.s "") in
    determine n'
  | Z =>
    System.log (LString.s "End of input.")
  end.

Definition lookup_config (name : string) : Maybe Configuration :=
  match name with
  {{ config_lookups }}
  | _ => Nothing
  end.

Definition authority (argv : list LString.t) : C.t System.effect unit :=
  (* Take count, take policy name. *)
  (* TODO: Look up name, transform it, apply it. *)
  determine 10.

Definition main := Extraction.launch authority.
Extraction "extraction/authority" main.
