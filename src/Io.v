Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.

Require Import ListString.All.

Require Import Io.All.
Require Import Io.System.All.

Require Import Trie.

Import C.Notations.
Import ListNotations.

(** The ASCII newline character.
  *)
  Definition newline := ascii_of_nat 10.

(** Returns the text of a file as a list of lines.
    - [path] the file path to read from
  *)
Definition load_lines (path : string) : C.t effect (option (list LString.t)) :=
  let! data_opt := read_file (LString.s path) in
  match data_opt with
  | Some data =>
    let lines := Etc.split data newline in
    ret (Some lines)
  | _ => ret None
  end.

(** Returns a list of list strings as a dictionary trie supporting membership checks.
    - [lines] the list of list strings
    - [trie] the trie to build on
  *)
Fixpoint load_dict' (lines : list LString.t) (trie : Trie ascii unit) : Trie ascii unit :=
  match lines with
  | line :: lines' => load_dict' lines' (trie_insert ascii_dec trie line tt)
  | [] => trie
  end.

(** Returns the text of a file as a dictionary trie supporting membership checks.
    - [path] the path of the file to read from
  *)
Definition load_dict (path : string) : C.t effect (option (Trie ascii unit)) :=
  let! lines_opt := load_lines path in
  match lines_opt with
  | Some lines => ret (Some (load_dict' lines (empty_trie ascii unit)))
  | _ => ret None
  end.

(** Loads a lookup containing dictionaries located at the given paths.
    - [paths] the list of paths
  *)
Fixpoint load_dicts (paths : list string) : C.t effect (list (string * option (Trie ascii unit))) :=
  match paths with
  | path :: paths' =>
    let! dict_opt := load_dict path in
    let! rest := load_dicts paths' in
    ret ((path, dict_opt) :: rest)
  | [] => ret []
  end.

Fixpoint lookup {K V : Type} (dec : forall a b : K, {a = b} + {a <> b}) (ps : list (K * V)) (k : K) : option V :=
  match ps with
  | p :: ps' =>
    match dec (fst p) k with
    | left _ => Some (snd p)
    | right _ => lookup dec ps' k
    end
  | [] => None
  end.
