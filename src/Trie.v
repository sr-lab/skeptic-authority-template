Require Import Coq.Lists.List.

Import ListNotations.

Set Implicit Arguments.

(** Generic search trees (tries) over a list of any type with decidable equality.
  *)
Section Trie.

  (** The type of key portions in the trie.

      For instance, for a trie of strings, this would be the ASCII character type.
    *)
  Variable K : Type.

  (** The type of values in the trie.
    *)
  Variable V : Type.

  (** In order to retrieve values from the trie, the key portion type must have decidable equality.
    *)
  Hypothesis Keq_dec : forall x y : K, {x = y} + {x <> y}.

  (** Represents a trie.
    *)
  Inductive Trie := Root : option V -> list Trie -> Trie
    | Node : option V -> K -> list Trie -> Trie.

  (** The empty trie.
    *)
  Definition empty_trie := Root None [].

  (** Checks if a trie is associated with the specified key portion.
      - [t] is the trie
      - [k] is the key portion
    *)
  Definition is_sought_trie (t : Trie) (k : K) : bool :=
    match t with
    | Root _ _ => false
    | Node _ k' _ =>
        match Keq_dec k k' with
        | left _ => true
        | right _ => false
        end
    end.

  (** Gets the trie from a list of tries associated with the specified key portion.
      - [ts] is the list of tries
      - [k] is the key portion
    *)
  Fixpoint get_trie (ts : list Trie) (k : K) : option Trie :=
    match ts with
    | t :: ts' =>
        if is_sought_trie t k then
          Some t
        else
          get_trie ts' k
    | [] => None
    end.

  (** Checks if a tries contains a trie with the specified key portion.
      - [ts] is the list of tries
      - [k] is the key portion
    *)
  Definition has_trie (ts : list Trie) (k : K) : bool :=
    match get_trie ts k with
    | Some t => true
    | None => false
    end.

  (** Gets the data associated with the given key in the specified trie.
      - [ts] is the list of tries
      - [ks] is the key
    *)
  Fixpoint trie_get (t : Trie) (ks : list K) : option V :=
    match t, ks with
    | Root _ c, k :: ks'
    | Node _ _ c, k :: ks' =>
        match get_trie c k with
        | Some t => trie_get t ks'
        | None => None
        end
    | Root v c, []
    | Node v _ c, [] => v
    end.

  (** Returns true if a trie contains the given key, otherwise false.
      - [t] is the trie
      - [ks] is the key
    *)
  Definition trie_contains (t : Trie) (ks : list K) : bool :=
    match trie_get t ks with
    | Some _ => true
    | _ => false
    end.

  (** Removes the trie from a list that contains the given key portion.
      - [ts] is the list of tries
      - [k] is the key portion
    *)
  Definition remove_trie (ts : list Trie) (k : K) : list Trie :=
    match ts with
    | t :: ts' =>
        if is_sought_trie t k then
          ts'
        else
          t :: ts'
    | [] => []
    end.

  (** Inserts a value into a trie.
      - [t] is the trie
      - [ks] is the key
      - [ks] is the key
    *)
  Fixpoint trie_insert (t : Trie) (ks : list K) (v : V) : Trie :=
    match t, ks with
    | Root _ c, [] =>
        Root (Some v) c
    | Root v' c, k :: ks' =>
        match get_trie c k with
        | Some t' =>
            Root v' ((trie_insert t' ks' v) :: (remove_trie c k))
        | None => Root v' ((trie_insert (Node None k []) ks' v) :: c)
        end
    | Node _ k' c, [] => Node (Some v) k' c
    | Node v' k' c, k :: ks' =>
      match get_trie c k with
      | Some t' =>
          Node v' k' ((trie_insert t' ks' v) :: (remove_trie c k))
      | None => Node v' k' ((trie_insert (Node None k []) ks' v) :: c)
      end
    end.

End Trie.
