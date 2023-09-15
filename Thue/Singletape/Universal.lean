import Thue.Singletape.Definition

variable {α : Type}

def serializeSymbol {β : Type} (numba : α → ℕ) (numbs : β → ℕ) (x : Symbol α β) :
  List (Fin 4) :=
0 :: (match x with
  | Symbol.letter a => List.replicate (numba a).succ 1
  | Symbol.marker b => List.replicate (numbs b).succ 2
)

def serializeString {β : Type} (numba : α → ℕ) (numbs : β → ℕ) (s : List (Symbol α β)) :
  List (Fin 4) :=
0 :: (s.map (serializeSymbol numba numbs)).join

def serializeRule {β : Type} (numba : α → ℕ) (numbs : β → ℕ) (r : Rule α β) :
  List (Fin 4) :=
serializeString numba numbs r.input ++ serializeString numba numbs r.output

def System.serialize (h : System α) (numba : α → ℕ) (numbs : h.special → ℕ) :
  List (Fin 4) :=
List.replicate (numbs h.starting).succ 1 ++ List.replicate (numbs h.accepting).succ 2 ++
  (h.ruleset.map (serializeRule numba numbs)).join

def universalInstance (h : System α) (numba : α → ℕ) (numbs : h.special → ℕ) (w : List α) :
  List (Fin 4) :=
h.serialize numba numbs ++ 3 :: (w.map (fun a => 0 :: List.replicate (numba a).succ 1)).join

def langUniversal : Language (Fin 4) :=
  { s | ∃ h : System α, ∃ numba : α → ℕ, ∃ numbs : h.special → ℕ, ∃ w : List α,
    s = universalInstance h numba numbs w ∧ w ∈ h.Semidecides }
