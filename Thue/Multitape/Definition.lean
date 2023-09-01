import Mathlib.Computability.Language
import Mathlib.Util.PiNotation
import Mathlib.Data.Fin.Tuple.Basic


def Co {k : ℕ} (β : Fin k → Type) : Type :=
  Π i : Fin k, List (β i)

/-- Rewrite rule -/
structure Mrule {k : ℕ} (β : Fin k → Type) where
  inputs : Co β
  outputs : Co β

/-- Multi-tape semi-Thue system (or "multi-string rewriting system") -/
structure Multi (α : Type) where        -- alphabet for words
  k : ℕ                                 -- number of tapes
  k_pos : NeZero k                      -- at least one tape
  β : Fin k → Type                      -- tape alphabets
  embed : α → β 0                       -- embedding words onto the input tape
  ruleset : List (Mrule β)              -- rewrite rules
  starting : Co β                       -- initialization strings
  accepting : Π i : Fin k, Option (β i) -- accepting / halting condition(s)


variable {α : Type}

/-- Initialize `M` with input `w` on which the computation should be done. -/
def Multi.initiate (M : Multi α) (w : List α) : Co M.β :=
  let _ : NeZero M.k := M.k_pos ;
  Function.update M.starting 0 (M.starting 0 ++ w.map M.embed)

/-- Does `M` consider `s` to be in accepting state? -/
def Multi.terminate (M : Multi α) (s : Co M.β) : Prop :=
  ∀ i : Fin M.k, M.accepting i = none ∨ M.accepting i = (s i).head?


/-- One rewriting step. -/
def Multi.Transforms (M : Multi α) (x y : Co M.β) : Prop :=
  ∃ r ∈ M.ruleset, ∀ i : Fin M.k,
    ∃ u v : List (M.β i), x i = u ++ r.inputs i ++ v ∧ y i = u ++ r.outputs i ++ v

/-- Closure (reflexive+transitive) of `M.Transforms` with step counting. Predicate `M.Derives s t n` means
    the multi-tape semi-Thue system `M` can transform `s` to `t` in exactly `n` rewriting step. -/
inductive Multi.Derives (M : Multi α) : Co M.β → Co M.β → ℕ → Prop
  | refl (x : Co M.β) : M.Derives x x 0
  | tail (x y z : Co M.β) (n : ℕ) : M.Derives x y n → M.Transforms y z → M.Derives x z n.succ

/-- Language recognized by given multi-tape semi-Thue system. -/
def Multi.Semidecides (M : Multi α) : Language α :=
  { w | ∃ n : ℕ, ∃ s : Co M.β, M.Derives (M.initiate w) s n ∧ M.terminate s }

/-- Definition of recursively-enumerable languages in terms of multi-tape semi-Thue systems. -/
def Language.InMRE (L : Language α) : Prop :=
  ∃ M : Multi α, M.Semidecides = L


/-- Related concept: https://en.wikipedia.org/wiki/Unambiguous_Turing_machine -/
def Multi.IsDeterministic (M : Multi α) : Prop :=
  ∀ w : List α, ∀ n : ℕ, ∀ s : Co M.β, M.Derives (M.initiate w) s n →
    ∀ x y : Co M.β, M.Transforms s x ∧ M.Transforms s y → x = y
