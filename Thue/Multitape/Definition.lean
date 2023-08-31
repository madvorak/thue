import Mathlib.Computability.Language
import Mathlib.Util.PiNotation
import Mathlib.Data.Fin.Tuple.Basic


def Co (α : Type) {e : ℕ} (β : Fin e → Type) : Type :=
  Π (i : Fin e.succ), List ((Fin.cons α β : Fin e.succ → Type) i)

/-- Rewrite rule -/
structure Mrule (α : Type) {e : ℕ} (β : Fin e → Type) where
  inputs : Co α β
  outputs : Co α β

/-- Multi-tape semi-Thue system (or "multi-string rewriting system") -/
structure Multi (α : Type) where -- alphabet for input tape
  e : ℕ                          -- number of extra tapes
  β : Fin e → Type               -- alphabets for extra tapes
  ruleset : List (Mrule α β)     -- rewrite rules
  starting : Π i, List (β i)     -- starting strings for extra tapes
  accepting : Π i, Option (β i)  -- accepting / halting condition(s)


variable {α : Type}

/-- Initialize `M` with input `w` on which the computation should be done. -/
def Multi.initiate (M : Multi α) (w : List α) : Co α M.β :=
  Fin.cons w M.starting

/-- Does `M` consider `s` to be in accepting state? -/
def Multi.terminate (M : Multi α) (s : Co α M.β) : Prop :=
  ∀ i : Fin M.e, M.accepting i = none ∨ M.accepting i = (s i.succ).head?


/-- One rewriting step. -/
def Multi.Transforms (M : Multi α) (x y : Co α M.β) : Prop :=
  ∃ r ∈ M.ruleset, ∀ i : Fin M.e.succ,
    ∃ u v : List ((Fin.cons α M.β : Fin M.e.succ → Type) i),
      x i = u ++ r.inputs i ++ v ∧ y i = u ++ r.outputs i ++ v

/-- Closure (reflexive+transitive) of `M.Transforms` with step counting. Predicate `M.Derives s t n` means
    the multi-tape semi-Thue system `M` can transform `s` to `t` in exactly `n` rewriting step. -/
inductive Multi.Derives (M : Multi α) : Co α M.β → Co α M.β → ℕ → Prop
  | refl (x : Co α M.β) : M.Derives x x 0
  | tail (x y z : Co α M.β) (n : ℕ) : M.Derives x y n → M.Transforms y z → M.Derives x z n.succ

/-- Language recognized by given multi-tape semi-Thue system. -/
def Multi.Semidecides (M : Multi α) : Language α :=
  { w | ∃ n : ℕ, ∃ s : Co α M.β, M.Derives (M.initiate w) s n ∧ M.terminate s }

/-- Definition of recursively-enumerable languages in terms of multi-tape semi-Thue systems. -/
def Language.InMRE (L : Language α) : Prop :=
  ∃ M : Multi α, M.Semidecides = L


/-- Related concept: https://en.wikipedia.org/wiki/Unambiguous_Turing_machine -/
def Multi.IsDeterministic (M : Multi α) : Prop :=
  ∀ w : List α, ∀ n : ℕ, ∀ s : Co α M.β, M.Derives (M.initiate w) s n →
    ∀ x y : Co α M.β, M.Transforms s x ∧ M.Transforms s y → x = y
