import Mathlib.Computability.Language
import Mathlib.Data.Prod.TProd


@[reducible]
def Tapes (k : ℕ) (τ : ℕ → Type) : Type :=
  List.TProd (List ∘ τ) (List.range k)

/-- Rewrite rule -/
structure Mrule (k : ℕ) (τ : ℕ → Type) where
  inputs : Tapes k τ
  outputs : Tapes k τ

/-- Multi-tape semi-Thue system (or "multi-string rewriting system") -/
structure Multi (α : Type) where    -- alphabet for words
  k : ℕ                             -- number of tapes
  τ : ℕ → Type                      -- tape alphabets
  embed : α → τ 0                   -- embedding words onto the top tape
  ruleset : List (Mrule k τ)        -- rewrite rules
  starting : Tapes k τ              -- initialization strings
  accepting : List.TProd (Option ∘ τ) (List.range k) -- accepting / halting condition(s)


variable {α : Type}

/-- Initialize `M` with input `w` on which the computation should be done. -/
def Multi.initiate (M : Multi α) (w : List α) : Tapes M.k M.τ :=
M.starting -- Function.update M.starting 0 (M.starting 0 ++ w.map M.embed) -- TODO

/-- Does `M` consider `s` to be in accepting state? -/
def Multi.terminate (M : Multi α) (s : Tapes M.k M.τ) : Prop :=
  ∀ i : ℕ, (ok : i < M.k) →
sorry --    M.accepting i = none ∨ M.accepting i = (s.elim (Iff.mpr List.mem_range ok)).head?


/-- One rewriting step. -/
def Multi.Transforms (M : Multi α) (x y : Tapes M.k M.τ) : Prop :=
  ∃ r ∈ M.ruleset, ∀ i : ℕ, (ok : i < M.k) →
    ∃ u v : List (M.τ i),
      let oki := Iff.mpr List.mem_range ok;
      let rᵢ : List (M.τ i) := r.inputs.elim oki;
      let rₒ : List (M.τ i) := r.outputs.elim oki;
      x.elim oki = u ++ rᵢ ++ v ∧ y.elim oki = u ++ rₒ ++ v

/-- Closure (reflexive+transitive) of `M.Transforms` with step counting. Predicate `M.Derives s t n` means
    the multi-tape semi-Thue system `M` can transform `s` to `t` in exactly `n` rewriting step. -/
inductive Multi.Derives (M : Multi α) : Tapes M.k M.τ → Tapes M.k M.τ → ℕ → Prop
  | refl (x : Tapes M.k M.τ) : M.Derives x x 0
  | tail (x y z : Tapes M.k M.τ) (n : ℕ) : M.Derives x y n → M.Transforms y z → M.Derives x z n.succ

/-- Language recognized by given multi-tape semi-Thue system. -/
def Multi.Semidecides (M : Multi α) : Language α :=
  { w | ∃ n : ℕ, ∃ s : Tapes M.k M.τ, M.Derives (M.initiate w) s n ∧ M.terminate s }

/-- Definition of recursively-enumerable languages in terms of multi-tape semi-Thue systems. -/
def Language.InMRE (L : Language α) : Prop :=
  ∃ M : Multi α, M.Semidecides = L


/-- Semantic definition of deterministic computation. -/
def Multi.IsDeterministic (M : Multi α) : Prop :=
  ∀ w : List α, ∀ n : ℕ, ∀ s : Tapes M.k M.τ, M.Derives (M.initiate w) s n →
    ∀ x y : Tapes M.k M.τ, M.Transforms s x ∧ M.Transforms s y → x = y
