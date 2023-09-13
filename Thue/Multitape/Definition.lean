import Mathlib.Computability.Language
import Mathlib.Data.Prod.TProd


def List.TProd.replaceHead {ι : Type} {α : ι → Type} {d : ι} {l : List ι}
  (x : (d::l).TProd α) (v : α d) : (d::l).TProd α := ⟨v, x.snd⟩


@[reducible]
def Tapes (k : ℕ) (τ : ℕ → Type) : Type :=
  List.TProd (List ∘ τ) (List.range k)

/-- Rewrite rule -/
structure Mrule (k : ℕ) (τ : ℕ → Type) where
  inputs : Tapes k τ
  outputs : Tapes k τ

/-- Multi-tape semi-Thue system (or "multi-string rewriting system") -/
structure Multi (α : Type) where -- alphabet for words
  k : ℕ                          -- number of tapes
  k_pos : 0 < k                  -- at least one tape
  τ : ℕ → Type                   -- tape alphabets
  embed : α → τ 0                -- embedding words onto the top tape
  ruleset : List (Mrule k τ)     -- rewrite rules
  starting : Tapes k τ           -- initialization strings
  accepting : List.TProd (Option ∘ τ) (List.range k) -- accepting / halting condition(s)


variable {α : Type}

def Multi.oki (M : Multi α) {i : ℕ} (hiMk : i < M.k) : i ∈ List.range M.k := by
  rwa [List.mem_range]

/-- Initialize `M` with input `w` on which the computation should be done. -/
def Multi.initiate (M : Multi α) (w : List α) : Tapes M.k M.τ := by
  unfold Tapes
  rw [←Nat.succ_pred_eq_of_pos M.k_pos, List.range_succ_eq_map]
  apply List.TProd.replaceHead
  · rw [←List.range_succ_eq_map]
    convert M.starting
    exact Nat.succ_pred_eq_of_pos M.k_pos
  · exact (M.starting.elim (M.oki M.k_pos)).append (w.map M.embed)

/-- Does `M` consider `s` to be in accepting state? -/
def Multi.terminate (M : Multi α) (s : Tapes M.k M.τ) : Prop :=
  ∀ i : ℕ, (ok : i < M.k) →
    M.accepting.elim (M.oki ok) = none ∨ M.accepting.elim (M.oki ok) = (s.elim (M.oki ok)).head?


/-- One rewriting step. -/
def Multi.Transforms (M : Multi α) (x y : Tapes M.k M.τ) : Prop :=
  ∃ r ∈ M.ruleset, ∀ i : ℕ, (ok : i < M.k) →
    ∃ u v : List (M.τ i),
      let rᵢ : List (M.τ i) := r.inputs.elim (M.oki ok);
      let rₒ : List (M.τ i) := r.outputs.elim (M.oki ok);
      x.elim (M.oki ok) = u ++ rᵢ ++ v ∧ y.elim (M.oki ok) = u ++ rₒ ++ v

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
