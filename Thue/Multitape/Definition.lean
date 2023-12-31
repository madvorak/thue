import Mathlib.Computability.Language
import Mathlib.Data.Prod.TProd

def List.TProd.replaceHead {ι : Type} {α : ι → Type} {d : ι} {l : List ι}
  (x : (d::l).TProd α) (v : α d) : (d::l).TProd α :=
⟨v, x.snd⟩


section defStructures

def Tapes (e : ℕ) (τ : ℕ → Type) : Type :=
  List.TProd (List ∘ τ) (List.range e.succ)

/-- Rewrite rule -/
structure Mrule (e : ℕ) (τ : ℕ → Type) where
  inputs : Tapes e τ
  outputs : Tapes e τ

/-- Multi-tape semi-Thue system (or "multi-string rewriting system") -/
structure Multi (α : Type) where -- alphabet for words
  e : ℕ                          -- number of extra tapes
  τ : ℕ → Type                   -- tape alphabets
  embed : α → τ 0                -- embedding words onto the top tape
  ruleset : List (Mrule e τ)     -- rewrite rules
  starting : Tapes e τ           -- initialization strings
  accepting : List.TProd (Option ∘ τ) (List.range e.succ)

end defStructures


def Tapes.toTProdCons {e : ℕ} {τ : ℕ → Type} :
  Tapes e τ → List.TProd (List ∘ τ) (0 :: (List.range e).map Nat.succ) :=
cast (congr_arg (List.TProd (List ∘ τ)) (List.range_succ_eq_map e))

def tapesOfTProdCons {e : ℕ} {τ : ℕ → Type} :
  List.TProd (List ∘ τ) (0 :: (List.range e).map Nat.succ) → Tapes e τ :=
cast (congr_arg (List.TProd (List ∘ τ)) (List.range_succ_eq_map e).symm)

variable {α : Type}

def Multi.oki (M : Multi α) {i : ℕ} (hiMk : i ≤ M.e) : i ∈ List.range M.e.succ := by
  rwa [List.mem_range, Nat.lt_succ]

/-- Initialize `M` with input `w` on which the computation should be done. -/
def Multi.initialize (M : Multi α) (w : List α) : Tapes M.e M.τ :=
  tapesOfTProdCons (List.TProd.replaceHead M.starting.toTProdCons
      ((M.starting.elim (M.oki (Nat.zero_le M.e))).append (w.map M.embed)))

/-- Does `M` consider `s` to be in accepting state? -/
def Multi.terminate (M : Multi α) (s : Tapes M.e M.τ) : Prop :=
  ∀ i : ℕ, (ok : i ≤ M.e) →
    M.accepting.elim (M.oki ok) = none ∨ M.accepting.elim (M.oki ok) = (s.elim (M.oki ok)).head?


section defPredicates

/-- One rewriting step. -/
def Multi.Transforms (M : Multi α) (x y : Tapes M.e M.τ) : Prop :=
  ∃ r ∈ M.ruleset, ∀ i : ℕ, (ok : i ≤ M.e) →
    ∃ u v : List (M.τ i),
      let rᵢ : List (M.τ i) := r.inputs.elim (M.oki ok);
      let rₒ : List (M.τ i) := r.outputs.elim (M.oki ok);
      x.elim (M.oki ok) = u ++ rᵢ ++ v ∧ y.elim (M.oki ok) = u ++ rₒ ++ v

/-- Closure (reflexive+transitive) of `M.Transforms` with step counting. Predicate `M.Derives s t n` means
    the multi-tape semi-Thue system `M` can transform `s` to `t` in exactly `n` rewriting step. -/
inductive Multi.Derives (M : Multi α) : Tapes M.e M.τ → Tapes M.e M.τ → ℕ → Prop
  | refl (x : Tapes M.e M.τ) : M.Derives x x 0
  | tail (x y z : Tapes M.e M.τ) (n : ℕ) : M.Derives x y n → M.Transforms y z → M.Derives x z n.succ

/-- Language recognized by given multi-tape semi-Thue system. -/
def Multi.Semidecides (M : Multi α) : Language α :=
  { w | ∃ n : ℕ, ∃ s : Tapes M.e M.τ, M.Derives (M.initialize w) s n ∧ M.terminate s }

/-- Definition of recursively-enumerable languages in terms of multi-tape semi-Thue systems. -/
def Language.InMRE (L : Language α) : Prop :=
  ∃ M : Multi α, M.Semidecides = L

/-- Semantic definition of deterministic computation. -/
def Multi.IsDeterministic (M : Multi α) : Prop :=
  ∀ w : List α, ∀ n : ℕ, ∀ s : Tapes M.e M.τ, M.Derives (M.initialize w) s n →
    ∀ x y : Tapes M.e M.τ, M.Transforms s x ∧ M.Transforms s y → x = y

end defPredicates
