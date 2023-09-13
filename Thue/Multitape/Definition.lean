import Mathlib.Computability.Language
import Mathlib.Data.Prod.TProd


def List.TProd.tail {ι : Type} {α : ι → Type} {d : ι} {l : List ι}
  (x : (d::l).TProd α) : l.TProd α := x.snd

def List.TProd.replaceHead {ι : Type} {α : ι → Type} {d : ι} {l : List ι}
  (x : (d::l).TProd α) (v : α d) : (d::l).TProd α := ⟨v, x.tail⟩


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
  k_pos : 0 < k
  τ : ℕ → Type                      -- tape alphabets
  embed : α → τ 0                   -- embedding words onto the top tape
  ruleset : List (Mrule k τ)        -- rewrite rules
  starting : Tapes k τ              -- initialization strings
  accepting : List.TProd (Option ∘ τ) (List.range k) -- accepting / halting condition(s)


variable {α : Type}

/-- Initialize `M` with input `w` on which the computation should be done. -/
def Multi.initiate (M : Multi α) (w : List α) : Tapes M.k M.τ := by
  unfold Tapes
  have start := M.starting
  unfold Tapes at start
  /-have mknz : 0 < M.k := M.k_pos
  have mknz' : 1 ≤ M.k := mknz
  have zzzz : ∃ z : ℕ, M.k = z.succ
  · cases M.k with
    | zero => sorry
    | succ n => use n
  cases zzzz with
  | intro z zmk => -/
  cases M.k with
  | zero => sorry -- contradicts `M.k_pos`
  | succ n =>
    -- change List.TProd (List ∘ M.τ) (List.range n.succ) at start
    have cut_head : List.range n.succ = 0 :: (List.range n).map Nat.succ
    · exact List.range_succ_eq_map n
    rw [cut_head]
    -- rw [List.TProd, List.foldr, ←List.TProd]
    apply List.TProd.replaceHead
    · rw [←cut_head]
      sorry -- exact start -- ha hek?
    · have zero_in : 0 ∈ List.range M.k
      · exact Iff.mpr List.mem_range M.k_pos
      exact (M.starting.elim zero_in).append (w.map M.embed)

-- M.starting -- Function.update M.starting 0 (M.starting 0 ++ w.map M.embed) -- TODO

/-- Does `M` consider `s` to be in accepting state? -/
def Multi.terminate (M : Multi α) (s : Tapes M.k M.τ) : Prop :=
  ∀ i : ℕ, (ok : i < M.k) →
    let oki := Iff.mpr List.mem_range ok;
    M.accepting.elim oki = none ∨ M.accepting.elim oki = (s.elim oki).head?


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
