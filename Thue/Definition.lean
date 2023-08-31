import Mathlib.Computability.Language


/-- Sum type of alphabet `α` and special symbols `β` -/
inductive Symbol (α : Type) (β : Type)
  | letter (a : α) : Symbol α β
  | marker (b : β) : Symbol α β

/-- Rewrite rule -/
structure Rule (α : Type) (β : Type) where
  input : List (Symbol α β)
  output : List (Symbol α β)

/-- Semi-Thue system (a.k.a. string rewriting system) -/
structure System (α : Type) where -- alphabet
  special : Type                  -- markers
  starting : special              -- to be prepended
  accepting : special             -- goal: derive a singleton [accepting]
  ruleset : List (Rule α special) -- rewrite rules


variable {α : Type}

/-- What happens to the input before computation starts -/
def System.initiate (h : System α) (w : List α) : List (Symbol α h.special) :=
  Symbol.marker h.starting :: List.map Symbol.letter w


/-- One step of rewriting -/
def System.Transforms (h : System α) (w₁ w₂ : List (Symbol α h.special)) : Prop :=
  ∃ r ∈ h.ruleset, ∃ u v : List (Symbol α h.special), w₁ = u ++ r.input ++ v ∧ w₂ = u ++ r.output ++ v

/-- Closure (reflexive+transitive) of the above, with step counting. Predicate `h.derives s t n` means
    the semi-Thue system `h` can transform `s` to `t` in exactly `n` rewriting step. -/
inductive System.Derives (h : System α) : List (Symbol α h.special) → List (Symbol α h.special) → ℕ → Prop
  | refl (w : List (Symbol α h.special)) : h.Derives w w 0
  | tail (u v w : List (Symbol α h.special)) (n : ℕ) : h.Derives u v n → h.Transforms v w → h.Derives u w n.succ

/-- Language recognized by given semi-Thue system. -/
def System.Semidecides (h : System α) : Language α :=
  { w | ∃ n : ℕ, h.Derives (h.initiate w) [Symbol.marker h.accepting] n }
