import Mathlib.Computability.Language


inductive Symbol (α : Type) (β : Type)
  | letter (a : α) : Symbol α β
  | marker (b : β) : Symbol α β

structure Rule (α : Type) (β : Type) where
  input : List (Symbol α β)
  ouput : List (Symbol α β)

structure System (α : Type) where -- alphabet
  special : Type                  -- markers
  starting : special              -- prepended
  accepting : special             -- goal
  ruleset : List (Rule α special) -- rewrite rules

variable {α : Type}

def System.initiate (h : System α) (w : List α) : List (Symbol α h.special) :=
  Symbol.marker h.starting :: List.map Symbol.letter w


def System.Transforms (h : System α) (w₁ w₂ : List (Symbol α h.special)) : Prop :=
  ∃ r : Rule α h.special,
    r ∈ h.ruleset ∧
    ∃ u v : List (Symbol α h.special), w₁ = u ++ r.input ++ v ∧ w₂ = u ++ r.ouput ++ v

inductive System.Derives (h : System α) : List (Symbol α h.special) → List (Symbol α h.special) → ℕ → Prop
  | refl (w : List (Symbol α h.special)) : h.Derives w w 0
  | tail (u v w : List (Symbol α h.special)) (n : ℕ) : h.Derives u v n → h.Transforms v w → h.Derives u w n.succ

def System.language (h : System α) : Language α :=
  { w | ∃ n : ℕ, h.Derives (h.initiate w) [Symbol.marker h.accepting] n }

def Language.IsThue (L : Language α) : Prop :=
  ∃ h : System α, h.language = L

def System.IsDeterministic (h : System α) : Prop :=
  ∀ w : List α, ∀ s : List (Symbol α h.special), ∀ n : ℕ, h.Derives (h.initiate w) s n →
    ∀ x y : List (Symbol α h.special), h.Transforms s x ∧ h.Transforms s y → x = y

def Language.IsDethue (L : Language α) : Prop :=
  ∃ h : System α, h.language = L ∧ h.IsDeterministic

def System.IsDtime (h : System α) (f : ℕ → ℕ) : Prop :=
  h.IsDeterministic ∧
  ∃ c : ℕ, ∀ w : List α, ∀ s : List (Symbol α h.special), ∀ n : ℕ,
    h.Derives (h.initiate w) s n → n ≤ c * f w.length
