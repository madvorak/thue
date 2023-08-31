import Thue.Definition

variable {α : Type}

/-- Definition of recursively-enumerable languages in terms of semi-Thue systems. -/
def Language.InRE (L : Language α) : Prop :=
  ∃ h : System α, h.Semidecides = L

def System.IsNtime (h : System α) (f : ℕ → ℕ) : Prop :=
  ∃ c : ℕ, ∀ w : List α, ∀ s : List (Symbol α h.special), ∀ n : ℕ, h.Derives (h.initiate w) s n →
    n ≤ c * f w.length.succ

def Language.InNtime (L : Language α) (f : ℕ → ℕ) : Prop :=
  ∃ h : System α, h.Semidecides = L ∧ h.IsNtime f

/-- Related concept: https://en.wikipedia.org/wiki/Unambiguous_Turing_machine -/
def System.IsDeterministic (h : System α) : Prop :=
  ∀ w : List α, ∀ s : List (Symbol α h.special), ∀ n : ℕ, h.Derives (h.initiate w) s n →
    ∀ x y : List (Symbol α h.special), h.Transforms s x ∧ h.Transforms s y → x = y

def System.IsDtime (h : System α) (f : ℕ → ℕ) : Prop :=
  h.IsDeterministic ∧ h.IsNtime f

def Language.InDtime (L : Language α) (f : ℕ → ℕ) : Prop :=
  ∃ h : System α, h.Semidecides = L ∧ h.IsDtime f
