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
    the semi-Thue system `h` can transform `t` to `n` in exactly `n` rewriting step. -/
inductive System.Derives (h : System α) : List (Symbol α h.special) → List (Symbol α h.special) → ℕ → Prop
  | refl (w : List (Symbol α h.special)) : h.Derives w w 0
  | tail (u v w : List (Symbol α h.special)) (n : ℕ) : h.Derives u v n → h.Transforms v w → h.Derives u w n.succ

/-- Language recognized by given semi-Thue system. -/
def System.Semidecides (h : System α) : Language α :=
  { w | ∃ n : ℕ, h.Derives (h.initiate w) [Symbol.marker h.accepting] n }

/-- Definition of recursively-enumerable languages in terms of semi-Thue systems. -/
def Language.IsRE (L : Language α) : Prop :=
  ∃ h : System α, h.Semidecides = L


def System.IsDeterministic (h : System α) : Prop :=
  ∀ w : List α, ∀ s : List (Symbol α h.special), ∀ n : ℕ, h.Derives (h.initiate w) s n →
    ∀ x y : List (Symbol α h.special), h.Transforms s x ∧ h.Transforms s y → x = y

def hasOneMarker {β : Type} (s : List (Symbol α β)) : Prop :=
  ∃ u : List α, ∃ X : β, ∃ v : List α,
    s = List.map Symbol.letter u ++ [Symbol.marker X] ++ List.map Symbol.letter v

def actuallyOverlap {β : Type} (s₁ s₂ : List (Symbol α β)) : Prop :=
  ∃ t : List (Symbol α β), hasOneMarker t ∧
    ∃ u₁ u₂ v₁ v₂ : List (Symbol α β), u₁ ++ s₁ ++ v₁ = t ∧ u₂ ++ s₂ ++ v₂ = t

def System.IsDeterministic' (h : System α) : Prop :=
  (∀ r ∈ h.ruleset, hasOneMarker r.input ∧ hasOneMarker r.output) ∧
  (∀ r₁ ∈ h.ruleset, ∀ r₂ ∈ h.ruleset, ¬ actuallyOverlap r₁.input r₂.input)

lemma System.IsDeterministic'.always_hasOneMarker {h : System α} (det : h.IsDeterministic')
    {w : List α} {s : List (Symbol α h.special)} {n : ℕ} (obtained : h.Derives (h.initiate w) s n) :
  hasOneMarker s :=
by
  induction obtained with
  | refl =>
    use [], h.starting, w
    rw [List.map_nil, List.nil_append]
    rfl
  | tail x y m trash orig ih =>
    clear trash w s n
    rcases orig with ⟨r, rin, u, v, bef, aft⟩
    rw [aft]
    have fact := det.1 r rin
    sorry

theorem deterministic_of_deterministic' (h : System α) :
  h.IsDeterministic' → h.IsDeterministic :=
by
  intro ass
  intros w s n hyp x y transs
  rcases transs with ⟨⟨r₁, rin₁, u₁, v₁, bef₁, aft₁⟩, ⟨r₂, rin₂, u₂, v₂, bef₂, aft₂⟩⟩
  have same_r : r₁ = r₂
  · obtain ⟨inp₁, out₁⟩ := ass.1 r₁ rin₁
    obtain ⟨inp₂, out₂⟩ := ass.1 r₂ rin₂
    sorry
  have same_u : u₁ = u₂
  · sorry
  have same_v : v₁ = v₂
  · sorry
  rw [aft₁, aft₂, same_r, same_u, same_v]
