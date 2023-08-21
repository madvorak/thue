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


lemma match_xYz {x₁ x₂ z₁ z₂ : List α} {Y₁ Y₂ : α} (together : x₁ ++ [Y₁] ++ z₁ = x₂ ++ [Y₂] ++ z₂)
    (notin_x : Y₂ ∉ x₁) (notin_z : Y₂ ∉ z₁) :
  x₁ = x₂ ∧ z₁ = z₂ :=
by
  have xlens : x₁.length = x₂.length
  · have not_lt : ¬ x₁.length < x₂.length
    · intro contr_lt
      apply notin_z
      sorry
    have not_gt : ¬ x₁.length > x₂.length
    · intro congr_gt
      apply notin_x
      sorry
    have yes_le : x₁.length ≤ x₂.length
    · exact Iff.mp Nat.not_lt not_gt
    have yes_ge : x₁.length ≥ x₂.length
    · exact Iff.mp Nat.not_lt not_lt
    exact Nat.le_antisymm yes_le yes_ge
  constructor
  · rw [List.append_assoc, List.append_assoc] at together
    convert congr_arg (List.take x₁.length) together
    · rw [List.take_left]
    · rw [xlens, List.take_left]
  · convert congr_arg (List.drop x₁.length.succ) together
    · rw [List.drop_left']
      rw [List.length_append, List.length_singleton]
    · rw [xlens, List.drop_left']
      rw [List.length_append, List.length_singleton]

lemma marker_notin_list_letters {β : Type} (B : β) (w : List α) :
  Symbol.marker B ∉ List.map Symbol.letter w :=
by
  rw [List.mem_map]
  push_neg
  intros a _
  apply Symbol.noConfusion

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
    clear trash m w s n
    rcases orig with ⟨r, rin, u, v, bef, aft⟩
    rcases det.1 r rin with ⟨⟨u₁, X₁, v₁, r₁eq⟩, ⟨u₂, X₂, v₂, r₂eq⟩⟩
    rw [r₁eq] at bef
    rw [r₂eq] at aft
    rcases ih with ⟨u', X', v', xeq⟩
    rw [xeq] at bef
    obtain ⟨u'_of, v'_of⟩ :
      List.map Symbol.letter u' = u ++ List.map Symbol.letter u₁ ∧
      List.map Symbol.letter v' = List.map Symbol.letter v₁ ++ v
    · have reaarrange :
        u ++ (List.map Symbol.letter u₁ ++ [Symbol.marker X₁] ++ List.map Symbol.letter v₁) ++ v =
        (u ++ List.map Symbol.letter u₁) ++ [Symbol.marker X₁] ++ (List.map Symbol.letter v₁ ++ v)
      · simp only [List.append_assoc]
      rw [reaarrange] at bef
      apply match_xYz bef
      · apply marker_notin_list_letters
      · apply marker_notin_list_letters
    use u'.take u.length ++ u₂, X₂, v₂ ++ v'.drop v₁.length
    rw [List.map_append, List.map_append, List.map_take, List.map_drop]
    rw [u'_of, v'_of]
    have eqlens : v₁.length = (v₁.map Symbol.letter).length
    · rw [List.length_map]
      exact h.special
    rw [List.take_left, eqlens, List.drop_left]
    rw [aft]
    simp only [List.append_assoc]

theorem deterministic_of_deterministic' (h : System α) :
  h.IsDeterministic' → h.IsDeterministic :=
by
  intro ass
  intros w s n hyp x y transs
  rcases transs with ⟨⟨r₁, rin₁, u₁, v₁, bef₁, aft₁⟩, ⟨r₂, rin₂, u₂, v₂, bef₂, aft₂⟩⟩
  rcases ass.always_hasOneMarker hyp with ⟨sₗ, sₘ, sᵣ, s_eq⟩
  have same_r : r₁ = r₂
  · rcases ass.1 r₁ rin₁ with ⟨inp₁, out₁⟩
    rcases ass.1 r₂ rin₂ with ⟨inp₂, out₂⟩
    sorry
  rw [same_r] at bef₁
  have same_u : u₁ = u₂
  · rw [s_eq] at bef₁ bef₂
    rcases (ass.1 r₂ rin₂).1 with ⟨u', X', v', r₂_eq⟩
    rw [r₂_eq] at bef₁ bef₂
    sorry
  have same_v : v₁ = v₂
  · sorry
  rw [aft₁, aft₂, same_r, same_u, same_v]
