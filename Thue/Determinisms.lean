import Thue.Definition

variable {α : Type}

def hasOneMarker {β : Type} (s : List (Symbol α β)) : Prop :=
  ∃ u : List α, ∃ X : β, ∃ v : List α,
    s = List.map Symbol.letter u ++ [Symbol.marker X] ++ List.map Symbol.letter v

def actuallyOverlap {β : Type} (s₁ s₂ : List (Symbol α β)) : Prop :=
  ∃ t : List (Symbol α β), hasOneMarker t ∧
    ∃ u₁ u₂ v₁ v₂ : List (Symbol α β), u₁ ++ s₁ ++ v₁ = t ∧ u₂ ++ s₂ ++ v₂ = t

def System.IsDeterministicSyntax (h : System α) : Prop :=
  (∀ r ∈ h.ruleset, hasOneMarker r.input ∧ hasOneMarker r.output) ∧
  (∀ r₁ ∈ h.ruleset, ∀ r₂ ∈ h.ruleset, ¬ actuallyOverlap r₁.input r₂.input)

lemma marker_notin_list_letters {β : Type} (B : β) (w : List α) :
  Symbol.marker B ∉ List.map Symbol.letter w :=
by
  rw [List.mem_map]
  push_neg
  intros a _
  apply Symbol.noConfusion

lemma System.IsDeterministicSyntax.always_hasOneMarker {h : System α} (det : h.IsDeterministicSyntax)
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

theorem deterministic_of_deterministicSyntax (h : System α) :
  h.IsDeterministicSyntax → h.IsDeterministic :=
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
