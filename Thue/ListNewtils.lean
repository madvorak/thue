import Mathlib.Data.List.Basic

variable {α : Type}

-- from `https://github.com/madvorak/chomsky/blob/main/Grammars/Utilities/ListUtils.lean`
lemma List.mem_doubleton {a b c : α} :
  a ∈ [b, c] ↔ a = b ∨ a = c :=
by
  rw [List.mem_cons, List.mem_singleton]

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
