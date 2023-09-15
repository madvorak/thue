import Mathlib.Data.List.Basic
import Mathlib.Tactic.Linarith
import Grammars.Utilities.ListUtils

variable {α : Type}

lemma List.two_singletons_eq_doubleton {a b : α} :
  [a] ++ [b] = [a, b] :=
rfl

lemma List.three_singletons_eq_tripleton {a b c : α} :
  [a] ++ [b] ++ [c] = [a, b, c] :=
rfl


private lemma middle_xYz_left {x₁ x₂ z₁ z₂ : List α} {Y₁ Y₂ : α} (together : x₁ ++ [Y₁] ++ z₁ = x₂ ++ [Y₂] ++ z₂)
    (longer : x₂.length < x₁.length) :
  Y₂ ∈ x₁ :=
by
  have middle := congr_fun (congr_arg List.get? together) x₂.length
  rw [
    List.append_assoc x₂,
    List.get?_append_right x₂.length.le_refl,
    Nat.sub_self,
    List.singleton_append,
    List.get?_cons_zero,
    List.append_assoc x₁,
    List.get?_append longer,
  ] at middle
  exact List.get?_mem middle

lemma match_xYz {x₁ x₂ z₁ z₂ : List α} {Y₁ Y₂ : α} (together : x₁ ++ [Y₁] ++ z₁ = x₂ ++ [Y₂] ++ z₂)
    (notin_x : Y₂ ∉ x₁) (notin_z : Y₂ ∉ z₁) :
  x₁ = x₂ ∧ Y₁ = Y₂ ∧ z₁ = z₂ :=
by
  have xlens : x₁.length = x₂.length
  · have not_gt : ¬ x₁.length > x₂.length
    · intro contra_gt
      apply notin_x
      exact middle_xYz_left together contra_gt
    have not_lt : ¬ x₁.length < x₂.length
    · intro contra_lt
      apply notin_z
      have reversed := congr_arg List.reverse together
      rw [
        List.reverse_append_append,
        List.reverse_append_append,
        List.reverse_singleton,
        List.reverse_singleton,
      ] at reversed
      rw [←List.mem_reverse]
      apply middle_xYz_left reversed
      rw [List.length_reverse, List.length_reverse]
      have total := congr_arg List.length together
      rw [
        List.length_append_append,
        List.length_append_append,
        List.length_singleton,
        List.length_singleton,
      ] at total
      linarith
    rw [Nat.not_lt] at not_gt not_lt
    exact Nat.le_antisymm not_gt not_lt
  constructor
  · rw [List.append_assoc, List.append_assoc] at together
    convert congr_arg (List.take x₁.length) together
    · rw [List.take_left]
    · rw [xlens, List.take_left]
  constructor
  · have chopped := congr_arg (List.drop x₁.length) together
    rw [List.append_assoc, List.append_assoc, List.drop_left, xlens, List.drop_left] at chopped
    convert congr_arg List.head? chopped
    simp
  · convert congr_arg (List.drop x₁.length.succ) together
    · rw [List.drop_left']
      rw [List.length_append, List.length_singleton]
    · rw [xlens, List.drop_left']
      rw [List.length_append, List.length_singleton]

lemma match_xYz' {x₁ x₂ z₁ z₂ : List α} {Y₁ Y₂ : α} (together : x₁ ++ ([Y₁] ++ z₁) = x₂ ++ [Y₂] ++ z₂)
    (notin_x : Y₂ ∉ x₁) (notin_z : Y₂ ∉ z₁) :
  x₁ = x₂ ∧ Y₁ = Y₂ ∧ z₁ = z₂ :=
by
  rw [←List.append_assoc] at together
  exact match_xYz together notin_x notin_z

lemma match_xYz'' {x₁ x₂ z₁ z₂ : List α} {Y₁ Y₂ : α} (together : x₁ ++ [Y₁] ++ z₁ = x₂ ++ ([Y₂] ++ z₂))
    (notin_x : Y₂ ∉ x₁) (notin_z : Y₂ ∉ z₁) :
  x₁ = x₂ ∧ Y₁ = Y₂ ∧ z₁ = z₂ :=
by
  rw [←List.append_assoc] at together
  exact match_xYz together notin_x notin_z
