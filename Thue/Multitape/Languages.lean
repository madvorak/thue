import Mathlib.Computability.Language


def langRepetition (α : Type) : Language (Option α) :=
  { w | ∃ v : List α, let v' := v.map Option.some ; v' ++ [none] ++ v' = w }
