import Thue.Multitape.Definition
import Thue.Multitape.Languages


@[reducible]
private def tau : ℕ → Type
| .zero => Option (Fin 2)
| .succ _ => Fin 8

private def tauRule (u₁ u₂ : List (Option (Fin 2))) (v₁ v₂ : List (Fin 8)) : Mrule 2 tau :=
  Mrule.mk (u₁, v₁, ()) (u₂, v₂, ())

/-
Start:
∅w = ∅v∅v
625

Succeed:
∅
45
-/

private def move0 : Mrule 2 tau :=
  tauRule [none, some 0] [none] [2] [0, 2]

private def move1 : Mrule 2 tau :=
  tauRule [none, some 1] [none] [2] [1, 2]

private def uturn : Mrule 2 tau :=
  tauRule [none, none] [none, none] [2] [3]

private def rewind0 : Mrule 2 tau :=
  tauRule [none, none] [none, none] [0, 3] [3]

private def rewind1 : Mrule 2 tau :=
  tauRule [none, none] [none, none] [1, 3] [3]

private def ahead : Mrule 2 tau :=
  tauRule [none, none] [none] [6, 3] [4]

private def check0 : Mrule 2 tau :=
  tauRule [none, some 0] [none] [4, 0] [4]

private def check1 : Mrule 2 tau :=
  tauRule [none, some 1] [none] [4, 1] [4]

private def endYes : Mrule 2 tau :=
  tauRule [none] [] [4, 5] [7]


private def rulesRep := [move0, move1, uturn, rewind0, rewind1, ahead, check0, check1, endYes]

private def machineRep : Multi (Option (Fin 2)) :=
  Multi.mk 2 (Nat.succ_pos 1) tau id rulesRep ([none], [2, 2, 5], ()) (none, some 7, ())

private lemma easyDirection {w : List (Option (Fin 2))} {v : List (Fin 2)}
    (hyp: let v' := List.map some v ; v' ++ [none] ++ v' = w) :
  Multi.Derives machineRep
    (Multi.initiate machineRep w)
    (([] : List (Option (Fin 2))), ([7] : List (Fin 8)), ())
    666 :=
by
  sorry

private theorem langRepetition_is_RE : (langRepetition (Fin 2)).InMRE :=
by
  use machineRep
  unfold Multi.Semidecides
  unfold langRepetition
  ext w
  rw [Set.mem_setOf_eq, Set.mem_setOf_eq]
  constructor
  · sorry
  · rintro ⟨v, hyp⟩
    use 666 -- TODO
    use (([] : List (Option (Fin 2))), ([7] : List (Fin 8)), ())
    constructor
    · exact easyDirection hyp
    simp only [Multi.terminate, machineRep, Function.comp_apply]
    intro i
    intro ok
    cases i with
    | zero =>
      left
      sorry
    | succ n =>
      cases n with
      | zero =>
        right
        sorry
      | succ n =>
        simp [machineRep] at ok
        contradiction
