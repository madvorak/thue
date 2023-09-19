import Thue.Multitape.Toolbox
import Thue.Multitape.Languages
--import Mathlib.Tactic.ExtractLets


@[reducible]
private def tau : ℕ → Type
| .zero => Option (Fin 2)
| .succ _ => Fin 8

private def tauRule (u₁ u₂ : List (Option (Fin 2))) (v₁ v₂ : List (Fin 8)) : Mrule 1 tau :=
  Mrule.mk (u₁, v₁, ()) (u₂, v₂, ())

/-
Start:
∅w = ∅v∅v
625

Succeed:
∅
45
-/

private def move0 : Mrule 1 tau :=
  tauRule [none, some 0] [none] [2] [0, 2]

private def move1 : Mrule 1 tau :=
  tauRule [none, some 1] [none] [2] [1, 2]

private def uturn : Mrule 1 tau :=
  tauRule [none, none] [none, none] [2] [3]

private def rewind0 : Mrule 1 tau :=
  tauRule [none, none] [none, none] [0, 3] [3]

private def rewind1 : Mrule 1 tau :=
  tauRule [none, none] [none, none] [1, 3] [3]

private def ahead : Mrule 1 tau :=
  tauRule [none, none] [none] [6, 3] [4]

private def check0 : Mrule 1 tau :=
  tauRule [none, none, some 0] [none] [4, 0] [4]

private def check1 : Mrule 1 tau :=
  tauRule [none, none, some 1] [none] [4, 1] [4]

private def endYes : Mrule 1 tau :=
  tauRule [none, none] [none] [4, 5] [7]


private def rulesRep := [move0, move1, uturn, rewind0, rewind1, ahead, check0, check1, endYes]

private def machineRep : Multi (Option (Fin 2)) :=
  Multi.mk 1 tau id rulesRep ([none], [6, 2, 5], ()) (none, some 7, ())


private def emb2fin8 : Fin 2 → Fin 8 := Fin.castLE (by decide)

private lemma firstEpoch {v : List (Fin 2)} :
  machineRep.Derives
    (none :: (List.map some v ++ [none] ++ List.map some v), machineRep.starting.snd)
    ([none, none] ++ List.map some v, 6 :: List.map emb2fin8 v ++ [2, 5], ())
    200 := -- TODO replace constants
by
  sorry

private lemma stepUturn {v : List (Fin 2)} :
  machineRep.Transforms
    ([none, none] ++ List.map some v, 6 :: List.map emb2fin8 v ++ [2, 5], ())
    ([none, none] ++ List.map some v, 6 :: List.map emb2fin8 v ++ [3, 5], ()) :=
by
  sorry

private lemma secondEpoch {v : List (Fin 2)} :
  machineRep.Derives
    ([none, none] ++ List.map some v, [6] ++ List.map emb2fin8 v ++ [3, 5], ())
    ([none, none] ++ List.map some v, [6, 3] ++ List.map emb2fin8 v ++ [5], ())
    200 := -- TODO replace constants
by
  sorry

private lemma stepAhead {v : List (Fin 2)} :
  machineRep.Transforms
    ([none, none] ++ List.map some v, [6, 3] ++ List.map emb2fin8 v ++ [5], ())
    ([none, none] ++ List.map some v, [4] ++ List.map emb2fin8 v ++ [5], ()) :=
by
  sorry

private lemma thirdEpoch {v : List (Fin 2)} :
  machineRep.Derives
    ([none, none] ++ List.map some v, [4] ++ List.map emb2fin8 v ++ [5], ())
    ([none, none], ([4, 5] : List (Fin 8)), ())
    263 := -- TODO replace constants
by
  sorry

private lemma lastStep :
  machineRep.Transforms
    (([none, none] : List (Option (Fin 2))), ([4, 5] : List (Fin 8)), ())
    (([none] : List (Option (Fin 2))), ([7] : List (Fin 8)), ()) :=
by
  use endYes
  constructor
  · simp [machineRep, rulesRep]
  intros i ok
  cases i with
  | zero =>
    use [], []
    simp [machineRep, rulesRep, endYes, tauRule]
  | succ z =>
    use [], []
    simp [machineRep, rulesRep, endYes, tauRule]

private lemma easyDirection {w : List (Option (Fin 2))} {v : List (Fin 2)}
    (hyp : let v' := List.map some v ; v' ++ [none] ++ v' = w) :
  machineRep.Derives
    (Multi.initialize machineRep w)
    (([none] : List (Option (Fin 2))), ([7] : List (Fin 8)), ())
    666 := -- TODO replace constants
by
  simp [Multi.initialize, Tapes.toTProdCons, tapesOfTProdCons, List.TProd.replaceHead]
  convert_to Multi.Derives machineRep (none :: w, machineRep.starting.snd) _ (665 + 1)
  · simp [machineRep]
  apply Multi.deri_of_deri_tran _ lastStep
  rw [←hyp]
  rw [show 665 = 200 + 465 by decide] -- TODO replace constants
  apply Multi.deri_of_deri_deri firstEpoch
  apply Multi.deri_of_tran_deri stepUturn
  rw [show 464 = 200 + 264 by decide] -- TODO replace constants
  apply Multi.deri_of_deri_deri secondEpoch
  apply Multi.deri_of_tran_deri stepAhead
  apply thirdEpoch

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
    use 666 -- TODO replace constants
    use (([none] : List (Option (Fin 2))), ([7] : List (Fin 8)), ())
    constructor
    · exact easyDirection hyp
    intros i ok
    cases i with
    | zero =>
      left
      simp [machineRep, List.TProd.elim]
    | succ n =>
      cases n with
      | zero =>
        right
        simp [machineRep, List.TProd.elim]
      | succ n =>
        simp only [machineRep] at ok
        contradiction
