import Thue.Multitape.Toolbox
import Thue.Multitape.Languages
import Thue.ListNewtils
import Mathlib.Tactic.Ring


@[reducible]
private def tau : ℕ → Type
| .zero => Option (Fin 2)
| .succ _ => Fin 8

private def tauRule (u₁ u₂ : List (Option (Fin 2))) (v₁ v₂ : List (Fin 8)) : Mrule 1 tau :=
  Mrule.mk (u₁, v₁, ()) (u₂, v₂, ())

/-
Start:
∅w = ∅v∅v
526

Succeed:
∅
46
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
  tauRule [none, none] [none] [5, 3] [4]

private def check0 : Mrule 1 tau :=
  tauRule [none, none, some 0] [none] [4, 0] [4]

private def check1 : Mrule 1 tau :=
  tauRule [none, none, some 1] [none] [4, 1] [4]

private def endYes : Mrule 1 tau :=
  tauRule [none, none] [none] [4, 6] [7]


private def rulesRep := [move0, move1, uturn, rewind0, rewind1, ahead, check0, check1, endYes]

private def machineRep : Multi (Option (Fin 2)) :=
  Multi.mk 1 tau id rulesRep ([none], [5, 2, 6], ()) (none, some 7, ())


private def emb2fin8 : Fin 2 → Fin 8 := Fin.castLE (by decide)

private lemma epochScan_aux {v : List (Fin 2)} {n : ℕ} (hn : n ≤ v.length) :
  machineRep.Derives
    ([none] ++ List.map some v ++ [none] ++ List.map some v,
      ([5, 2, 6] : List (Fin 8)), ())
    ([none] ++ List.map some (v.drop n) ++ [none] ++ List.map some v,
      [5] ++ List.map emb2fin8 (v.take n) ++ [2, 6], ())
    n :=
by
  induction n with
  | zero =>
    apply Multi.deri_self
  | succ n ih =>
    specialize ih sorry
    apply Multi.deri_of_deri_tran ih
    cases v.drop n with
    | nil => sorry
    | cons a l =>
      have vdropsucc : v.drop n.succ = l
      · sorry
      have vtakesucc : v.take n.succ = v.take n ++ [a]
      · sorry
      rw [vdropsucc, vtakesucc]
      rw [List.map_cons, List.singleton_append_cons_eq_doubleton_append]
      rw [List.map_append, List.map_singleton, ←List.append_assoc]
      rw [List.append_assoc _ [emb2fin8 a] _]
      by_cases a_is : a = 0
      · rw [a_is]
        use move0
        constructor
        · simp [machineRep, rulesRep]
        intros i ok
        cases i with
        | zero =>
          use [], List.map some l ++ [none] ++ List.map some v
          simp
          constructor
          · simp
            sorry
          · simp
            sorry
        | succ n =>
          sorry
      have a_is1 : a = 1
      · sorry
      sorry

private lemma epochScan {v : List (Fin 2)} :
  machineRep.Derives
    ([none] ++ List.map some v ++ [none] ++ List.map some v, ([5, 2, 6] : List (Fin 8)), ())
    ([none, none] ++ List.map some v, [5] ++ List.map emb2fin8 v ++ [2, 6], ())
    v.length :=
by
  convert epochScan_aux (show v.length ≤ v.length by rfl)
  · rw [List.drop_length, List.map_nil, List.append_nil]
    rfl
  · rw [List.take_length]

private lemma stepUturn {v : List (Fin 2)} :
  machineRep.Transforms
    ([none, none] ++ List.map some v, [5] ++ List.map emb2fin8 v ++ [2, 6], ())
    ([none, none] ++ List.map some v, [5] ++ List.map emb2fin8 v ++ [3, 6], ()) :=
by
  sorry

private lemma epochRewind {v : List (Fin 2)} :
  machineRep.Derives
    ([none, none] ++ List.map some v, [5] ++ List.map emb2fin8 v ++ [3, 6], ())
    ([none, none] ++ List.map some v, [5, 3] ++ List.map emb2fin8 v ++ [6], ())
    v.length :=
by
  sorry

private lemma stepAhead {v : List (Fin 2)} :
  machineRep.Transforms
    ([none, none] ++ List.map some v, [5, 3] ++ List.map emb2fin8 v ++ [6], ())
    ([none, none] ++ List.map some v, [4] ++ List.map emb2fin8 v ++ [6], ()) :=
by
  use ahead
  constructor
  · simp [machineRep, rulesRep]
  intros i ok
  cases i with
  | zero =>
    use [], List.map some v
    sorry
  | succ z =>
    use [], List.map emb2fin8 v ++ [6]
    sorry

private lemma epochCheck {v : List (Fin 2)} :
  machineRep.Derives
    ([none, none] ++ List.map some v, [4] ++ List.map emb2fin8 v ++ [6], ())
    ([none, none], ([4, 6] : List (Fin 8)), ())
    v.length :=
by
  sorry

private lemma stepYes :
  machineRep.Transforms
    (([none, none] : List (Option (Fin 2))), ([4, 6] : List (Fin 8)), ())
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
    (hyp : List.map some v ++ [none] ++ List.map some v = w) :
  machineRep.Derives
    (Multi.initialize machineRep w)
    (([none] : List (Option (Fin 2))), ([7] : List (Fin 8)), ())
    (3 * v.length + 3) :=
by
  convert_to
    machineRep.Derives
      ([none] ++ w, machineRep.starting.snd)
      ([none], ([7] : List (Fin 8)), ())
      (v.length + 1 + v.length + 1 + v.length + 1)
  · show (machineRep.starting.fst.append (w.map machineRep.embed), _) = _
    simp [machineRep]
  · ring
  rw [←hyp]
  apply Multi.deri_of_deri_tran _ stepYes
  apply Multi.deri_of_deri_deri _ epochCheck
  apply Multi.deri_of_deri_tran _ stepAhead
  apply Multi.deri_of_deri_deri _ epochRewind
  apply Multi.deri_of_deri_tran _ stepUturn
  exact epochScan -- no idea why `exact` works and why `convert` doesn't

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
    use 3 * v.length + 3
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
