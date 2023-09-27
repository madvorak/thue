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
  tauRule [none, none] [none, none] [0, 3] [3, 0]

private def rewind1 : Mrule 1 tau :=
  tauRule [none, none] [none, none] [1, 3] [3, 1]

private def ahead : Mrule 1 tau :=
  tauRule [none, none] [none, none] [5, 3] [4]

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
    ([none] ++ List.map some (v.take n) ++ [none] ++ List.map some v,
      ([5] ++ List.map emb2fin8 (v.drop n) ++ [2, 6] : List (Fin 8)), ())
    ([none, none] ++ List.map some v,
      [5] ++ List.map emb2fin8 v ++ [2, 6], ())
    n :=
by
  sorry

private lemma epochScan {v : List (Fin 2)} :
  machineRep.Derives
    ([none] ++ List.map some v ++ [none] ++ List.map some v, ([5, 2, 6] : List (Fin 8)), ())
    ([none, none] ++ List.map some v, [5] ++ List.map emb2fin8 v ++ [2, 6], ())
    v.length :=
by
  convert epochScan_aux (show v.length ≤ v.length by rfl) using 3
  · rw [List.take_length]
  · rw [List.drop_length]
    rfl

private lemma stepUturn {v : List (Fin 2)} :
  machineRep.Transforms
    ([none, none] ++ List.map some v, [5] ++ List.map emb2fin8 v ++ [2, 6], ())
    ([none, none] ++ List.map some v, [5] ++ List.map emb2fin8 v ++ [3, 6], ()) :=
by
  use uturn
  constructor
  · simp [machineRep, rulesRep]
  intros i ok
  match i with
  | 0 =>
    use [], List.map some v
    constructor
    · rfl
    · rfl
  | 1 =>
    use [5] ++ List.map emb2fin8 v, ([6] : List (Fin 8))
    constructor
    · show [5] ++ List.map emb2fin8 v ++ [2, 6] = [5] ++ (List.map emb2fin8 v ++ [2] ++ [6])
      simp
    · show [5] ++ List.map emb2fin8 v ++ [3, 6] = [5] ++ (List.map emb2fin8 v ++ [3] ++ [6])
      simp

private lemma epochRewind_aux {v : List (Fin 2)} {n : ℕ} (hn : n ≤ v.length) :
  machineRep.Derives
    ([none, none] ++ List.map some v,
      [5] ++ List.map emb2fin8 (v.take n) ++ [3] ++ List.map emb2fin8 (v.drop n) ++ [6],
      ())
    ([none, none] ++ List.map some v,
      [5, 3] ++ List.map emb2fin8 v ++ [6],
      ())
    n :=
by
  induction n with
  | zero =>
    unfold List.drop
    unfold List.take
    rw [List.map_nil, List.append_nil, List.two_singletons_eq_doubleton]
    apply Multi.deri_self
  | succ n ih =>
    have hn' : n < v.length
    · exact hn
    apply Multi.deri_of_tran_deri _ (ih (le_of_lt hn'))
    let n' : Fin v.length := ⟨n, hn'⟩
    rw [List.take_succ]
    have nth_valid : Option.toList (v.get? n) = [v.get n']
    · rw [List.get?_eq_get hn', Option.to_list_some]
    rw [nth_valid]
    match vgn : v.get n' with
    | 0 =>
      have nth_char : v.get n' = 0
      · exact vgn
      clear vgn
      use rewind0
      constructor
      · simp [machineRep, rulesRep]
      intro i iok
      match i with
      | 0 =>
        use [], v.map some
        constructor
        · rfl
        · rfl
      | 1 =>
        use [5] ++ List.map emb2fin8 (v.take n), (v.drop n.succ).map emb2fin8 ++ [6]
        constructor
        · convert_to
            [5] ++ (v.take n ++ [0]).map emb2fin8 ++ [3] ++ (v.drop n.succ).map emb2fin8 ++ [6] =
            ([5] ++ (v.take n).map emb2fin8) ++ [0, 3] ++ ((v.drop n.succ).map emb2fin8 ++ [6])
          simp
        · convert_to
            [5] ++ List.map emb2fin8 (List.take n v) ++ [3] ++ List.map emb2fin8 (List.drop n v) ++ [6] =
            [5] ++ List.map emb2fin8 (List.take n v) ++ [3, 0] ++ (List.map emb2fin8 (List.drop (Nat.succ n) v) ++ [6])
          have key : (v.drop n).map emb2fin8 = [0] ++ (v.drop n.succ).map emb2fin8
          · convert_to (v.drop n).map emb2fin8 = [emb2fin8 (v.get n')] ++ (v.drop n.succ).map emb2fin8
            · rw [nth_char]
              rfl
            convert_to (v.drop n).map emb2fin8 = ([v.get n'] ++ v.drop n.succ).map emb2fin8
            apply congr_arg
            exact List.drop_eq_get_cons hn'
          rw [key]
          simp
    | 1 =>
      have nth_char : v.get n' = 1
      · exact vgn
      clear vgn
      use rewind1
      constructor
      · simp [machineRep, rulesRep]
      intro i iok
      match i with
      | 0 =>
        use [], v.map some
        constructor
        · rfl
        · rfl
      | 1 =>
        use [5] ++ List.map emb2fin8 (v.take n), (v.drop n.succ).map emb2fin8 ++ [6]
        constructor
        · convert_to
            [5] ++ (v.take n ++ [1]).map emb2fin8 ++ [3] ++ (v.drop n.succ).map emb2fin8 ++ [6] =
            ([5] ++ (v.take n).map emb2fin8) ++ [1, 3] ++ ((v.drop n.succ).map emb2fin8 ++ [6])
          simp
        · convert_to
            [5] ++ List.map emb2fin8 (List.take n v) ++ [3] ++ List.map emb2fin8 (List.drop n v) ++ [6] =
            [5] ++ List.map emb2fin8 (List.take n v) ++ [3, 1] ++ (List.map emb2fin8 (List.drop (Nat.succ n) v) ++ [6])
          have key : (v.drop n).map emb2fin8 = [1] ++ (v.drop n.succ).map emb2fin8
          · convert_to (v.drop n).map emb2fin8 = [emb2fin8 (v.get n')] ++ (v.drop n.succ).map emb2fin8
            · rw [nth_char]
              rfl
            convert_to (v.drop n).map emb2fin8 = ([v.get n'] ++ v.drop n.succ).map emb2fin8
            apply congr_arg
            exact List.drop_eq_get_cons hn'
          rw [key]
          simp

private lemma epochRewind {v : List (Fin 2)} :
  machineRep.Derives
    ([none, none] ++ List.map some v, [5] ++ List.map emb2fin8 v ++ [3, 6], ())
    ([none, none] ++ List.map some v, [5, 3] ++ List.map emb2fin8 v ++ [6], ())
    v.length :=
by
  convert epochRewind_aux (show v.length ≤ v.length by rfl) using 3
  rw [List.drop_length, List.take_length, List.map_nil, List.append_nil]
  rw [←List.two_singletons_eq_doubleton, ←List.append_assoc]

private lemma stepAhead {v : List (Fin 2)} :
  machineRep.Transforms
    ([none, none] ++ List.map some v, [5, 3] ++ List.map emb2fin8 v ++ [6], ())
    ([none, none] ++ List.map some v, [4] ++ List.map emb2fin8 v ++ [6], ()) :=
by
  use ahead
  constructor
  · simp [machineRep, rulesRep]
  intros i ok
  match i with
  | 0 =>
    use [], List.map some v
    constructor
    · rfl
    · rfl
  | 1 =>
    use [], List.map emb2fin8 v ++ [6]
    constructor
    · rfl
    · rfl

private lemma epochCheck_aux {v : List (Fin 2)} {n : ℕ} (hn : n ≤ v.length) :
  machineRep.Derives
    ([none, none] ++ List.map some (v.drop (v.length - n)),
      [4] ++ List.map emb2fin8 (v.drop (v.length - n)) ++ [6], ())
    ([none, none],
      ([4, 6] : List (Fin 8)), ())
    v.length :=
by
  sorry

private lemma epochCheck {v : List (Fin 2)} :
  machineRep.Derives
    ([none, none] ++ List.map some v, [4] ++ List.map emb2fin8 v ++ [6], ())
    ([none, none], ([4, 6] : List (Fin 8)), ())
    v.length :=
by
  convert epochCheck_aux (show v.length ≤ v.length by rfl) using 3 <;>
  · rw [Nat.sub_self]
    rfl

private lemma stepYes :
  machineRep.Transforms
    (([none, none] : List (Option (Fin 2))), ([4, 6] : List (Fin 8)), ())
    (([none] : List (Option (Fin 2))), ([7] : List (Fin 8)), ()) :=
by
  use endYes
  constructor
  · simp [machineRep, rulesRep]
  intros i ok
  match i with
  | 0 =>
    use [], []
    constructor
    · rfl
    · rfl
  | 1 =>
    use [], []
    constructor
    · rfl
    · rfl

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
    match i with
    | 0 =>
      left
      simp [machineRep, List.TProd.elim]
    | 1 =>
      right
      simp [machineRep, List.TProd.elim]
