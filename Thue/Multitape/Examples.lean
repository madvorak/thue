import Thue.Multitape.Definition
import Thue.Multitape.Languages

@[reducible]
private def tau : ℕ → Type
| .zero => Option (Fin 2)
| .succ _ => Fin 6

/-
Start:
∅w = ∅v∅v
225

Accept:
∅
45
-/

private def copy0 : Mrule 2 tau :=
  Mrule.mk (([none, some 0], [2], ())) (([none], [0, 2], ()))

private def copy1 : Mrule 2 tau :=
  Mrule.mk (([none, some 1], [2], ())) (([none], [1, 2], ()))

private def uturn : Mrule 2 tau :=
  Mrule.mk (([none, none], [2], ())) (([none, none], [3], ()))

private def rewind0 : Mrule 2 tau :=
  Mrule.mk (([none, none], [0, 3], ())) (([none, none], [3], ()))

private def rewind1 : Mrule 2 tau :=
  Mrule.mk (([none, none], [1, 3], ())) (([none, none], [3], ()))

private def ahead : Mrule 2 tau :=
  Mrule.mk (([none, none], [2, 3], ())) (([none], [4], ()))

private def check0 : Mrule 2 tau :=
  Mrule.mk (([none, some 0], [4, 0], ())) (([none], [4], ()))

private def check1 : Mrule 2 tau :=
  Mrule.mk (([none, some 1], [4, 1], ())) (([none], [4], ()))

private def rulesRep := [copy0, copy1, uturn, rewind0, rewind1, ahead, check0, check1]

private def machineRep : Multi (Option (Fin 2)) :=
  Multi.mk 2 tau id rulesRep (([none], [2, 2, 5], ())) sorry

example : (langRepetition (Fin 2)).InMRE :=
by
  use machineRep
  sorry
