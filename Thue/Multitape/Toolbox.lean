import Thue.Multitape.Definition

variable {T : Type} {M : Multi T}


lemma Multi.deri_self {x : Tapes M.e M.τ} :
  M.Derives x x 0 :=
by
  apply Multi.Derives.refl

lemma Multi.deri_of_tran {x y : Tapes M.e M.τ}
    (hxy : M.Transforms x y) :
  M.Derives x y 1 :=
by
  apply Multi.Derives.tail
  apply Multi.Derives.refl
  exact hxy

lemma Multi.deri_of_deri_deri {x y z : Tapes M.e M.τ} {m n : ℕ}
    (hxy : M.Derives x y m) (hyz : M.Derives y z n) :
  M.Derives x z (m + n) :=
by
  induction hyz with
  | refl => exact hxy
  | tail v w n _ orig ih =>
    apply Multi.Derives.tail
    exact ih
    exact orig

lemma Multi.deri_of_deri_tran {x y z : Tapes M.e M.τ} {m : ℕ}
    (hxy : M.Derives x y m) (hyz : M.Transforms y z) :
  M.Derives x z m.succ :=
by
  apply Multi.Derives.tail
  exact hxy
  exact hyz

lemma Multi.deri_of_tran_deri {x y z : Tapes M.e M.τ} {n : ℕ}
    (hxy : M.Transforms x y) (hyz : M.Derives y z n) :
  M.Derives x z n.succ :=
by
  convert_to M.Derives x z (1 + n)
  · rw [add_comm]
  apply Multi.deri_of_deri_deri
  exact M.deri_of_tran hxy
  exact hyz
