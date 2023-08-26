import Thue.Definition

variable {T : Type} {g : System T}


lemma System.deri_self {w : List (Symbol T g.special)} :
  g.Derives w w 0 :=
by -- seems redundant
  apply System.Derives.refl

lemma System.deri_of_tran {v w : List (Symbol T g.special)}
    (ass : g.Transforms v w) :
  g.Derives v w 1 :=
by
  apply System.Derives.tail
  apply System.Derives.refl
  exact ass

lemma System.deri_of_deri_deri {u v w : List (Symbol T g.special)} {m n : ℕ}
    (huv : g.Derives u v m) (hvw : g.Derives v w n) :
  g.Derives u w (m + n) :=
by
  induction hvw with
  | refl => exact huv
  | tail v w n _ orig ih =>
    apply System.Derives.tail
    exact ih
    exact orig

lemma System.deri_of_deri_tran {u v w : List (Symbol T g.special)} {m : ℕ}
    (huv : g.Derives u v m) (hvw : g.Transforms v w) :
  g.Derives u w m.succ :=
by -- seems redundant
  apply System.Derives.tail
  exact huv
  exact hvw

lemma System.deri_of_tran_deri {u v w : List (Symbol T g.special)} {n : ℕ}
    (huv : g.Transforms u v) (hvw : g.Derives v w n) :
  g.Derives u w n.succ :=
by
  convert_to g.Derives u w (1 + n)
  · rw [add_comm]
  apply System.deri_of_deri_deri
  exact g.deri_of_tran huv
  exact hvw

lemma System.eq_or_tran_deri_of_deri {u w : List (Symbol T g.special)} {n : ℕ}
    (huw : g.Derives u w n.succ) :
  ∃ v : List (Symbol T g.special), g.Transforms u v ∧ g.Derives v w n :=
sorry

lemma System.eq_or_deri_tran_of_deri {u w : List (Symbol T g.special)} {n : ℕ}
    (huw : g.Derives u w n.succ) :
  ∃ v : List (Symbol T g.special), g.Derives u v n ∧ g.Transforms v w :=
by
  cases huw with
  | tail v w n tran deri =>
    use v

lemma System.deri_with_prefix {w₁ w₂ : List (Symbol T g.special)} {n : ℕ}
    (z : List (Symbol T g.special)) (ass : g.Derives w₁ w₂ n) :
  g.Derives (z ++ w₁) (z ++ w₂) n :=
by
  induction ass with
  | refl => apply System.deri_self
  | tail x y m _ orig ih =>
    apply System.deri_of_deri_tran
    · exact ih
    rcases orig with ⟨r, rin, u, v, bef, aft⟩
    use r
    constructor
    · exact rin
    use z ++ u, v
    rw [bef, aft]
    constructor <;> simp only [List.append_assoc]

lemma System.deri_with_postfix {w₁ w₂ : List (Symbol T g.special)} {n : ℕ}
    (z : List (Symbol T g.special)) (ass : g.Derives w₁ w₂ n) :
  g.Derives (w₁ ++ z) (w₂ ++ z) n :=
by
  induction ass with
  | refl => apply System.deri_self
  | tail x y m _ orig ih =>
    apply System.deri_of_deri_tran
    · exact ih
    rcases orig with ⟨r, rin, u, v, bef, aft⟩
    use r
    constructor
    · exact rin
    use u, v ++ z
    rw [bef, aft]
    constructor <;> simp only [List.append_assoc]
