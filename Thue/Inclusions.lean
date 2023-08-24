import Thue.Classes


variable {α : Type}

theorem Language.InNtime.toRE {f : ℕ → ℕ} {L : Language α} (ass : L.InNtime f) : L.InRE :=
by
  rcases ass with ⟨g, hyp, -⟩
  exact ⟨g, hyp⟩

lemma System.IsDtime.toNtime {f : ℕ → ℕ} {g : System α} (ass : g.IsDtime f) : g.IsNtime f :=
by
  rcases ass with ⟨-, hyp⟩
  exact hyp

theorem Language.InDtime.toNtime {f : ℕ → ℕ} {L : Language α} (ass : L.InDtime f) : L.InNtime f :=
by
  rcases ass with ⟨g, lang, time⟩
  exact ⟨g, lang, time.toNtime⟩
