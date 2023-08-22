import Thue.Classes


variable {α : Type}

theorem Ntime_to_RE (f : ℕ → ℕ) (L : Language α) : L.InNtime f → L.InRE :=
by
  rintro ⟨g, hyp, _⟩
  exact ⟨g, hyp⟩

lemma Dtime_is_Ntime {f : ℕ → ℕ} {g : System α} : g.IsDtime f → g.IsNtime f :=
by
  rintro ⟨_, hyp⟩
  exact hyp

theorem Dtime_in_Ntime (f : ℕ → ℕ) (L : Language α) : L.InDtime f → L.InNtime f :=
by
  rintro ⟨g, lang, time⟩
  exact ⟨g, lang, Dtime_is_Ntime time⟩
