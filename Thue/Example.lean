import Thue.Determinisms


private inductive alphabet
  | a_ : alphabet
  | b_ : alphabet

private inductive specials
  | S_ : specials

private def Symb : Type := Symbol alphabet specials

private def a : Symb := Symbol.letter alphabet.a_
private def b : Symb := Symbol.letter alphabet.b_
private def S : Symb := Symbol.marker specials.S_

private def ruleSkip : Rule alphabet specials := ⟨[S, a], [a, S]⟩
private def ruleAnih : Rule alphabet specials := ⟨[a, S, b], [S]⟩

private def mysys : System alphabet := ⟨specials, specials.S_, specials.S_, [ruleSkip, ruleAnih]⟩

private example : [alphabet.a_, alphabet.a_, alphabet.b_, alphabet.b_] ∈ mysys.Semidecides := by
  use 4
  have lastStep : mysys.Transforms [a, S, b] [S]
  · use ruleAnih
    constructor
    · simp [mysys]
    use [], []
    simp [ruleAnih]
  apply System.Derives.tail _ _ _ _ _ lastStep
  have prevStep : mysys.Transforms [a, a, S, b, b] [a, S, b]
  · use ruleAnih
    constructor
    · simp [mysys]
    use [a], [b]
    simp [ruleAnih]
  apply System.Derives.tail _ _ _ _ _ prevStep
  have sndStep : mysys.Transforms [a, S, a, b, b] [a, a, S, b, b]
  · use ruleSkip
    constructor
    · simp [mysys]
    use [a], [b, b]
    simp [ruleSkip]
  apply System.Derives.tail _ _ _ _ _ sndStep
  have fstStep : mysys.Transforms [S, a, a, b, b] [a, S, a, b, b]
  · use ruleSkip
    constructor
    · simp [mysys]
    use [], [a, b, b]
    simp [ruleSkip]
  apply System.Derives.tail _ _ _ _ _ fstStep
  apply System.Derives.refl

private lemma ruleSkip_doesnt_overlap_ruleAnih :
  ¬ actuallyOverlap ruleSkip.input ruleAnih.input :=
by
  intro overlap
  unfold actuallyOverlap at overlap
  rcases overlap with ⟨t, ⟨t₁, t₂, t₃, teq⟩, ⟨r₁, r₃, t_of_r⟩, ⟨q₁, q₃, t_of_q⟩⟩
  rw [teq] at t_of_r t_of_q
  dsimp only [ruleSkip] at t_of_r
  dsimp only [ruleAnih] at t_of_q
  rw [←List.three_singletons_eq_tripleton] at t_of_q
  rw [←List.append_assoc, ←List.append_assoc, List.append_assoc _ [b]] at t_of_q
  have := match_xYz t_of_q sorry sorry
  sorry

private example : mysys.IsDeterministic :=
by
  apply deterministic_of_deterministicSyntax
  constructor
  · intros r rin
    unfold mysys at rin
    rw [List.mem_doubleton] at rin
    cases rin with
    | inl rSkip =>
      constructor
      · use [], specials.S_, [alphabet.a_]
        rw [rSkip]
        rfl
      · use [alphabet.a_], specials.S_, []
        rw [rSkip]
        rfl
    | inr rAnih =>
      constructor
      · use [alphabet.a_], specials.S_, [alphabet.b_]
        rw [rAnih]
        rfl
      · use [], specials.S_, []
        rw [rAnih]
        rfl
  · intros r rin q qin overlap
    unfold mysys at rin qin
    rw [List.mem_doubleton] at rin qin
    cases rin with
    | inl rSkip =>
      cases qin with
      | inl qSkip =>
        rw [rSkip, qSkip]
      | inr qAnih =>
        exfalso
        rw [rSkip, qAnih] at overlap
        exact ruleSkip_doesnt_overlap_ruleAnih overlap
    | inr rAnih =>
      cases qin with
      | inl qSkip =>
        exfalso
        rw [rAnih, qSkip, actuallyOverlap_symm] at overlap
        exact ruleSkip_doesnt_overlap_ruleAnih overlap
      | inr qAnih =>
        rw [rAnih, qAnih]
