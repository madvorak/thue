import Thue.Definition


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

private example : [alphabet.a_, alphabet.a_, alphabet.b_, alphabet.b_] ∈ mysys.language := by
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
