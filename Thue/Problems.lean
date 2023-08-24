import Mathlib.Computability.Language


structure clause3SAT (n : ℕ) where
  (i j k : Fin n)
  (p q r : Bool)

structure struct3SAT where
  n : ℕ
  clauses : List (clause3SAT n)

def satisfiable3SAT (S : struct3SAT) : Prop :=
  ∃ x : Fin S.n → Bool, ∀ c ∈ S.clauses,
    x c.i = c.p ∨ x c.j = c.q ∨ x c.k = c.r


def encode_literal {n : ℕ} (i : Fin n) (p : Bool) : List (Fin 4) :=
  List.replicate i.val.succ (if p then 1 else 0)

def encode_clause3 {n : ℕ} (c : clause3SAT n) : List (Fin 4) :=
  3 :: encode_literal c.i c.p ++ 2 :: encode_literal c.j c.q ++ 2 :: encode_literal c.k c.r

def encode_3SAT (S : struct3SAT) : List (Fin 4) :=
  List.replicate S.n 1 ++ (S.clauses.map encode_clause3).join

def lang3SAT : Language (Fin 4) :=
  { s | ∃ S : struct3SAT, s = encode_3SAT S ∧ satisfiable3SAT S }
