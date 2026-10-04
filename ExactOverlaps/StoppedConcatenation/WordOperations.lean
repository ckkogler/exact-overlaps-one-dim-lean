/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.SelfSimilar.Words
public import ExactOverlaps.SelfSimilar.BernoulliBlocks
public import ExactOverlaps.Entropy.IndependentPair

/-! Exact splitting and concatenation of finite affine words. -/

@[expose] public section

open scoped ENNReal

namespace ExactOverlaps.SelfSimilar

namespace Word

variable {ι : Type*}

def append : (n m : ℕ) → Word ι n → Word ι m → Word ι (m + n)
  | 0, _, _, v => v
  | n + 1, m, w, v => (w.1, append n m w.2 v)

def split : (n m : ℕ) → Word ι (m + n) → Word ι n × Word ι m
  | 0, _, w => (PUnit.unit, w)
  | n + 1, m, w => let z := split n m w.2; ((w.1, z.1), z.2)

theorem split_append (n m : ℕ) (w : Word ι n) (v : Word ι m) :
    split n m (append n m w v) = (w, v) := by
  induction n with
  | zero => cases w; rfl
  | succ n ih =>
    change ((w.1, (split n m (append n m w.2 v)).1),
      (split n m (append n m w.2 v)).2) = (w, v)
    rw [ih]
    cases w
    rfl

theorem append_split (n m : ℕ) (w : Word ι (m + n)) :
    append n m (split n m w).1 (split n m w).2 = w := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (w.1, append n m (split n m w.2).1 (split n m w.2).2) = w
    rw [ih]
    cases w
    rfl

def appendEquiv (n m : ℕ) : Word ι n × Word ι m ≃ Word ι (m + n) where
  toFun := fun z ↦ append n m z.1 z.2
  invFun := split n m
  left_inv := fun z ↦ split_append n m z.1 z.2
  right_inv := append_split n m

/-- The first n symbols of a canonical sequence, as the existing recursive word type. -/
def read : (n : ℕ) → (ℕ → ι) → Word ι n
  | 0, _ => PUnit.unit
  | n + 1, ω => (ω 0, read n (Bernoulli.shift ω))

theorem read_append (n m : ℕ) (ω : ℕ → ι) :
    read (m + n) ω = append n m (read n ω) (read m (Bernoulli.shift^[n] ω)) := by
  induction n generalizing ω with
  | zero => rfl
  | succ n ih =>
    change (ω 0, read (m + n) (Bernoulli.shift ω)) =
      (ω 0, append n m (read n (Bernoulli.shift ω)) (read m (Bernoulli.shift^[n + 1] ω)))
    rw [ih]
    rw [Function.iterate_succ_apply]

end Word

namespace System

variable {ι : Type*} [Fintype ι]

theorem wordWeight_append (S : System ι) (n m : ℕ) (w : Word ι n) (v : Word ι m) :
    S.wordWeight (m + n) (Word.append n m w v) = S.wordWeight n w * S.wordWeight m v := by
  induction n with
  | zero => simp only [Word.append, wordWeight, one_mul, Nat.add_zero]
  | succ n ih =>
    change (S.weight w.1 : ℝ≥0∞) * S.wordWeight (m + n) (Word.append n m w.2 v) = _
    rw [ih]
    exact (mul_assoc _ _ _).symm

theorem wordMap_append (S : System ι) (n m : ℕ) (w : Word ι n) (v : Word ι m) :
    S.wordMap (m + n) (Word.append n m w v) = (S.wordMap n w).comp (S.wordMap m v) := by
  induction n with
  | zero => simp only [Word.append, wordMap, RealSimilarity.identity_comp, Nat.add_zero]
  | succ n ih =>
    change (S.map w.1).comp (S.wordMap (m + n) (Word.append n m w.2 v)) = _
    rw [ih]
    exact (RealSimilarity.comp_assoc _ _ _).symm

end System
end ExactOverlaps.SelfSimilar
