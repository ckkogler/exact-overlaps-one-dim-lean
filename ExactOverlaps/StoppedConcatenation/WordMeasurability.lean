/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.StoppedConcatenation.WordOperations
public import ExactOverlaps.StoppedConcatenation.StoppingRules

/-! Finite word observations use precisely the increments available at their time. -/

@[expose] public section

open MeasureTheory

namespace ExactOverlaps.SelfSimilar.Word

variable {ι : Type*}

instance measurableSpace [MeasurableSpace ι] : (n : ℕ) → MeasurableSpace (Word ι n)
  | 0 => inferInstanceAs (MeasurableSpace PUnit)
  | n + 1 => letI := measurableSpace n
             inferInstanceAs (MeasurableSpace (ι × Word ι n))

instance measurableSingletonClass [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (n : ℕ) : MeasurableSingletonClass (Word ι n) := by
  induction n with
  | zero => exact inferInstanceAs (MeasurableSingletonClass PUnit)
  | succ n ih => exact inferInstanceAs (MeasurableSingletonClass (ι × Word ι n))

def ofBlock : (n : ℕ) → (Fin n → ι) → Word ι n
  | 0, _ => PUnit.unit
  | n + 1, w => (w 0, ofBlock n (fun k ↦ w k.succ))

theorem read_eq_ofBlock (n : ℕ) (ω : ℕ → ι) :
    read n ω = ofBlock n (Bernoulli.block n 0 ω) := by
  induction n generalizing ω with
  | zero => rfl
  | succ n ih =>
    change (ω 0, read n (Bernoulli.shift ω)) =
      (ω 0, ofBlock n (fun k ↦ ω (0 + (k.succ : ℕ))))
    rw [ih]
    rfl

theorem read_eq_of_prefix_eq (n : ℕ) {ω ω' : ℕ → ι}
    (h : ∀ k < n, ω k = ω' k) : read n ω = read n ω' := by
  rw [read_eq_ofBlock, read_eq_ofBlock]
  congr 1
  funext k
  exact h (0 + k) (by simp)

def prepend : (n : ℕ) → Word ι n → (ℕ → ι) → (ℕ → ι)
  | 0, _, ω => ω
  | n + 1, w, ω => fun k ↦ match k with
      | 0 => w.1
      | k + 1 => prepend n w.2 ω k

theorem shift_prepend (n : ℕ) (w : Word ι (n + 1)) (ω : ℕ → ι) :
    Bernoulli.shift (prepend (n + 1) w ω) = prepend n w.2 ω := rfl

theorem read_prepend (n : ℕ) (w : Word ι n) (ω : ℕ → ι) :
    read n (prepend n w ω) = w := by
  induction n with
  | zero => cases w; rfl
  | succ n ih =>
    change (w.1, read n (prepend n w.2 ω)) = w
    rw [ih]
    cases w
    rfl

theorem shift_iterate_prepend (n : ℕ) (w : Word ι n) (ω : ℕ → ι) :
    Bernoulli.shift^[n] (prepend n w ω) = ω := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, shift_prepend]
    exact ih w.2

variable [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

theorem measurable_read_at (n : ℕ) :
    Measurable[StoppedConcatenation.incrementFiltration (ι := ι) n] (read n) := by
  rw [StoppedConcatenation.incrementFiltration_eq_comap_block]
  have hb : Measurable[MeasurableSpace.comap (Bernoulli.block n 0) inferInstance]
      (Bernoulli.block (A := ι) n 0) := Measurable.of_comap_le le_rfl
  have h := (measurable_of_finite (ofBlock (ι := ι) n)).comp hb
  have he : (read (ι := ι) n) = ofBlock n ∘ Bernoulli.block n 0 :=
    funext (read_eq_ofBlock n)
  rw [he]
  exact h

theorem measurable_read (n : ℕ) : Measurable (read (ι := ι) n) :=
  (measurable_read_at n).mono (StoppedConcatenation.incrementFiltration.le n) le_rfl

end ExactOverlaps.SelfSimilar.Word
