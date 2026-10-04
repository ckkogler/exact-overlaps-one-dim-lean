/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import ExactOverlaps.StoppedConcatenation.StoppingRules

/-! Every ordinary bounded WithTop-valued stopping time gives the same finite rule. -/

@[expose] public section

open MeasureTheory

namespace ExactOverlaps.StoppedConcatenation.BoundedStoppingRule

variable {ι : Type*} [MeasurableSpace ι]

omit [MeasurableSpace ι] in
theorem coe_untopD_of_bounded (τ : (ℕ → ι) → WithTop ℕ) (N : ℕ)
    (h : ∀ ω, τ ω ≤ N) (ω : ℕ → ι) :
    (((τ ω).untopD (0 : ℕ) : ℕ) : WithTop ℕ) = τ ω := by
  cases he : τ ω with
  | top => have hb := h ω; simp [he] at hb
  | coe n => rfl

def ofWithTop (τ : (ℕ → ι) → WithTop ℕ)
    (hτ : IsStoppingTime incrementFiltration τ) (N : ℕ) (h : ∀ ω, τ ω ≤ N) :
    BoundedStoppingRule ι where
  time := fun ω ↦ (τ ω).untopD 0
  horizon := N
  bounded := fun ω ↦ by
    have hb := h ω
    rw [← coe_untopD_of_bounded τ N h ω] at hb
    exact_mod_cast hb
  adapted := by
    have heq : (fun ω ↦ (((τ ω).untopD (0 : ℕ) : ℕ) : WithTop ℕ)) = τ :=
      funext (coe_untopD_of_bounded τ N h)
    rw [heq]
    exact hτ

theorem ofWithTop_time (τ : (ℕ → ι) → WithTop ℕ)
    (hτ : IsStoppingTime incrementFiltration τ) (N : ℕ) (h : ∀ ω, τ ω ≤ N)
    (ω : ℕ → ι) :
    ((ofWithTop τ hτ N h).time ω : WithTop ℕ) = τ ω :=
  coe_untopD_of_bounded τ N h ω

/-- Truncation supplies a pointwise bounded representative of every a.e. bounded rule. -/
def truncate (τ : (ℕ → ι) → WithTop ℕ)
    (hτ : IsStoppingTime incrementFiltration τ) (N : ℕ) : BoundedStoppingRule ι :=
  ofWithTop (fun ω ↦ min (τ ω) N) (hτ.min (isStoppingTime_const _ N)) N
    (fun _ ↦ min_le_right _ _)

theorem truncate_time_eq_ae (τ : (ℕ → ι) → WithTop ℕ)
    (hτ : IsStoppingTime incrementFiltration τ) (N : ℕ) (μ : Measure (ℕ → ι))
    (h : ∀ᵐ ω ∂μ, τ ω ≤ N) :
    (fun ω ↦ ((truncate τ hτ N).time ω : WithTop ℕ)) =ᵐ[μ] τ := by
  filter_upwards [h] with ω hω
  change ((ofWithTop (fun ω ↦ min (τ ω) N) _ N _).time ω : WithTop ℕ) = τ ω
  rw [ofWithTop_time, min_eq_left hω]

end ExactOverlaps.StoppedConcatenation.BoundedStoppingRule
