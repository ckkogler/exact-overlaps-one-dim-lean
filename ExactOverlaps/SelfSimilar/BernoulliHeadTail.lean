module

public import ExactOverlaps.SelfSimilar.BernoulliBlocks
public import Mathlib.Probability.Independence.ZeroOne

/-!
The head symbol and shifted tail of the one-sided Bernoulli sequence are
independent. Their joint law is the product of the alphabet law and the
original sequence law.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace ExactOverlaps.Bernoulli

variable {A : Type*} [MeasurableSpace A]

theorem independent_head_shift (p : Measure A) [IsProbabilityMeasure p] :
    IndepFun (fun ω : ℕ → A ↦ ω 0) shift (sequenceLaw p) := by
  let σ : ℕ → MeasurableSpace (ℕ → A) :=
    fun n ↦ MeasurableSpace.comap (fun ω : ℕ → A ↦ ω n) inferInstance
  have hind : iIndepFun (fun n (ω : ℕ → A) ↦ ω n) (sequenceLaw p) :=
    iIndepFun_infinitePi (X := fun _ x ↦ x) (fun _ ↦ measurable_id)
  have hσ : ∀ n, σ n ≤ (inferInstance : MeasurableSpace (ℕ → A)) :=
    fun n ↦ (measurable_pi_apply n).comap_le
  have hs := indep_biSup_compl hσ hind.iIndep ({0} : Set ℕ)
  change Indep (σ 0) (MeasurableSpace.comap shift inferInstance) (sequenceLaw p)
  apply indep_of_indep_of_le hs
  · exact le_iSup_of_le 0 (le_iSup_of_le (Set.mem_singleton 0) le_rfl)
  · have heq : (shift : (ℕ → A) → (ℕ → A)) = fun ω n ↦ ω (n + 1) := rfl
    rw [heq, MeasurableSpace.comap_process_pi]
    apply iSup_le
    intro n
    exact le_iSup_of_le (n + 1) (le_iSup_of_le (by simp : n + 1 ∈ ({0} : Set ℕ)ᶜ) le_rfl)

theorem head_shift_map (p : Measure A) [IsProbabilityMeasure p] :
    (sequenceLaw p).map (fun ω ↦ (ω 0, shift ω)) = p.prod (sequenceLaw p) := by
  rw [(independent_head_shift p).map_prod_eq_prod_map_map
    (measurable_pi_apply 0).aemeasurable measurable_shift.aemeasurable,
    (measurePreserving_shift p).map_eq]
  change (Measure.map (fun ω : ℕ → A ↦ ω 0) (Measure.infinitePi (fun _ : ℕ ↦ p))).prod _ = _
  rw [Measure.infinitePi_map_eval]

end ExactOverlaps.Bernoulli
