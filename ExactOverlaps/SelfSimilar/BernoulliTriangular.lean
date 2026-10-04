module

public import ExactOverlaps.SelfSimilar.TriangularAverages
public import ExactOverlaps.SelfSimilar.TerminalAverages

/-!
Triangular averaging for dominated convergent observables on a finite
Bernoulli shift. This is proved from the pointwise averaging theorem,
dominated tail oscillations, and the vanishing terminal-block estimate.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology

namespace ExactOverlaps.Bernoulli

variable {A : Type*} [MeasurableSpace A] [Fintype A]

theorem ae_tendsto_triangularAverage (p : Measure A) [IsProbabilityMeasure p]
    {F : ℕ → (ℕ → A) → ℝ} {f G : (ℕ → A) → ℝ}
    (hFm : ∀ n, Measurable (F n)) (hfm : Measurable f) (hGm : Measurable G)
    (hGi : Integrable G (sequenceLaw p))
    (hbound : ∀ᵐ ω ∂sequenceLaw p, (∀ n, |F n ω| ≤ G ω) ∧ |f ω| ≤ G ω)
    (hlim : ∀ᵐ ω ∂sequenceLaw p, Tendsto (fun n ↦ F n ω) atTop (𝓝 (f ω))) :
    ∀ᵐ ω ∂sequenceLaw p,
      Tendsto (fun n ↦ Ergodic.triangularAverage shift F n ω)
        atTop (𝓝 (∫ v, f v ∂sequenceLaw p)) := by
  let H := Ergodic.tailOscillation F f
  have hHm : ∀ m, Measurable (H m) := Ergodic.measurable_tailOscillation hFm hfm
  have hHi : ∀ m, Integrable (H m) (sequenceLaw p) := by
    intro m
    apply (hGi.const_mul 2).mono' (hHm m).aestronglyMeasurable
    filter_upwards [hbound] with ω hω
    have hh := Ergodic.tailOscillation_bounds hω.1 hω.2 m
    change ‖Ergodic.tailOscillation F f m ω‖ ≤ 2 * G ω
    simpa only [Real.norm_eq_abs, abs_of_nonneg hh.1] using hh.2
  have hfi : Integrable f (sequenceLaw p) := by
    apply hGi.mono' hfm.aestronglyMeasurable
    simpa only [Real.norm_eq_abs] using hbound.mono (fun _ h ↦ h.2)
  have hHint : Tendsto (fun m ↦ ∫ ω, H m ω ∂sequenceLaw p) atTop (𝓝 0) :=
    Ergodic.integral_tailOscillation_tendsto_zero hFm hfm hGi hbound hlim
  have hborbit : ∀ᵐ ω ∂sequenceLaw p, ∀ j : ℕ,
      (∀ n, |F n (shift^[j] ω)| ≤ G (shift^[j] ω)) ∧
        |f (shift^[j] ω)| ≤ G (shift^[j] ω) := by
    apply ae_all_iff.mpr
    intro j
    exact ((measurePreserving_shift p).iterate j).quasiMeasurePreserving.ae hbound
  have hHave : ∀ᵐ ω ∂sequenceLaw p, ∀ m : ℕ,
      Tendsto (fun n ↦ birkhoffAverage ℝ shift (H m) n ω)
        atTop (𝓝 (∫ v, H m v ∂sequenceLaw p)) :=
    ae_all_iff.mpr (fun m ↦ ae_tendsto_birkhoffAverage p (hHm m) (hHi m))
  filter_upwards [hborbit, hHave, ae_tendsto_birkhoffAverage p hfm hfi,
    ae_tendsto_birkhoffAverage p hGm hGi] with ω hb hH hf hG
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨m, hm⟩ := (hHint.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 4 by positivity))).exists
  have eH := (hH m).eventually (gt_mem_nhds
    (show (∫ v, H m v ∂sequenceLaw p) < (∫ v, H m v ∂sequenceLaw p) + ε / 4 by linarith))
  have ht := (Ergodic.terminal_orbit_sum_div_tendsto_zero shift G ω hG m).const_mul 2
  simp only [mul_zero] at ht
  have eT := ht.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 4 by positivity))
  have ef := (Metric.tendsto_nhds.mp hf) (ε / 4) (by positivity)
  filter_upwards [eH, eT, ef, eventually_ge_atTop m] with n hnH hnT hnf hmn
  rw [Real.dist_eq] at hnf ⊢
  have herr := Ergodic.triangularAverage_error_le shift (fun j ↦ (hb j).1)
    (fun j ↦ (hb j).2) hmn
  have htri := abs_sub_le (Ergodic.triangularAverage shift F n ω)
    (birkhoffAverage ℝ shift f n ω) (∫ v, f v ∂sequenceLaw p)
  change birkhoffAverage ℝ shift (Ergodic.tailOscillation F f m) n ω < _ at hnH
  linarith

end ExactOverlaps.Bernoulli
