module

public import ExactOverlaps.SelfSimilar.CodingMassTelescoping

/-!
The logarithmic ball mass has a constant almost-sure rate at the actual
prefix contraction radii. The rate is obtained from the proved symbol
and conditional-information averages, through exact telescoping.
-/

@[expose] public section

open MeasureTheory Filter Metric
open scoped ENNReal Topology

namespace ExactOverlaps.SelfSimilar.System

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

noncomputable def codingLogMassRate (S : System ι) : ℝ :=
  (∫ v, S.headLogWeight v ∂Bernoulli.sequenceLaw S.alphabetLaw.toMeasure) +
    ∫ v, S.branchInformation S.codingMeasure (v 0) (S.coding v)
      ∂Bernoulli.sequenceLaw S.alphabetLaw.toMeasure

theorem ae_log_prefixBallMass_div_tendsto (S : System ι) {r : ℝ} (hr : 0 < r)
    (hbase : ∀ ω : ℕ → ι, S.codingMeasure (closedBall (S.coding ω) r) = 1) :
    ∀ᵐ ω ∂Bernoulli.sequenceLaw S.alphabetLaw.toMeasure,
      Tendsto (fun n : ℕ ↦ Real.log (S.prefixBallMass r n ω).toReal / n)
        atTop (𝓝 S.codingLogMassRate) := by
  have hm : ∀ᵐ ω ∂Bernoulli.sequenceLaw S.alphabetLaw.toMeasure,
      ∀ j n : ℕ, 0 < S.prefixBallMass r n (Bernoulli.shift^[j] ω) := by
    apply ae_all_iff.mpr
    intro j
    exact ((Bernoulli.measurePreserving_shift S.alphabetLaw.toMeasure).iterate j).quasiMeasurePreserving.ae (S.ae_prefixBallMass_pos hr)
  filter_upwards [hm, S.ae_coding_weight_pos, S.ae_headLogWeight_average,
    S.ae_prefixBranchInformation_triangular_average hr] with ω hmω hw hhead hbranch
  have h := hhead.add hbranch
  apply h.congr
  intro n
  have htel := S.log_prefixBallMass_telescoping r n ω (fun j ↦ (hw j).ne') hmω
  have hzero : S.prefixBallMass r 0 (Bernoulli.shift^[n] ω) = 1 := by
    simpa only [prefixBallMass, prefixRatio, Finset.range_zero, Finset.prod_empty,
      abs_one, one_mul] using hbase (Bernoulli.shift^[n] ω)
  rw [hzero, ENNReal.toReal_one, Real.log_one, add_zero] at htel
  simp only [birkhoffAverage, smul_eq_mul, ← div_eq_inv_mul, Ergodic.triangularAverage,
    ← add_div, ← htel]

theorem ae_log_prefix_radius_div_tendsto (S : System ι) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ ω ∂Bernoulli.sequenceLaw S.alphabetLaw.toMeasure,
      Tendsto (fun n : ℕ ↦ Real.log (|S.prefixRatio n ω| * r) / n)
        atTop (𝓝 S.lyapunov) := by
  filter_upwards [S.ae_log_abs_prefixRatio_div_tendsto] with ω hω
  have h := hω.add ((tendsto_const_nhds (x := Real.log r)).div_atTop tendsto_natCast_atTop_atTop)
  simp only [add_zero] at h
  apply h.congr
  intro n
  rw [Real.log_mul (abs_ne_zero.mpr (S.prefixRatio_ne_zero n ω)) hr.ne', add_div]

theorem ae_prefix_local_dimension_limit (S : System ι) {r : ℝ} (hr : 0 < r)
    (hbase : ∀ ω : ℕ → ι, S.codingMeasure (closedBall (S.coding ω) r) = 1) :
    ∀ᵐ ω ∂Bernoulli.sequenceLaw S.alphabetLaw.toMeasure,
      Tendsto (fun n : ℕ ↦ Real.log (S.prefixBallMass r n ω).toReal /
        Real.log (|S.prefixRatio n ω| * r)) atTop (𝓝 (S.codingLogMassRate / S.lyapunov)) := by
  filter_upwards [S.ae_log_prefixBallMass_div_tendsto hr hbase,
    S.ae_log_prefix_radius_div_tendsto hr] with ω hmass hradius
  apply (hmass.div hradius S.lyapunov_neg.ne).congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact div_div_div_cancel_right₀ (by exact_mod_cast hn.ne') _ _

end ExactOverlaps.SelfSimilar.System
