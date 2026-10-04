module

public import ExactOverlaps.SelfSimilar.RatioComponentBound
public import ExactOverlaps.SelfSimilar.RatioLevelConcentration
public import ExactOverlaps.SelfSimilar.RatioLevelWindows

/-!
Actual ratio levels are clamped only on exceptional classes, to keep every
component between the common coarse and fine scales. On typical classes the
level is unchanged. The discarded class probability tends to zero.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology BigOperators Classical

namespace ExactOverlaps.SelfSimilar

def clampLevel (i f j : ℤ) : ℤ := max i (min f j)

theorem le_clampLevel (i f j : ℤ) : i ≤ clampLevel i f j := le_max_left _ _

theorem clampLevel_le {i f : ℤ} (hif : i ≤ f) (j : ℤ) : clampLevel i f j ≤ f :=
  max_le hif (min_le_left _ _)

theorem clampLevel_eq {i f j : ℤ} (hij : i ≤ j) (hjf : j ≤ f) : clampLevel i f j = j := by
  simp only [clampLevel, min_eq_right hjf, max_eq_right hij]

theorem bufferedRatioLevel_le_target {κ ε q : ℝ} (hκ : 0 ≤ κ) (hε : 0 ≤ ε) (hq : 1 ≤ q) (n : ℕ) :
    bufferedRatioLevel κ ε n ≤ targetRatioLevel κ q n := by
  apply Int.floor_mono
  have hmul := mul_le_mul_of_nonneg_right hq hκ
  apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg n)
  nlinarith

namespace System

open Entropy
variable {ι : Type*} [Fintype ι]

noncomputable def typicalRatioClasses (S : System ι) (ε : ℝ) (n : ℕ) :
    Finset (S.wordRatioLaw n).support :=
  letI : Fintype (S.wordRatioLaw n).support := (S.wordRatioLaw_support_finite n).fintype
  Finset.univ.filter (fun r ↦ (S.dyadicLyapunov - ε) * n ≤ (ratioLevel r : ℝ) ∧
    (ratioLevel r : ℝ) ≤ (S.dyadicLyapunov + ε) * n)

theorem mem_typicalRatioClasses (S : System ι) (ε : ℝ) (n : ℕ) (r : (S.wordRatioLaw n).support) :
    r ∈ S.typicalRatioClasses ε n ↔ (S.dyadicLyapunov - ε) * n ≤ (ratioLevel r : ℝ) ∧
      (ratioLevel r : ℝ) ≤ (S.dyadicLyapunov + ε) * n := by
  simp only [typicalRatioClasses, Finset.mem_filter, Finset.mem_univ, true_and]

theorem typicalRatioClasses_badMass_tendsto_zero (S : System ι) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ S.ratioClassBadMass n (S.typicalRatioClasses ε n)) atTop (𝓝 0) := by
  have he (n : ℕ) : S.ratioClassBadMass n (S.typicalRatioClasses ε n) =
      ((S.wordRatioLaw n).toMeasure (S.atypicalRatioLevelSet ε n)).toReal := by
    rw [S.wordRatioLaw_mass_eq_support_sum n _ (S.measurableSet_atypicalRatioLevelSet ε n)]
    unfold ratioClassBadMass
    apply Finset.sum_congr rfl
    intro r _
    by_cases hr : r ∈ S.typicalRatioClasses ε n
    · have ht := (S.mem_typicalRatioClasses ε n r).mp hr
      simp [hr, atypicalRatioLevelSet, ht]
    · have ht := not_congr (S.mem_typicalRatioClasses ε n r) |>.mp hr
      simp [hr, atypicalRatioLevelSet, ht]
  simp_rw [he]
  exact S.wordRatioLaw_atypical_level_mass_tendsto_zero hε

noncomputable def ratioComponentLevel (S : System ι) (ε q : ℝ) (n : ℕ)
    (r : (S.wordRatioLaw n).support) : ℤ :=
  clampLevel (bufferedRatioLevel S.dyadicLyapunov ε n) (targetRatioLevel S.dyadicLyapunov q n)
    (ratioLevel r)

theorem eventually_typical_component_levels (S : System ι) {ε q : ℝ}
    (hε : 0 < ε) (hgap : 0 < (q - 1) * S.dyadicLyapunov - ε) (N : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ r ∈ S.typicalRatioClasses ε n,
      S.ratioComponentLevel ε q n r = ratioLevel r ∧
      N ≤ (targetRatioLevel S.dyadicLyapunov q n - S.ratioComponentLevel ε q n r).toNat := by
  filter_upwards [eventually_typical_level_buffers hε hgap N] with n hn
  intro r hr
  obtain ⟨hlo, hhi⟩ := (S.mem_typicalRatioClasses ε n r).mp hr
  obtain ⟨hleft, hright⟩ := hn (ratioLevel r) hlo hhi
  have hbase : bufferedRatioLevel S.dyadicLyapunov ε n ≤ ratioLevel r := by omega
  have htop : ratioLevel r ≤ targetRatioLevel S.dyadicLyapunov q n := by omega
  have he : S.ratioComponentLevel ε q n r = ratioLevel r := clampLevel_eq hbase htop
  refine ⟨he, ?_⟩
  rw [he]
  omega

noncomputable def averageRatioLevelGap (S : System ι) (n : ℕ)
    (j : (S.wordRatioLaw n).support → ℤ) (i : ℤ) : ℝ :=
  letI : Fintype (S.wordRatioLaw n).support := (S.wordRatioLaw_support_finite n).fintype
  ∑ r : (S.wordRatioLaw n).support, (S.wordRatioLaw n r).toReal * ((j r - i : ℤ) : ℝ)

theorem typical_component_gap_le (S : System ι) {ε q : ℝ} {n : ℕ}
    (r : (S.wordRatioLaw n).support) (hr : r ∈ S.typicalRatioClasses ε n)
    (he : S.ratioComponentLevel ε q n r = ratioLevel r) :
    ((S.ratioComponentLevel ε q n r - bufferedRatioLevel S.dyadicLyapunov ε n : ℤ) : ℝ) ≤
      3 * ε * n + 1 := by
  have htyp := ((S.mem_typicalRatioClasses ε n r).mp hr).2
  have hfloor := Int.lt_floor_add_one ((S.dyadicLyapunov - 2 * ε) * n)
  rw [he]
  simp only [Int.cast_sub, bufferedRatioLevel]
  nlinarith

theorem eventually_averageRatioLevelGap_le (S : System ι) {ε q : ℝ}
    (hε : 0 < ε) (hq : 1 < q) (hgap : 0 < (q - 1) * S.dyadicLyapunov - ε) :
    ∀ᶠ n : ℕ in atTop,
      S.averageRatioLevelGap n (S.ratioComponentLevel ε q n) (bufferedRatioLevel S.dyadicLyapunov ε n) ≤
        3 * ε * n + 1 +
          ((targetRatioLevel S.dyadicLyapunov q n - bufferedRatioLevel S.dyadicLyapunov ε n : ℤ) : ℝ) *
            S.ratioClassBadMass n (S.typicalRatioClasses ε n) := by
  filter_upwards [S.eventually_typical_component_levels hε hgap 0] with n hn
  let : Fintype (S.wordRatioLaw n).support := (S.wordRatioLaw_support_finite n).fintype
  let i := bufferedRatioLevel S.dyadicLyapunov ε n
  let f := targetRatioLevel S.dyadicLyapunov q n
  let G := S.typicalRatioClasses ε n
  let B : ℝ := 3 * ε * n + 1
  let D : ℝ := ((f - i : ℤ) : ℝ)
  have hif : i ≤ f := bufferedRatioLevel_le_target S.dyadicLyapunov_pos.le hε.le hq.le n
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hpoint (r : (S.wordRatioLaw n).support) :
      ((S.ratioComponentLevel ε q n r - i : ℤ) : ℝ) ≤ B + D * (if r ∈ G then 0 else 1) := by
    by_cases hr : r ∈ G
    · have h := S.typical_component_gap_le r hr (hn r hr).1
      simpa only [hr, ite_true, mul_zero, add_zero] using h
    · have hj : S.ratioComponentLevel ε q n r ≤ f := clampLevel_le hif _
      have hle : ((S.ratioComponentLevel ε q n r - i : ℤ) : ℝ) ≤ D := by
        dsimp [D]
        exact_mod_cast sub_le_sub_right hj i
      simp only [hr, ite_false, mul_one]
      linarith
  have hmass : (∑ r : (S.wordRatioLaw n).support, (S.wordRatioLaw n r).toReal) = 1 :=
    sum_pmf_toReal (supportLaw (S.wordRatioLaw n))
  have hb : (∑ r : (S.wordRatioLaw n).support,
      (S.wordRatioLaw n r).toReal * (D * (if r ∈ G then 0 else 1))) = D * S.ratioClassBadMass n G := by
    unfold ratioClassBadMass
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    split_ifs
    · simp only [mul_zero]
    · simp only [mul_one]
      ring
  have h := Finset.sum_le_sum (s := Finset.univ) (fun r _ ↦
    mul_le_mul_of_nonneg_left (hpoint r)
      (show 0 ≤ (S.wordRatioLaw n r).toReal from ENNReal.toReal_nonneg))
  simp only [mul_add, Finset.sum_add_distrib] at h
  rw [← Finset.sum_mul, hmass, one_mul, hb] at h
  exact h

end System
end ExactOverlaps.SelfSimilar
