module

public import ExactOverlaps.SelfSimilar.Words

/-!
Uniform geometric bounds for finite random compositions, before taking any
stationary limit. Signed contraction factors are bounded through absolute
values; the translation and joint laws are genuine finite pushforwards.
-/

@[expose] public section

namespace ExactOverlaps.SelfSimilar.System

variable {ι : Type*} [Fintype ι]

theorem abs_wordRatio_le_pow (S : System ι) {c : ℝ} (hc : 0 ≤ c)
    (hmax : ∀ i, |(S.map i).ratio| ≤ c) (n : ℕ) (w : Word ι n) :
    |S.wordRatio n w| ≤ c ^ n := by
  induction n with
  | zero => simp [wordRatio, wordMap, RealSimilarity.identity]
  | succ n ih =>
    rw [wordRatio_succ, abs_mul, pow_succ']
    exact mul_le_mul (hmax w.1) (ih w.2) (abs_nonneg _) hc

theorem abs_wordTranslation_le (S : System ι) {c M : ℝ}
    (hc : 0 ≤ c) (hc1 : c < 1) (hM : 0 ≤ M)
    (hmax : ∀ i, |(S.map i).ratio| ≤ c) (hshift : ∀ i, |(S.map i).shift| ≤ M)
    (n : ℕ) (w : Word ι n) : |S.wordTranslation n w| ≤ M / (1 - c) := by
  have hbound : 0 ≤ M / (1 - c) := div_nonneg hM (sub_pos.mpr hc1).le
  have hfix : c * (M / (1 - c)) + M = M / (1 - c) := by
    have hden : 1 - c ≠ 0 := (sub_pos.mpr hc1).ne'
    field_simp [hden]
    ring
  induction n with
  | zero => simpa [wordTranslation, wordMap, RealSimilarity.identity] using hbound
  | succ n ih =>
    rw [wordTranslation_succ]
    calc
      |(S.map w.1).ratio * S.wordTranslation n w.2 + (S.map w.1).shift| ≤
          |(S.map w.1).ratio| * |S.wordTranslation n w.2| + |(S.map w.1).shift| := by
        simpa only [abs_mul] using abs_add_le
          ((S.map w.1).ratio * S.wordTranslation n w.2) (S.map w.1).shift
      _ ≤ c * (M / (1 - c)) + M :=
        add_le_add (mul_le_mul (hmax w.1) (ih w.2) (abs_nonneg _) hc) (hshift w.1)
      _ = M / (1 - c) := hfix

/-- The law of the full affine random composition, retaining exact overlaps. -/
noncomputable def wordSimilarityLaw (S : System ι) (n : ℕ) : PMF RealSimilarity :=
  (S.wordLaw n).map (S.wordMap n)

/-- The law of its translation coordinate. -/
noncomputable def wordTranslationLaw (S : System ι) (n : ℕ) : PMF ℝ :=
  (S.wordLaw n).map (S.wordTranslation n)

/-- The joint law used in Hochman's nonuniform contraction theorem. -/
noncomputable def jointWordLaw (S : System ι) (n : ℕ) : PMF (ℝ × ℝ) :=
  (S.wordLaw n).map (fun w ↦ (S.wordTranslation n w, S.wordRatio n w))

theorem wordSimilarityLaw_support_finite (S : System ι) (n : ℕ) :
    (S.wordSimilarityLaw n).support.Finite := by
  rw [wordSimilarityLaw, PMF.support_map]
  exact (Set.toFinite _).image _

theorem wordTranslationLaw_support_finite (S : System ι) (n : ℕ) :
    (S.wordTranslationLaw n).support.Finite := by
  rw [wordTranslationLaw, PMF.support_map]
  exact (Set.toFinite _).image _

theorem jointWordLaw_support_finite (S : System ι) (n : ℕ) :
    (S.jointWordLaw n).support.Finite := by
  rw [jointWordLaw, PMF.support_map]
  exact (Set.toFinite _).image _

theorem jointWordLaw_map_fst (S : System ι) (n : ℕ) :
    (S.jointWordLaw n).map Prod.fst = S.wordTranslationLaw n := by
  simp only [jointWordLaw, wordTranslationLaw, PMF.map_comp, Function.comp_def]

/-- All finite translation laws share a bounded interval, without a separation assumption. -/
theorem exists_uniform_translation_bound (S : System ι) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ, ∀ b ∈ (S.wordTranslationLaw n).support, |b| ≤ B := by
  obtain ⟨c, M, hc, hc1, hM, hmax, hshift⟩ := S.exists_uniform_bounds
  refine ⟨M / (1 - c), div_nonneg hM (sub_pos.mpr hc1).le, ?_⟩
  intro n b hb
  obtain ⟨w, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hb
  exact S.abs_wordTranslation_le hc.le hc1 hM hmax hshift n w

end ExactOverlaps.SelfSimilar.System
