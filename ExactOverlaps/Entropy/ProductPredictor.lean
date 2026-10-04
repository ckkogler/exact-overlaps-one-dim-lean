module

public import ExactOverlaps.Entropy.CrossEntropy

/-!
# Algebra of the product binary predictor

The two nonnegative evidence weights are normalized to a probability. On
each actually possible outcome its logarithmic loss is a log-one-plus-odds
expression, and the square-root bound factors into the two marginal odds.
-/

@[expose] public section

namespace ExactOverlaps.Entropy

noncomputable def productPredictor (A B : ℝ) : ℝ :=
  A * (1 - B) / (A * (1 - B) + (1 - A) * B)

lemma productPredictor_mem_Icc {A B : ℝ} (hA : A ∈ Set.Icc 0 1) (hB : B ∈ Set.Icc 0 1) :
    productPredictor A B ∈ Set.Icc 0 1 := by
  have hU := mul_nonneg hA.1 (sub_nonneg.mpr hB.2)
  have hV := mul_nonneg (sub_nonneg.mpr hA.2) hB.1
  refine ⟨div_nonneg hU (add_nonneg hU hV), ?_⟩
  by_cases hd : A * (1 - B) + (1 - A) * B = 0
  · simp [productPredictor, hd]
  · have hdpos : 0 < A * (1 - B) + (1 - A) * B := lt_of_le_of_ne (add_nonneg hU hV) (Ne.symm hd)
    exact (div_le_one hdpos).mpr (le_add_of_nonneg_right hV)

lemma productPredictor_pos {A B : ℝ} (hA : 0 < A) (hB : B < 1)
    (hV : 0 ≤ (1 - A) * B) : 0 < productPredictor A B := by
  have hU := mul_pos hA (sub_pos.mpr hB)
  exact div_pos hU (add_pos_of_pos_of_nonneg hU hV)

lemma productPredictor_lt_one {A B : ℝ} (hA : A < 1) (hB : 0 < B)
    (hU : 0 ≤ A * (1 - B)) : productPredictor A B < 1 := by
  have hV := mul_pos (sub_pos.mpr hA) hB
  exact (div_lt_one (add_pos_of_nonneg_of_pos hU hV)).mpr (lt_add_of_pos_right _ hV)

lemma neg_log_normalized_weight {U V : ℝ} (hU : 0 < U) (hV : 0 ≤ V) :
    -Real.log (U / (U + V)) = Real.log (1 + V / U) := by
  rw [← Real.log_inv]
  congr 1
  field_simp

lemma productPredictor_true_loss_le {A B : ℝ}
    (hA : A ∈ Set.Ioc 0 1) (hB : B ∈ Set.Ico 0 1) :
    -Real.log (productPredictor A B) ≤
      Real.sqrt ((1 - A) / A) * Real.sqrt (B / (1 - B)) := by
  have hU := mul_pos hA.1 (sub_pos.mpr hB.2)
  have hV := mul_nonneg (sub_nonneg.mpr hA.2) hB.1
  rw [productPredictor, neg_log_normalized_weight hU hV]
  apply (log_one_add_le_sqrt (div_nonneg hV hU.le)).trans_eq
  have he : (1 - A) * B / (A * (1 - B)) = ((1 - A) / A) * (B / (1 - B)) := by
    field_simp
  rw [he, Real.sqrt_mul (div_nonneg (sub_nonneg.mpr hA.2) hA.1.le)]

lemma productPredictor_false_loss_le {A B : ℝ}
    (hA : A ∈ Set.Ico 0 1) (hB : B ∈ Set.Ioc 0 1) :
    -Real.log (1 - productPredictor A B) ≤
      Real.sqrt (A / (1 - A)) * Real.sqrt ((1 - B) / B) := by
  have hU := mul_nonneg hA.1 (sub_nonneg.mpr hB.2)
  have hV := mul_pos (sub_pos.mpr hA.2) hB.1
  have hd : A * (1 - B) + (1 - A) * B ≠ 0 := (add_pos_of_nonneg_of_pos hU hV).ne'
  have he : 1 - productPredictor A B =
      ((1 - A) * B) / (((1 - A) * B) + A * (1 - B)) := by
    unfold productPredictor
    rw [add_comm ((1 - A) * B)]
    apply (eq_div_iff hd).mpr
    rw [sub_mul, one_mul, div_mul_cancel₀ _ hd]
    ring
  rw [he, neg_log_normalized_weight hV hU]
  apply (log_one_add_le_sqrt (div_nonneg hU hV.le)).trans_eq
  have hfactor : A * (1 - B) / ((1 - A) * B) = (A / (1 - A)) * ((1 - B) / B) := by
    field_simp
  rw [hfactor, Real.sqrt_mul (div_nonneg hA.1 (sub_nonneg.mpr hA.2.le))]

end ExactOverlaps.Entropy
