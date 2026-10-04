module

public import ExactOverlaps.SelfSimilar.BoundedWords
public import ExactOverlaps.StoppedConcatenation.WordOperations
public import ExactOverlaps.EntropyEnergyGap.DigitCopies

/-! Exact bounded-length blocks and their ordered affine digit-sum identity. -/

@[expose] public section

open scoped BigOperators Classical

namespace ExactOverlaps.SelfSimilar

def blockLength (N r : ℕ) : ℕ → ℕ
  | 0 => r
  | L + 1 => blockLength N r L + N

theorem blockLength_eq (N r L : ℕ) : blockLength N r L = r + N * L := by
  induction L with
  | zero => simp [blockLength]
  | succ L ih => simp only [blockLength, ih, Nat.mul_succ]; omega

def boundedBlockEncode {ι : Type*} {N r : ℕ} (hr : r ≤ N) :
    (L : ℕ) → Word ι (blockLength N r L) → Fin (L + 1) → BoundedWord ι N
  | 0, w => fun _ ↦ ⟨⟨r, Nat.lt_succ_of_le hr⟩, w⟩
  | L + 1, w =>
    let z := Word.split N (blockLength N r L) w
    Fin.cons ⟨⟨N, Nat.lt_succ_self N⟩, z.1⟩ (boundedBlockEncode hr L z.2)

def prefixCoefficient : (L : ℕ) → (Fin L → ℝ) → Fin L → ℝ
  | 0, _ => Fin.elim0
  | L + 1, t => Fin.cons 1 (fun j ↦ t 0 * prefixCoefficient L (Fin.tail t) j)

namespace System

variable {ι : Type*} [Fintype ι]

noncomputable def blockMap (S : System ι) (N : ℕ) :
    (L : ℕ) → (Fin L → BoundedWord ι N) → RealSimilarity
  | 0, _ => RealSimilarity.identity
  | L + 1, x => (S.boundedWordMap N (x 0)).comp (S.blockMap N L (Fin.tail x))

theorem blockMap_encode (S : System ι) {N r : ℕ} (hr : r ≤ N)
    (L : ℕ) (w : Word ι (blockLength N r L)) :
    S.blockMap N (L + 1) (boundedBlockEncode hr L w) = S.wordMap (blockLength N r L) w := by
  induction L with
  | zero =>
    change (S.wordMap r w).comp RealSimilarity.identity = S.wordMap r w
    exact RealSimilarity.comp_identity _
  | succ L ih =>
    simp only [boundedBlockEncode, blockMap]
    change (S.wordMap N (Word.split N (blockLength N r L) w).1).comp
      (S.blockMap N (L + 1) (boundedBlockEncode hr L (Word.split N (blockLength N r L) w).2)) = _
    rw [ih]
    rw [← S.wordMap_append]
    exact congrArg (S.wordMap (blockLength N r L + N))
      (Word.append_split N (blockLength N r L) w)

theorem blockMap_ratio (S : System ι) (N L : ℕ) (x : Fin L → BoundedWord ι N) :
    (S.blockMap N L x).ratio = ∏ j, S.boundedWordRatio N (x j) := by
  induction L with
  | zero => simp [blockMap, RealSimilarity.identity]
  | succ L ih =>
    rw [Fin.prod_univ_succ]
    change S.boundedWordRatio N (x 0) * (S.blockMap N L (Fin.tail x)).ratio = _
    rw [ih]
    rfl

theorem blockMap_translation (S : System ι) (N L : ℕ) (x : Fin L → BoundedWord ι N) :
    (S.blockMap N L x).shift =
      ∑ j, prefixCoefficient L (fun k ↦ S.boundedWordRatio N (x k)) j *
        S.boundedWordTranslation N (x j) := by
  induction L with
  | zero => simp [blockMap, RealSimilarity.identity]
  | succ L ih =>
    rw [Fin.sum_univ_succ]
    change S.boundedWordRatio N (x 0) * (S.blockMap N L (Fin.tail x)).shift +
      S.boundedWordTranslation N (x 0) = _
    rw [ih, Finset.mul_sum]
    simp only [prefixCoefficient, Fin.cons_zero, Fin.cons_succ, one_mul]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    have ht : Fin.tail (fun k ↦ S.boundedWordRatio N (x k)) =
        (fun k ↦ S.boundedWordRatio N (x k.succ)) := rfl
    rw [ht]
    change S.boundedWordRatio N (x 0) *
      (prefixCoefficient L (fun k ↦ S.boundedWordRatio N (x k.succ)) j *
        S.boundedWordTranslation N (x j.succ)) = _
    ring

theorem wordTranslation_eq_block_digitSum (S : System ι) {N r : ℕ} (hr : r ≤ N)
    (L : ℕ) (w : Word ι (blockLength N r L)) :
    S.wordTranslation (blockLength N r L) w =
      EntropyEnergyGap.digitValueSum (fun _ ↦ S.boundedWordTranslation N)
        (prefixCoefficient (L + 1)
          (fun j ↦ S.boundedWordRatio N (boundedBlockEncode hr L w j)))
        (boundedBlockEncode hr L w) := by
  have h := S.blockMap_translation N (L + 1) (boundedBlockEncode hr L w)
  rw [S.blockMap_encode hr L w] at h
  exact h

theorem wordRatio_eq_block_product (S : System ι) {N r : ℕ} (hr : r ≤ N)
    (L : ℕ) (w : Word ι (blockLength N r L)) :
    S.wordRatio (blockLength N r L) w =
      ∏ j, S.boundedWordRatio N (boundedBlockEncode hr L w j) := by
  have h := S.blockMap_ratio N (L + 1) (boundedBlockEncode hr L w)
  rw [S.blockMap_encode hr L w] at h
  exact h

end System
end ExactOverlaps.SelfSimilar
