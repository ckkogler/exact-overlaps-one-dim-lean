module

public import ExactOverlaps.Entropy.FiniteProductMaps
public import ExactOverlaps.Entropy.IndependentRegrouping

/-!
# Independence of one coordinate and the sum of the others

For the actual finite product law, each real coordinate statistic is
independent of the sum of all remaining coordinate statistics. The second
marginal is the actual push-forward by total sum minus the selected input.
-/

@[expose] public section

namespace ExactOverlaps.Entropy

def tupleSumExcept {α : Type*} (x : α → ℝ) (n : ℕ) (i : Fin n) (w : FiniteTuple α n) : ℝ :=
  tupleSum x n w - x (tupleCoordinate n w i)

lemma exists_independent_tupleSumExcept {α : Type*} (x : α → ℝ) (n : ℕ)
    (p : Fin n → PMF α) (i : Fin n) :
    ∃ q : PMF ℝ, (tupleLaw n p).map
      (fun w ↦ (x (tupleCoordinate n w i), tupleSumExcept x n i w)) =
        independentPair ((p i).map x) q := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · refine ⟨(tupleLaw n (fun j ↦ p j.succ)).map (tupleSum x n), ?_⟩
      change (independentPair (p 0) (tupleLaw n (fun j ↦ p j.succ))).map
        (fun w ↦ (x w.1, x w.1 + tupleSum x n w.2 - x w.1)) = _
      have he : (fun w : α × FiniteTuple α n ↦ (x w.1, x w.1 + tupleSum x n w.2 - x w.1)) =
          (fun w ↦ (x w.1, tupleSum x n w.2)) := by
        funext w
        congr 1
        ring
      rw [he, FiniteProbability.independentPair_map_pair]
    · obtain ⟨q, hq⟩ := ih (fun j ↦ p j.succ) j
      refine ⟨(independentPair (p 0) q).map (fun z ↦ x z.1 + z.2), ?_⟩
      have hr := independentPair_regroup (p 0) (tupleLaw n (fun j ↦ p j.succ))
        (fun w ↦ x (tupleCoordinate n w j)) (tupleSumExcept x n j) ((p j.succ).map x) q hq
      rw [← independentPair_map_right, ← hr, PMF.map_comp]
      apply congrArg (PMF.map · (tupleLaw (n + 1) p))
      funext w
      change (x (tupleCoordinate n w.2 j), x w.1 + tupleSum x n w.2 - x (tupleCoordinate n w.2 j)) =
        (x (tupleCoordinate n w.2 j), x w.1 + (tupleSum x n w.2 - x (tupleCoordinate n w.2 j)))
      congr 1
      ring

theorem tupleLaw_coordinate_sumExcept {α : Type*} (x : α → ℝ) (n : ℕ)
    (p : Fin n → PMF α) (i : Fin n) :
    (tupleLaw n p).map (fun w ↦ (x (tupleCoordinate n w i), tupleSumExcept x n i w)) =
      independentPair ((p i).map x) ((tupleLaw n p).map (tupleSumExcept x n i)) := by
  obtain ⟨q, hq⟩ := exists_independent_tupleSumExcept x n p i
  have he := congrArg (fun r : PMF (ℝ × ℝ) ↦ r.map Prod.snd) hq
  rw [PMF.map_comp, independentPair_map_snd] at he
  change (tupleLaw n p).map (tupleSumExcept x n i) = q at he
  rw [he]
  exact hq

end ExactOverlaps.Entropy
