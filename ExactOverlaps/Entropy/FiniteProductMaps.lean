module

public import ExactOverlaps.Entropy.FiniteProductLaw
public import ExactOverlaps.Probability.IndependentExpectations

/-!
# Coordinate maps and support of finite product laws

Coordinatewise statistics of a genuine independent tuple have exactly the
product of the marginal push-forward laws. The support criterion likewise
requires precisely positive mass in every coordinate.
-/

@[expose] public section

open scoped Classical

namespace ExactOverlaps.Entropy

def tupleMap {α β : Type*} : (n : ℕ) → (Fin n → α → β) → FiniteTuple α n → FiniteTuple β n
  | 0, _, _ => PUnit.unit
  | n + 1, f, w => (f 0 w.1, tupleMap n (fun i ↦ f i.succ) w.2)

lemma tupleCoordinate_tupleMap {α β : Type*} (n : ℕ) (f : Fin n → α → β)
    (w : FiniteTuple α n) (i : Fin n) :
    tupleCoordinate n (tupleMap n f w) i = f i (tupleCoordinate n w i) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · rfl
    · exact ih (fun j ↦ f j.succ) w.2 j

lemma tupleLaw_mem_support_iff {α : Type*} (n : ℕ) (p : Fin n → PMF α)
    (w : FiniteTuple α n) :
    w ∈ (tupleLaw n p).support ↔ ∀ i, tupleCoordinate n w i ∈ (p i).support := by
  induction n with
  | zero =>
    cases w
    constructor
    · intro _ i
      exact Fin.elim0 i
    · intro _
      exact (PMF.mem_support_pure_iff _ _).mpr rfl
  | succ n ih =>
    change w ∈ (independentPair (p 0) (tupleLaw n (fun i ↦ p i.succ))).support ↔ _
    rw [independentPair_support]
    change (w.1 ∈ (p 0).support ∧ w.2 ∈ (tupleLaw n (fun i ↦ p i.succ)).support) ↔ _
    rw [ih]
    constructor
    · intro h i
      exact Fin.cases h.1 h.2 i
    · intro h
      exact ⟨h 0, fun i ↦ h i.succ⟩

theorem tupleLaw_map {α β : Type*} (n : ℕ) (p : Fin n → PMF α) (f : Fin n → α → β) :
    (tupleLaw n p).map (tupleMap n f) = tupleLaw n (fun i ↦ (p i).map (f i)) := by
  induction n with
  | zero => exact PMF.pure_map _ _
  | succ n ih =>
    change (independentPair (p 0) (tupleLaw n (fun i ↦ p i.succ))).map
        (fun w ↦ (f 0 w.1, tupleMap n (fun i ↦ f i.succ) w.2)) =
      independentPair ((p 0).map (f 0)) (tupleLaw n (fun i ↦ (p i.succ).map (f i.succ)))
    rw [FiniteProbability.independentPair_map_pair, ih]

end ExactOverlaps.Entropy
