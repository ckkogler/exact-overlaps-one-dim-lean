module

public import ExactOverlaps.Entropy.FiniteProductMaps
public import ExactOverlaps.Probability.RectangularConditioning
public import ExactOverlaps.Probability.ConditionalRefinement

/-!
# Actual product laws after rectangular conditioning

The fiber containing a positive tuple is the product of its coordinate
fibers. Its normalized conditional probability law is exactly the product
of the normalized coordinate laws, with no finiteness assumption needed.
-/

@[expose] public section

open scoped Classical
open ExactOverlaps.Entropy

namespace ExactOverlaps.FiniteProbability

lemma independentPair_mem_support {α β : Type*} (p : PMF α) (q : PMF β) (w : α × β) :
    w ∈ (independentPair p q).support ↔ w.1 ∈ p.support ∧ w.2 ∈ q.support := by
  rw [independentPair_support]
  rfl

lemma conditionalAt_independentPair {α β γ δ : Type*} (p : PMF α) (q : PMF β)
    (f : α → γ) (g : β → δ) (w : (independentPair p q).support) :
    conditionalAt (independentPair p q) (fun z ↦ (f z.1, g z.2)) w =
      independentPair
        (conditionalAt p f ⟨w.val.1, ((independentPair_mem_support p q w.val).mp w.property).1⟩)
        (conditionalAt q g ⟨w.val.2, ((independentPair_mem_support p q w.val).mp w.property).2⟩) := by
  exact conditionalPMF_independentPair p q f g
    ⟨f w.val.1, (PMF.mem_support_map_iff f p _).mpr
      ⟨w.val.1, ((independentPair_mem_support p q w.val).mp w.property).1, rfl⟩⟩
    ⟨g w.val.2, (PMF.mem_support_map_iff g q _).mpr
      ⟨w.val.2, ((independentPair_mem_support p q w.val).mp w.property).2, rfl⟩⟩

noncomputable def tupleSupportCoordinate {α : Type*} (n : ℕ) (p : Fin n → PMF α)
    (w : (tupleLaw n p).support) (i : Fin n) : (p i).support :=
  ⟨tupleCoordinate n w.val i, (tupleLaw_mem_support_iff n p w.val).mp w.property i⟩

theorem conditionalAt_tupleLaw {α β : Type*} (n : ℕ) (p : Fin n → PMF α)
    (f : Fin n → α → β) (w : (tupleLaw n p).support) :
    conditionalAt (tupleLaw n p) (tupleMap n f) w =
      tupleLaw n (fun i ↦ conditionalAt (p i) (f i) (tupleSupportCoordinate n p w i)) := by
  induction n with
  | zero =>
    let : Fintype (FiniteTuple α 0) := inferInstanceAs (Fintype PUnit)
    let : Unique (FiniteTuple α 0) := inferInstanceAs (Unique PUnit)
    ext a
    cases a
    have h := ((conditionalAt (tupleLaw 0 p) (tupleMap 0 f) w).tsum_coe).trans
      (tupleLaw 0 (fun i ↦ conditionalAt (p i) (f i) (tupleSupportCoordinate 0 p w i))).tsum_coe.symm
    have hd : (default : FiniteTuple α 0) = PUnit.unit := Subsingleton.elim _ _
    simpa only [tsum_fintype, Fintype.sum_unique, hd] using h
  | succ n ih =>
    let pt := tupleLaw n (fun i ↦ p i.succ)
    let ft := tupleMap n (fun i ↦ f i.succ)
    have hw : w.val.1 ∈ (p 0).support ∧ w.val.2 ∈ pt.support :=
      (independentPair_mem_support (p 0) pt w.val).mp w.property
    let wt : pt.support := ⟨w.val.2, hw.2⟩
    have h := conditionalAt_independentPair (p 0) pt (f 0) ft w
    change conditionalAt (independentPair (p 0) pt) (fun z ↦ (f 0 z.1, ft z.2)) w = _
    rw [h]
    change independentPair (conditionalAt (p 0) (f 0) _)
      (conditionalAt pt ft wt) = _
    rw [ih (fun i ↦ p i.succ) (fun i ↦ f i.succ) wt]
    rfl

end ExactOverlaps.FiniteProbability
