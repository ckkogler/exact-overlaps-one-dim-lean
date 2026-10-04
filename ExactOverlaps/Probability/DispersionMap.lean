module

public import ExactOverlaps.Probability.Dispersion
public import ExactOverlaps.Probability.IndexedQuantile

/-!
# Exact transport of finite dispersion through a statistic

Both independent samples are pushed forward by the same statistic. The
resulting expected absolute distance is therefore exactly the dispersion
of the composed statistic on the original law.
-/

@[expose] public section

open ExactOverlaps.FiniteProbability

namespace ExactOverlaps.FiniteLaw

lemma dispersion_map {α β : Type*} (p : PMF α) (hp : p.support.Finite)
    (f : α → β) (g : β → ℝ) :
    dispersion (p.map f) (by simpa using hp.image f) g =
      dispersion p hp (fun a ↦ g (f a)) := by
  change expectation (p.map f) (by simpa using hp.image f)
      (fun a ↦ expectation (p.map f) (by simpa using hp.image f) (fun b ↦ |g a - g b|)) =
    expectation p hp (fun a ↦ expectation p hp (fun b ↦ |g (f a) - g (f b)|))
  rw [expectation_map p hp f]
  apply congrArg (expectation p hp)
  funext a
  exact expectation_map p hp f (fun b ↦ |g (f a) - g b|)

end ExactOverlaps.FiniteLaw
