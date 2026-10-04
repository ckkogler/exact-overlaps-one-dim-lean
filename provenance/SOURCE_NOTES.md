# Source conventions and proof changes

The selected target statements retain their mathematical scope, constants and quantifier order. Some auxiliary arguments require endpoint care or corrected estimates. The explanations here distinguish those issues from equivalent choices of formal proof.

## Primary paper

In the proof of Lemma 2.2, the quantile event at one half must be strict. An atom at one half makes the comparison with a non-strict event invalid. The formal proof consistently uses the strict event already present in the integrand. At predictor thresholds, finitely many atom locations can also give zero predicted probability. The proof establishes the estimate away from that finite set and removes the exceptions before integration. Neither repair changes the constant nine or Theorem 1.3's constant `30m`.

The local-variance energy of a general bounded law need not be finite. This is a semantic finiteness obligation, not a correction of the source theorem. The definition therefore uses extended nonnegative integration. Separate finite-support results justify every real-valued conversion used in the entropy-loss argument.

The standard attractor is the **nonempty** compact invariant set. The empty set also satisfies the bare invariance equation, so nonemptiness is necessary in that definition. Corollary 1.2 uses the standard meaning, and its attractor existence and uniqueness are proved.

The introduction's informal equivalence between strict dimension drop and existence of an exact overlap does not hold without accounting for dimension saturation at one. For example, take `g₀(x)=x/2`, `g₁(x)=(x+1)/2`, each with weight `1/4`, and `h_k(x)=(x+k)/4`, for `k=0,1,2,3`, each with weight `1/8`. The uniform law on `[0,1]` is stationary and has dimension one. The one-step Shannon entropy is `(5/2)log 2`, and the absolute Lyapunov exponent is `(3/2)log 2`, so their capped ratio is one. Yet `g₀ ∘ h₀ = h₀ ∘ g₀`, an exact overlap between distinct words of equal length. That informal equivalence is excluded from the targets. Theorem 1.1 instead retains its precise formula using the asymptotic random-walk entropy rate.

## Hochman input and supplementary estimates

Theorem 1.4 is preserved. Its formal proof uses these explicit corrections and conventions:

- The joint word law includes the actual probability weights; signed ratios remain in observations and absolute ratios determine metric scales.
- Entropy comparison errors depend on the difference of dyadic levels, not merely their ratio.
- The sufficient inverse theorem uses a separate exceptional-scale tolerance, chosen with explicit slack from the summand-entropy threshold.
- The iterated-convolution estimate subtracts the initial law's entropy, as required by telescoping.
- The sharp unit-interval entropy bound uses half-open `[0,1)` support. Closed `[0,1]` permits an extra boundary cell.

The corresponding implementations include `Entropy/DyadicBounds`, the iterated-convolution entropy modules, and the sufficient inverse theorem. Separately, the supplementary `Entropy/ScaleCounting` estimates correct shifted dense-scale counting by including both density-loss terms and the endpoint loss; this module is outside the final dependency closure of Theorem 1.4. Incorrect auxiliary formulations are not imported as axioms or used as hypotheses of Theorem 1.4.

## Equivalent formal proof organizations

The finite Poisson cut law retains precisely the gap indicators observable by a finite real law. Its exact refinement, survival and conditional-law identities replace construction of an infinite point process while preserving every required observable. The finite translated-grid integral argument similarly replaces an infinite logarithmic-grid averaging step in Proposition 3.12.

Lemma 3.7 is supplied by a complete Stein argument with one explicit positive universal constant. The informal optimal-constant remark is not a target. Lemma 3.8 uses an explicit finite core and a common summable entropy envelope to control the tails of unbounded laws, instead of a compactness/subsequence argument. The large-variance entropy step may select a finite subset with controlled total variance; actual independence identifies the remaining sum as a convolution factor.

The W functional uses a canonical measurable space of variable-length factor families. Its equivalence with arbitrary source mixing spaces and its null-set repair are proved. The variance bound averages conditional windows over continuous interval origins, an exact equivalent of averaging translated grids.

Exact dimensionality and its standard Hausdorff-dimension identification are proved internally. References to such inputs in the papers are not substituted for Lean proofs. The stopped-block construction uses genuine bounded Mathlib stopping times and exact conditional kernel laws. Almost-sure ordering is repaired by bounded stopping-time maxima only to prove the joint law; almost-sure equality transfers that law back to the original block family.
