# Formalization guide

This Lean development formalizes the selected results of Samuel Kittle and Constantin Kogler's *The exact overlaps conjecture for self-similar measures on the real line*, together with the required Theorem 1.4 of Michael Hochman. [COVERAGE.md](COVERAGE.md) gives the source-to-declaration map. [provenance](provenance/README.md) distinguishes the mathematical sources, reused code and automated formalization work.

## Research context and the conjecture being formalized

Theorem 1.1 matches the general entropy-rate formulation in [Varjú, Conjecture 3](https://arxiv.org/html/2509.22042v2#S1): `dim ν = min(1, h_RW/abs χ)`, where `h_RW = lim H(μ⁎ⁿ)/n` counts actual composed similarities. Without exact overlaps, `h_RW = H(p)`, giving the usual similarity-entropy formula; Moran weights then give the attractor conclusion in Corollary 1.2. The entropy-rate statement also addresses systems with exact overlaps. The cap at one matters: an exact overlap need not force strict dimension drop when dimension is already one. The precise formula is the target; the informal converse is discussed with a counterexample in [SOURCE_NOTES.md](provenance/SOURCE_NOTES.md).

[Hochman (2014)](https://annals.math.princeton.edu/2014/180-2/p07) established the dimension formula under exponential separation and, in particular, the no-exact-overlap case when all similarity coefficients are algebraic. [Rapaport (2022)](https://smf.emath.fr/publications/preuve-de-la-conjecture-de-chevauchements-exacts-pour-des-systemes-contractions) established the no-exact-overlap formula for algebraic contraction ratios with arbitrary real translations. These are earlier cases of the problem. The Kittle–Kogler statement formalized here permits arbitrary real translations and nonzero signed, unequal contraction ratios, with no algebraicity or separation hypothesis, and retains the actual entropy rate when exact overlaps occur.

[Feng and Hu (2009)](https://arxiv.org/abs/1002.2036) proved exact dimensionality without a separation assumption in a broader setting. The needed finite real self-similar case and its identification with standard lower Hausdorff dimension are proved inside this development. The proof of the primary dimension formula also uses the internally proved full Hochman Theorem 1.4 and the primary paper's entropy-loss inequality. The additional historical citations explain the relationship to the standard conjecture; they add no formalization targets or assumed theorems. Full bibliographic details are in [BIBLIOGRAPHY.md](provenance/BIBLIOGRAPHY.md).

## Public statements and proof library

[Challenge.lean](Challenge.lean) presents two main theorems and a corollary from the introduction, plus necessary entropy-subadditivity and entropy-rate limit statements, and three elementary normalization/support lemmas used in the definitions. All eight theorem declarations are included in the comparison. Its definitions are independent of the proved development. The deliberate challenge holes specify the claims to be compared with the matching proved declarations in `Solution.lean`; supporting results belong under `ExactOverlaps/`.

The measure-dimension theorem uses standard lower Hausdorff dimension. Exact dimensionality is proved internally and identifies the source's almost-everywhere dimension with this standard quantity. The attractor corollary uses the ordinary nonempty compact invariant set. The entropy-loss theorem uses Mathlib's `iIndepFun` on an arbitrary probability space, actual finite marginal laws, and the actual sum pushforward law.

All affine multipliers retain their signs. Metric scales use absolute multipliers. The finite alphabet permits zero probability weights; proofs work on genuine positive support when conditioning. Coincident maps are identified by their actual affine compositions, so the entropy rate does not count distinct words as distinct maps without justification.

## Definitions with explicit finiteness

`Entropy.finiteEntropy` is Shannon entropy with natural logarithms. The physical mesh entropy is the translation average of the entropy of `floor((X+t)/r)`. `ScaleEntropy/` handles bounded laws. `GaussianScaleEntropy/` supplies the actual countable-cell entropy, proves finite-second-moment summability and integration, and proves agreement with the bounded definition.

`VarianceEnergy/` defines the local unnormalized conditional variance as the infimum of the actual quadratic error integral over interval centers. It proves equality with the normalized conditional variance multiplied by interval mass, including null intervals. The local profile has factor `4/r³`, and full energy integrates that profile against `dr/r`. Extended nonnegative values retain possible divergence. Finite-support energy finiteness justifies the ordinary real-valued formulas used in the entropy-loss inequality.

`ConvolutionDisintegration/` uses a measurable space of finite families of genuine probability laws, with variable positive factor count. Its functional W is the actual infimum of integrated exponential variance cost. The canonical representation is proved equivalent to arbitrary measurable mixing spaces. Replacing inadmissible values on a null set gives literal all-index admissibility without changing the mixture or cost.

## Proof organization

The Section 2 development starts with actual finite PMFs, conditional laws and moment identities. The finite Poisson cut process reveals genuine information about independent summands. Its exact reveal-rate integral, conditional-entropy estimate and dispersion-energy identity yield the constant `30m` in Theorem 1.3. The finite model is then connected to standard random variables and independence by exact law identities.

The Hochman development proves the entropy and self-similar dimension input before the primary main theorem. The proof supplies the needed inverse-entropy consequence with explicit parameter slack, component estimates, quantitative Gaussian approximation, the genuine exact-dimensionality chain, and the signed joint-law asymptotic. Physical scale and logarithm-base comparisons then give primary Lemma 3.2.

The Section 3 proof uses the digit-count entropy estimate and Theorem 1.3 to obtain truncated variance energy. The convolution-disintegration functional connects this energy to almost maximal entropy increments, using the complete Gaussian approximation and continuity inputs. Small W forces full dimension. Genuine bounded stopping rules combine uniform energy improvements across scales, and the final contradiction yields the dimension formula. The attractor corollary then uses Moran probabilities, the entropy identity under absence of exact overlaps, and actual cylinder covers.

Several formal arguments use equivalent proof organizations: finite observable Poisson cuts; finite translated-grid averaging; a finite-core and entropy-tail continuity proof; an explicit Stein argument; a finite subset with controlled variance; and continuous-origin averaging of conditional windows. These choices are explained in [SOURCE_NOTES.md](provenance/SOURCE_NOTES.md).

## Attribution and checking boundary

The primary mathematical results and paper arguments are attributed to Samuel Kittle and Constantin Kogler. Hochman's theorem and its entropy framework are attributed to Michael Hochman. Constantin Kogler is the responsible maintainer. OpenAI Codex supplied automated Lean construction, adaptation, compilation and cross-agent review assistance. Automated review is distinct from independent human mathematical review; no human review or registry approval is asserted here.

The repository pins Lean through `lean-toolchain` and dependencies through `lakefile.toml` and `lake-manifest.json`. All adapted authored code is included locally; the development needs no sibling source project or private filesystem location. New authored material is licensed under [0BSD](LICENSE), with the retained reused-code notice in [provenance/LpSelfSimilar-LICENSE](provenance/LpSelfSimilar-LICENSE).

All selected statements, including the full joint stopped-block embedding in Lemma 3.11, have compilation, axiom and semantic-review records. The complete default build and full authored-declaration axiom audit have passed. Strict comparison of all eight Challenge claims and replay by Lean, NanoDa and con-ron have also passed. A separate isolated Git checkout freshly rebuilt the 592 proof modules, producing 594 authored `.olean` files, and passed the same 3,622-declaration axiom audit. This relocation check binds the 598-file proof/configuration snapshot and its nine pinned dependencies; final public-commit and recovery-bundle checks are separate. [verification/README.md](verification/README.md) records the outcomes and exact checked proof-source snapshot; no hosted CI run or registry acceptance is claimed. The intended allowed axiom set for proved declarations is `propext`, `Classical.choice` and `Quot.sound`.
