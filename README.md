# The exact overlaps conjecture for self-similar measures on the real line

This repository formalizes the seventeen numbered results and Definition 3.5 of [*The exact overlaps conjecture for self-similar measures on the real line*](https://arxiv.org/abs/2610.10511) by [Samuel Kittle](https://github.com/samuel-kittle) and [Constantin Kogler](https://github.com/ckkogler), together with the required Theorem 1.4 of Michael Hochman and its necessary inputs. Informal remarks are excluded. The main theorem identifies the Hausdorff dimension of a stationary self-similar measure with `min 1 (h/|χ|)`, where `h` is the entropy rate of the actual affine random walk.

[Challenge.lean](Challenge.lean) states two main theorems and a corollary from the introduction, two entropy preliminaries, and three elementary normalization/support lemmas needed for its definitions. [Solution.lean](Solution.lean) imports their complete proofs. The five deliberate Challenge proof holes are confined to the independent statement specification. The comparator checks all eight theorem declarations, including the three elementary helpers proved in Challenge. The proved library uses only `propext`, `Classical.choice` and `Quot.sound`.

- [COVERAGE.md](COVERAGE.md): every selected source result and its Lean declaration.
- [FORMALIZATION.md](FORMALIZATION.md): definitions, proof structure and checking boundary.
- [provenance](provenance/README.md): mathematical attribution, reused code and [source corrections](provenance/SOURCE_NOTES.md).
- [formalization.yaml](formalization.yaml) and [comparator.json](comparator.json): submission metadata and exact statement comparison configuration.
- [verification/README.md](verification/README.md): recorded outcomes and the exact checked proof-source snapshot.

All selected mathematical statements have been proved and reviewed within the development. The complete default build, the audit of all 3,622 authored declarations, strict comparison of all eight Challenge claims, and replay by Lean, NanoDa and con-ron have passed. A separate isolated checkout also rebuilt all 592 proof modules and passed the same 3,622-declaration audit, with no preexisting authored proof artifacts. That relocation check covers the exact proof/configuration snapshot; final-commit recovery is a separate check. No registry acceptance or hosted CI run is claimed.

## Build and audit

The project pins **Lean v4.35.0-rc2** in [lean-toolchain](lean-toolchain) and **Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`** in its Lake files. Every transitive dependency is pinned in [lake-manifest.json](lake-manifest.json). Install [Elan](https://github.com/leanprover/elan), then run these commands from this repository's root:

```sh
lake exe cache get
lake build
lake env lean Verification.lean
```

The optional first command retrieves the cache for the pinned Mathlib sources. `lake build` compiles the entire authored library and Solution. `Verification.lean` inspects transitive axiom dependencies of every imported authored declaration and fails on any axiom outside the permitted three. This checkout contains all adapted source code; no sibling project or private filesystem path is needed.

## Reproduce local Palomar checks

The verification workflow uses the official [PalomarSubmission](https://github.com/PalomarRegistry/PalomarSubmission) policy at commit `65f0154ed776cd26c224254aa57b379137f28b0d`. It performs local checks and does not call a registry submission endpoint. A future submission should also check the then-current official policy.

For the same local checks, use Linux with Python 3.11, Ruby 3.3.12, Bundler 2.7.2, Git, and the pinned Lean toolchain. Install the policy checkout and its locked dependencies:

```sh
git clone https://github.com/PalomarRegistry/PalomarSubmission.git .lake/palomar-pipeline
git -C .lake/palomar-pipeline checkout --detach 65f0154ed776cd26c224254aa57b379137f28b0d
python3 -m venv .lake/palomar-python
.lake/palomar-python/bin/python -m pip install --require-hashes --no-deps -r .lake/palomar-pipeline/requirements.txt
gem install bundler --version 2.7.2 --no-document
export BUNDLE_GEMFILE="$PWD/.lake/palomar-pipeline/Gemfile"
export BUNDLE_PATH="$PWD/.lake/palomar-gems"
export BUNDLE_FROZEN=true
bundle install
.lake/palomar-python/bin/python scripts/validate_local_contract.py
```

The helper checks the official metadata schema, all Lean source module headers and line limits, the Challenge limits, pinned dependency checkouts, Mathlib/toolchain alignment and Licensee's detected license. It writes a receipt with the exact public-file hashes under `.lake/verification/`. The ignored `.lake` directory also holds downloaded tools and dependencies.

For strict Challenge/Solution comparison, install bubblewrap **0.12.0**. The official pinned installer verifies its release archive digest; it needs `curl`, `xz`, Meson, Ninja, a C compiler, `pkg-config` and the libcap development headers. On Ubuntu with restricted user namespaces it also installs the narrowly scoped AppArmor profile used by the official pipeline, requiring `sudo`:

```sh
export COMPARATOR_BWRAP="$(.lake/palomar-pipeline/scripts/install_bwrap.sh "$PWD/.lake/palomar-bwrap")"
python3 scripts/verify_palomar.py
```

The verifier uses the pinned Lean comparator and the bundled NanoDa and con-ron kernels. `--prepare-only` checks local prerequisites and generates the configuration without comparing proofs. The [CI workflow](.github/workflows/verify.yml) runs the build, axiom audit, local policy checks and full comparator, retaining their logs as a workflow artifact. Defining this workflow is not a claim that a remote run has passed.

## Attribution and license

The mathematical sources are Kittle–Kogler and Hochman; Constantin Kogler is the responsible maintainer. OpenAI Codex assisted with the Lean implementation and automated checking. Original mathematical proofs are attributed to their human authors. Adapted LpSelfSimilar code retains its [0BSD notice](provenance/LpSelfSimilar-LICENSE). New authored material is also licensed under [0BSD](LICENSE).
