# Verification evidence

The complete default build passed for all 592 authored proof modules and
Solution. The environment-based axiom audit passed for 3,622 declarations,
including definitions, instances and generated declarations. Only `propext`,
`Classical.choice` and `Quot.sound` occur.

Strict Comparator accepted all eight Challenge declarations. Its actual
exported Solution was accepted by con-ron, NanoDa and Lean's default kernel.
The five deliberate Challenge holes are confined to the independent statement
specification; the proved Solution does not import Challenge. All eight
theorem claims are compared, including the three elementary lemmas already
proved in Challenge. There are no definition holes.

The verification records identify exact source bytes, pinned tools, process
exits and output hashes. They summarize checks; they are not proof certificates.

- [proof-source-snapshot.json](proof-source-snapshot.json) binds every authored
  library source, aggregate, Solution, Verification and build configuration.
- [library-checks.json](library-checks.json) records the complete default build
  and the full authored axiom audit.
- [comparison-source-snapshot.json](comparison-source-snapshot.json) and
  [comparison-checks.json](comparison-checks.json) record the strict comparison
  and the three actual kernel checks.
- [semantic-review.json](semantic-review.json) describes the cross-agent
  mathematical review and its exact scope. This is not independent human review.
- [policy-review.json](policy-review.json) identifies the current official
  submission policy and immutable tool profile checked for this development.
- [relocation-checks.json](relocation-checks.json) records the fresh isolated
  proof build, dependency checks, phase timestamps and log digests.
- [repository-checks.json](repository-checks.json) records local metadata,
  license, source packaging and dependency-policy checks.
- [challenge-provenance.json](challenge-provenance.json) records the source
  provenance of the complete transitive import closure and the separate
  compilation using canonical dependencies.

The relocated proof/configuration snapshot also passed a fresh default build
(4,434 jobs) and the same 3,622-declaration axiom audit. Its separate Git
checkout began with zero authored `.olean` files and produced 594: the 592
library modules, the aggregate and Solution. The nine pinned dependency
checkouts were local and unchanged; third-party caches were reused. Runtime
search paths stayed within that checkout and the pinned compiler library.
This verifies the exact 598-file proof/configuration snapshot. Final public
Git history and full-history bundle readback are separate post-commit checks.
The [README](../README.md) documents reproduction commands, prerequisites and
the pinned CI workflow. No remote CI run or Palomar review, registration or
acceptance is claimed. Raw work logs and recovery artifacts are retained
outside the submitted repository.
