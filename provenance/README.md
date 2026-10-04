# Attribution and code provenance

Samuel Kittle and Constantin Kogler are the authors of the primary paper and its mathematical results. Michael Hochman is the author of the required external theorem and entropy framework. The exact references are in [BIBLIOGRAPHY.md](BIBLIOGRAPHY.md). Constantin Kogler is the responsible maintainer and copyright holder of the authored repository material.

The Lean implementation was developed with OpenAI Codex automation, including parallel proof development, adaptation of existing code, compilation and cross-agent semantic review. This records assistance in constructing and checking the formalization. It does not attribute the original paper proofs to an AI model or represent automated review as human peer review.

Some elementary entropy, finite probability and self-similar foundations were adapted from Constantin Kogler's **LpSelfSimilar** formalization (2026), licensed under the BSD Zero Clause License. [REUSE.json](REUSE.json) lists the upstream module names and local destinations. Adaptations include namespace and import changes, the current Lean module system, tactic/API adjustments, and specialization of Euclidean similarities to signed real affine similarities. The local adapted proofs are checked as part of this development.

The upstream notice is retained in [LpSelfSimilar-LICENSE](LpSelfSimilar-LICENSE), and relevant source headers identify the adaptation. The authored code is copied into this repository; building requires no checkout of LpSelfSimilar. Lean and Mathlib remain separately licensed upstream dependencies, pinned by the repository's toolchain and Lake manifest. Their own distribution notices govern those dependencies.

New code and documentation use the [repository 0BSD license](../LICENSE). [SOURCE_NOTES.md](SOURCE_NOTES.md) explains corrections to auxiliary arguments and equivalent formal proof choices. Mathematical source attribution and software provenance are separate: a cited theorem is proved through the stated library dependencies, and a software license is not a claim of mathematical authorship.
