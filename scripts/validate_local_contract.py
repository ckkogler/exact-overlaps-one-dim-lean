#!/usr/bin/env python3
"""Check local metadata, sources, pins and license with official Palomar APIs.

This does not request registry acceptance or run the proof comparator. See
README.md for installation and verify_palomar.py for proof comparison.
"""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys


PIPELINE_COMMIT = "65f0154ed776cd26c224254aa57b379137f28b0d"
ROOT = Path(__file__).resolve().parents[1]


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def command(arguments: list[str], **kwargs) -> str:
    return subprocess.check_output(arguments, text=True, **kwargs).strip()


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def snapshot() -> dict[str, str]:
    result = {}
    for directory, directories, files in os.walk(ROOT, followlinks=False):
        directories[:] = sorted(d for d in directories if d not in {".git", ".lake"})
        for name in directories + sorted(files):
            path = Path(directory) / name
            require(not path.is_symlink(), f"Public package contains a symlink: {path}")
        for name in sorted(files):
            path = Path(directory) / name
            if path.is_file():
                result[path.relative_to(ROOT).as_posix()] = sha256(path)
    return result


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--pipeline", type=Path, default=ROOT / ".lake/palomar-pipeline",
                        help="Checkout of the pinned official PalomarSubmission repository")
    parser.add_argument("--bundle", default="bundle", help="Bundler executable on PATH, or its path")
    args = parser.parse_args()
    pipeline = args.pipeline.resolve()
    require(command(["git", "-C", str(pipeline), "rev-parse", "HEAD"]) == PIPELINE_COMMIT,
            "The official policy checkout does not match PIPELINE_COMMIT.")
    subprocess.run(["git", "-C", str(pipeline), "diff", "--exit-code", "HEAD"], check=True)
    sys.dont_write_bytecode = True
    sys.path.insert(0, str(pipeline))
    from scripts import source_requirements as sources
    from scripts import submission_contract as contract
    from scripts import verify_submission as official

    stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S%fZ")
    before = snapshot()
    results = {}
    errors = []

    def step(name, action):
        try:
            results[name] = action()
            print(f"PASS {name}", flush=True)
        except Exception as error:
            if hasattr(error, "issues"):
                detail = [issue.diagnostic(name) for issue in error.issues]
            elif hasattr(error, "diagnostic"):
                detail = error.diagnostic(name)
            else:
                detail = {"type": type(error).__name__, "message": str(error)}
            errors.append({"step": name, "detail": detail})
            print(f"FAIL {name}: {detail}", flush=True)

    def source_check():
        information, issues = sources.inspect_lean_sources(ROOT)
        require(not issues, json.dumps([issue.diagnostic("source_requirements") for issue in issues]))
        return information

    def dependency_check():
        packages = official.manifest_packages(ROOT)
        records = official.recorded_project_dependencies(ROOT, ROOT, packages)
        heads = {}
        for package in packages:
            require(not package["url"].startswith("path:"), "Local path dependencies are not permitted.")
            checkout = ROOT / ".lake/packages" / package["name"]
            head = command(["git", "-C", str(checkout), "rev-parse", "HEAD"])
            require(head == package["revision"], f"Dependency checkout differs: {package['name']}")
            subprocess.run(["git", "-C", str(checkout), "diff", "--exit-code", "HEAD"], check=True)
            heads[package["name"]] = head
        toolchain = (ROOT / "lean-toolchain").read_text().strip()
        alignment = official.check_mathlib_toolchain(
            ROOT, packages, checkout=ROOT, project_toolchain=toolchain,
            project_toolchain_path="lean-toolchain")
        canonical = official.manifest_packages(ROOT / ".lake/packages/mathlib")
        trusted = official.trusted_package_url_map(packages, canonical)
        return {"packages": records, "checkout_heads": heads, "mathlib_toolchain": alignment,
                "mathlib_manifest_sha256": sha256(ROOT / ".lake/packages/mathlib/lake-manifest.json"),
                "mathlib_manifest_closure_urls": json.loads(trusted)}

    def license_check():
        bundle = shutil.which(args.bundle)
        require(bundle is not None, "Bundler is missing; install the official locked Ruby dependencies.")
        environment = os.environ.copy()
        environment["BUNDLE_GEMFILE"] = str(pipeline / "Gemfile")
        environment["BUNDLE_FROZEN"] = "true"
        version = command([bundle, "exec", "ruby", "-e",
                           'require "licensee"; puts Gem.loaded_specs["licensee"].version'],
                          cwd=pipeline, env=environment)
        require(version == "10.0.0", f"Unexpected Licensee version: {version}")
        license_file = official.repository_license_file(ROOT)
        detected = official.detect_spdx_identifier(license_file, Path(bundle))
        declared = results["metadata"]["project"]["license"].strip()
        require(detected == declared, f"Detected license {detected} differs from declared {declared}.")
        return {"licensee_version": version, "detected_spdx": detected,
                "declared_spdx": declared, "file": license_file.name,
                "sha256": sha256(license_file)}

    def challenge_limits():
        path = ROOT / "Challenge.lean"
        size = path.stat().st_size
        lines = sources.physical_lines(path.read_text())
        require(size <= official.MAX_CHALLENGE_BYTES, "Challenge exceeds the official byte limit.")
        require(lines <= official.MAX_CHALLENGE_LINES, "Challenge exceeds the official line limit.")
        return {"bytes": size, "lines": lines}

    step("metadata", lambda: contract.load_formalization_metadata(ROOT / "formalization.yaml"))
    if "metadata" in results:
        step("provenance", lambda: contract.normalized_provenance(results["metadata"]))
    step("source_requirements", source_check)
    step("comparator_config", lambda: official.load_comparator_config(ROOT / "comparator.json"))
    step("toolchain", lambda: official.supported_toolchain((ROOT / "lean-toolchain").read_text().strip()))
    step("dependencies", dependency_check)
    step("license", license_check)
    step("challenge_limits", challenge_limits)
    after = snapshot()
    if before != after:
        errors.append({"step": "source_snapshot", "detail": "Public files changed during validation; rerun."})
    policy_files = ["scripts/submission_contract.py", "scripts/source_requirements.py",
                    "scripts/verify_submission.py", "scripts/detect_license.rb", "toolchains.json",
                    "allowed-challenge-repositories.json", "Gemfile", "Gemfile.lock", "requirements.txt"]
    receipt = {
        "status": "pass" if not errors else "fail", "created_utc": stamp,
        "scope": "Local official policy checks; separate proof comparison and registry review are required.",
        "pipeline_commit": PIPELINE_COMMIT,
        "policy_hashes": {name: sha256(pipeline / name) for name in policy_files},
        "source_hashes_before": before, "source_hashes_after": after,
        "sources_unchanged": before == after, "results": results, "errors": errors,
    }
    output = ROOT / ".lake/verification" / f"local-contract-{stamp}.json"
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(receipt, indent=2) + "\n")
    print(f"{receipt['status'].upper()} {output.relative_to(ROOT)}", flush=True)
    return 1 if errors else 0


if __name__ == "__main__":
    raise SystemExit(main())
