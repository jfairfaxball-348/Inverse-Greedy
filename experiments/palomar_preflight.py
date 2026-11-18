#!/usr/bin/env python3
"""Conservative local preflight for Palomar packaging.

This is NOT the official Comparator or Palomar verifier.
Usage: python experiments/palomar_preflight.py [--project-dir DIR] [--root DIR]
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path


def _has_module_header(content: str) -> bool:
    """Recognise the intended first-code-line 'module' header conservatively."""
    in_block_comment = False
    for line in content.splitlines():
        s = line.strip()
        if in_block_comment:
            if "-/" in s:
                in_block_comment = False
            continue
        if not s or s.startswith("--"):
            continue
        if s.startswith("/-"):
            if "-/" not in s[2:]:
                in_block_comment = True
            continue
        return s == "module" or s.startswith("module --")
    return False


def inspect_repository(root: Path, project_rel: str = ".") -> dict:
    root = root.resolve()
    project = (root / project_rel).resolve()
    failures: list[str] = []
    if not project.is_relative_to(root) or not project.is_dir():
        return {"status": "BLOCKED", "failures": ["Project directory is absent or outside repository"], "lean_files": 0}
    candidates = [x for x in ("LICENSE", "LICENSE.md", "LICENSE.txt", "LICENCE", "COPYING") if (root / x).is_file()]
    if not candidates:
        failures.append("Root repository licence is missing; owner must select and approve it")
    configs = [x for x in ("lakefile.toml", "lakefile.lean") if (project / x).is_file()]
    if len(configs) != 1:
        failures.append("Exactly one project Lakefile (TOML or Lean) is required")
    if not (project / "lake-manifest.json").is_file():
        failures.append("Pinned lake-manifest.json is missing from selected project")
    if not (project / "lean-toolchain").is_file() and not (root / "lean-toolchain").is_file():
        failures.append("Pinned lean-toolchain is missing")
    for name in ("Challenge.lean", "Solution.lean", "comparator.json", "formalization.yaml"):
        if not (project / name).is_file():
            failures.append(f"Missing {project_rel}/{name}")
    challenge = project / "Challenge.lean"
    if challenge.is_file():
        raw = challenge.read_bytes()
        if len(raw) > 102400 or len(raw.splitlines()) > 1000:
            failures.append("Challenge exceeds 100 KiB or 1000 physical lines")
    lean_files = []
    for path in sorted(root.rglob("*.lean")):
        if {".git", ".lake"} & set(path.relative_to(root).parts):
            continue
        if path.is_symlink():
            failures.append(f"Lean symlink forbidden: {path.relative_to(root)}")
            continue
        if not path.is_file():
            continue
        lean_files.append(path)
        content = path.read_text(encoding="utf-8")
        if not _has_module_header(content):
            failures.append(f"No modern Lean module header: {path.relative_to(root)}")
        if len(content.splitlines()) > 10000:
            failures.append(f"More than 10000 lines: {path.relative_to(root)}")
    config = project / "comparator.json"
    if config.is_file():
        try:
            obj = json.loads(config.read_text(encoding="utf-8"))
            if not obj.get("challenge_module") or not obj.get("solution_module"):
                failures.append("Comparator challenge_module and solution_module are required")
            if not obj.get("theorem_names") and not obj.get("definition_names"):
                failures.append("Comparator selects no declarations")
        except (ValueError, OSError) as exc:
            failures.append(f"Invalid Comparator JSON: {exc}")
    return {
        "status": "BLOCKED" if failures else "STATIC_PREFLIGHT_PASSED",
        "project_dir": project_rel,
        "lean_files": len(lean_files),
        "failures": failures,
        "not_verified": [
            "Official lake comparator output and permitted-axiom closure",
            "Actual lean build and complete Python/exact/census test suite",
            "Mathlib/toolchain compatibility, metadata policy and semantic review",
            "Palomar acceptance, consent and public registration",
        ],
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", default=".")
    parser.add_argument("--project-dir", default=".")
    args = parser.parse_args()
    result = inspect_repository(Path(args.root), args.project_dir)
    print(json.dumps(result, indent=2))
    return 1 if result["status"] == "BLOCKED" else 0


if __name__ == "__main__":
    raise SystemExit(main())
