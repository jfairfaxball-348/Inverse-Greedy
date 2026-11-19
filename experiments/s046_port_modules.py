#!/usr/bin/env python3
"""S046 mechanical FIRST PASS for Lean module migration.

Do not mistake this transformation for a successful Lean/Palomar port.
It follows Lean's official initial migration recipe. The generated result
MUST compile and pass Comparator before it is eligible for submission.

Use --apply on a disposable branch/worktree; default is read-only inspection.
"""
from __future__ import annotations

import argparse
import json
import re
from pathlib import Path


def port_source(source: str) -> str:
    """Mechanical module + public API exposure; idempotent."""
    if re.search(r"^module(?:\s|$)", source, flags=re.MULTILINE):
        return source
    lines = source.splitlines(keepends=True)
    last_import = -1
    for i, line in enumerate(lines):
        if re.match(r"^import\s+", line):
            lines[i] = "public " + line
            last_import = i
        elif re.match(r"^public import\s+", line):
            last_import = i
    # Lean's public section covers declarations AND their def bodies.
    # Its implicit closure is at EOF, preserving existing named namespaces.
    lines.insert(last_import + 1, "\n@[expose] public section\n\n")
    return "module\n" + "".join(lines)


def plan(root: Path) -> list[dict[str, str | int]]:
    result = []
    for path in sorted(root.rglob("*.lean")):
        if {".git", ".lake"} & set(path.relative_to(root).parts):
            continue
        if path.is_symlink():
            raise RuntimeError(f"Refuse to rewrite symlink: {path}")
        source = path.read_text(encoding="utf-8")
        changed = port_source(source)
        if changed != source:
            result.append({"path": str(path.relative_to(root)), "old_bytes": len(source.encode()), "new_bytes": len(changed.encode())})
    return result


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", type=Path, default=Path("."))
    ap.add_argument("--apply", action="store_true")
    args = ap.parse_args()
    root = args.root.resolve()
    entries = plan(root)
    if args.apply:
        for item in entries:
            path = root / str(item["path"])
            path.write_text(port_source(path.read_text(encoding="utf-8")), encoding="utf-8")
    print(json.dumps({"mode": "apply" if args.apply else "dry-run", "changed": len(entries), "files": entries}, indent=2))


if __name__ == "__main__":
    main()
