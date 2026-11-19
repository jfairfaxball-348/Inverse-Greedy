#!/usr/bin/env python3
"""Validate formalization.yaml with the pinned upstream v0.4 JSON Schema.

This is a local metadata test, not Palomar verification or registration.
Schema source: https://github.com/mathlib-initiative/formalization.yaml
commit 99c678e569c7c4c0772db297c5ddd5e4c9b6322e.
"""
from pathlib import Path
import json
import sys

import jsonschema
import yaml

ROOT = Path(__file__).resolve().parents[1]
SCHEMA = ROOT / "schemas" / "formalization-v0.4.schema.json"


def main() -> int:
    try:
        document = yaml.safe_load((ROOT / "formalization.yaml").read_text(encoding="utf-8"))
        schema = json.loads(SCHEMA.read_text(encoding="utf-8"))
        jsonschema.Draft7Validator.check_schema(schema)
        issues = sorted(
            jsonschema.Draft7Validator(schema).iter_errors(document),
            key=lambda e: tuple(str(p) for p in e.path),
        )
        if issues:
            for error in issues:
                location = "$" + "".join(f"[{p!r}]" for p in error.path)
                print(f"{location}: {error.message}", file=sys.stderr)
            return 1
        if document.get("version") != "v0.4":
            print("Expected formalization.yaml version v0.4", file=sys.stderr)
            return 1
        if document["project"]["license"] != "Apache-2.0":
            print("Licence does not match owner-approved Apache-2.0", file=sys.stderr)
            return 1
        print("formalization.yaml: upstream v0.4 JSON Schema PASS (locally pinned)")
        return 0
    except (OSError, ValueError, yaml.YAMLError, jsonschema.exceptions.SchemaError, TypeError, KeyError) as exc:
        print(f"Metadata validation could not complete: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
