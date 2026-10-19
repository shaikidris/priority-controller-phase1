"""Catch ambiguous MSC scalars before different YAML parsers disagree.

This is a narrow portability lint, not a replacement for Palomar's current
browser/server validator, metadata schema, taxonomy or semantic checks.
"""
import argparse
from pathlib import Path
import re

import yaml


def validate_metadata_portability(text):
    """Require scientific-notation-shaped MSC codes to be quoted strings."""
    document = yaml.compose(text, Loader=yaml.SafeLoader)

    def field(node, name):
        if not isinstance(node, yaml.MappingNode):
            return None
        values = [value for key, value in node.value
                  if isinstance(key, yaml.ScalarNode) and key.value.lower() == name]
        if len(values) > 1:
            raise ValueError("Duplicate metadata field: " + name)
        return values[0] if values else None

    codes = field(field(document, "classification"), "msc2020")
    if not isinstance(codes, yaml.SequenceNode):
        return 0  # Shape/cardinality checks belong to the exact upstream validator.
    for code in codes.value:
        if (isinstance(code, yaml.ScalarNode) and code.style is None
                and re.fullmatch(r"[0-9]{2}[Ee][0-9]{2}", code.value)):
            raise ValueError(
                f"Quote MSC2020 code {code.value!r} as a YAML string; "
                "the browser's YAML 1.2 parser reads its plain form as a number"
            )
    return len(codes.value)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("metadata", nargs="+", type=Path)
    args = parser.parse_args()
    for path in args.metadata:
        count = validate_metadata_portability(path.read_text())
        print(f"PASS: {path}: {count} MSC scalars checked; exact intake validation is separate")


if __name__ == "__main__":
    main()
