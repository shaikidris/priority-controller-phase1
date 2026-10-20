"""Check a reviewed family-to-abstract map against exact submission inputs.

The map records a semantic review; this script checks its completeness and
freshness. It cannot decide whether a reviewer grouped or described theorems
correctly. Keep the map outside formalization.yaml's upstream schema.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path


def _file(source, relative):
    if not isinstance(relative, str) or not relative or Path(relative).is_absolute():
        raise ValueError("Coverage paths must be nonempty repository-relative paths")
    path = source / relative
    if not path.resolve().is_relative_to(source.resolve()) or not path.is_file():
        raise ValueError("Missing or out-of-tree coverage input: " + relative)
    return path


def _text(value, label):
    if not isinstance(value, str) or not value.strip():
        raise ValueError("Missing " + label)
    return value.strip()


def _names(value, label):
    if not isinstance(value, list) or not value:
        raise ValueError("Expected nonempty " + label)
    return [_text(name, label + " name") for name in value]


def validate_abstract_coverage(source, metadata, metadata_path, comparator_path, coverage_path):
    """Reject omitted selections, absent abstract phrases, or stale review inputs."""
    source = Path(source)
    ledger_file = _file(source, coverage_path)
    ledger = json.loads(ledger_file.read_text())
    if type(ledger.get("schema_version")) is not int or ledger["schema_version"] != 1:
        raise ValueError("Unsupported abstract coverage schema")
    for key, expected in [("metadata_path", metadata_path), ("comparator_path", comparator_path)]:
        if ledger.get(key) != expected:
            raise ValueError("Abstract coverage " + key + " differs from selected input")
    comparator_file = _file(source, comparator_path)
    config = json.loads(comparator_file.read_text())
    selected = _names(config.get("theorem_names"), "selected theorems")
    if len(set(selected)) != len(selected):
        raise ValueError("Duplicate Comparator theorem selection")
    module = _text(config.get("challenge_module"), "Challenge module")
    files = {
        "metadata": _file(source, metadata_path),
        "comparator": comparator_file,
        "challenge": _file(source, module.replace(".", "/") + ".lean"),
    }
    hashes = {name: hashlib.sha256(path.read_bytes()).hexdigest() for name, path in files.items()}
    if ledger.get("input_sha256") != hashes:
        raise ValueError("Stale abstract coverage review; recheck metadata, selection and Challenge")
    review = ledger.get("review", {})
    if not isinstance(review, dict) or review.get("method") != "manual-semantic-review":
        raise ValueError("Abstract coverage needs a manual semantic review")
    _text(review.get("reviewer"), "semantic reviewer")
    _text(review.get("rationale"), "semantic review rationale")
    description = " ".join(_text(metadata["project"].get("description"), "public abstract").split())
    families = ledger.get("families")
    if not isinstance(families, list) or not families:
        raise ValueError("Missing reviewed theorem families")
    ids, mapped = [], []
    for family in families:
        if not isinstance(family, dict):
            raise ValueError("Invalid theorem family record")
        identifier = _text(family.get("id"), "theorem family id")
        ids.append(identifier)
        mapped.extend(_names(family.get("theorems"), "family theorems"))
        _text(family.get("account"), "family mathematical account")
        quotes = _names(family.get("abstract_quotes"), "abstract quotes")
        for quote in quotes:
            if " ".join(quote.split()) not in description:
                raise ValueError("Abstract omits reviewed phrase for family " + identifier + ": " + quote)
    if len(ids) != len(set(ids)):
        raise ValueError("Duplicate theorem family id")
    counts = Counter(mapped)
    missing = sorted(set(selected) - set(mapped))
    extra = sorted(set(mapped) - set(selected))
    duplicates = sorted(name for name, count in counts.items() if count != 1)
    if missing or extra or duplicates:
        raise ValueError(f"Abstract family coverage differs from selection: missing={missing}, "
                         f"extra={extra}, repeated={duplicates}")
    return {
        "status": "pass", "families_checked": len(families), "theorems_checked": len(selected),
        "coverage_sha256": hashlib.sha256(ledger_file.read_bytes()).hexdigest(),
        "input_sha256": hashes,
        "scope": "Reviewed family coverage and input freshness; not automatic semantic certification",
    }


def main():
    import yaml
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--metadata", required=True)
    parser.add_argument("--comparator", required=True)
    parser.add_argument("--coverage", required=True)
    args = parser.parse_args()
    metadata = yaml.safe_load(_file(args.source, args.metadata).read_text())
    result = validate_abstract_coverage(args.source, metadata, args.metadata,
                                        args.comparator, args.coverage)
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
