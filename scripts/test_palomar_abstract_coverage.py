"""Regression cases for omitted result families and stale abstract reviews."""
import copy
import hashlib
import json
from pathlib import Path
import tempfile
import unittest

import yaml
from check_palomar_abstract_coverage import validate_abstract_coverage


class AbstractCoverageTest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.metadata = {"project": {"description": "Recovery and native and specification backdoor lower bounds."}}
        self.config = {"challenge_module": "Challenge", "theorem_names": ["recovery", "native", "specification"]}
        (self.root / "Challenge.lean").write_text("module\n-- statement fixture\n")
        self.ledger = {
            "schema_version": 1, "metadata_path": "formalization.yaml", "comparator_path": "comparator.json",
            "review": {"method": "manual-semantic-review", "reviewer": "Test fixture",
                       "rationale": "Recovery and two backdoor statements form two result families."},
            "families": [
                {"id": "recovery", "theorems": ["recovery"], "account": "Recover the supplied source.",
                 "abstract_quotes": ["Recovery"]},
                {"id": "backdoors", "theorems": ["native", "specification"],
                 "account": "Backdoor lower bounds for both representations.",
                 "abstract_quotes": ["native and specification backdoor lower bounds"]},
            ],
        }
        self.write_inputs()
        self.rebind()

    def write_inputs(self):
        (self.root / "formalization.yaml").write_text(yaml.safe_dump(self.metadata))
        (self.root / "comparator.json").write_text(json.dumps(self.config))

    def rebind(self):
        self.ledger["input_sha256"] = {
            key: hashlib.sha256((self.root / path).read_bytes()).hexdigest()
            for key, path in [("metadata", "formalization.yaml"), ("comparator", "comparator.json"),
                              ("challenge", "Challenge.lean")]
        }
        self.write_ledger()

    def write_ledger(self):
        (self.root / "coverage.json").write_text(json.dumps(self.ledger))

    def check(self):
        return validate_abstract_coverage(self.root, self.metadata, "formalization.yaml",
                                          "comparator.json", "coverage.json")

    def test_complete_map_passes(self):
        self.assertEqual(self.check()["theorems_checked"], 3)

    def test_missing_ledger_fails(self):
        (self.root / "coverage.json").unlink()
        with self.assertRaisesRegex(ValueError, "Missing"):
            self.check()

    def test_p06_omission_rejected_even_after_rehash(self):
        self.metadata["project"]["description"] = "Recovery and width lower bounds."
        self.write_inputs(); self.rebind()
        with self.assertRaisesRegex(ValueError, "omits.*backdoors"):
            self.check()

    def test_deleted_family_leaves_uncovered_selection(self):
        self.ledger["families"].pop(); self.write_ledger()
        with self.assertRaisesRegex(ValueError, "missing=.*native"):
            self.check()

    def test_new_selected_theorem_needs_family(self):
        self.config["theorem_names"].append("new_result")
        self.write_inputs(); self.rebind()
        with self.assertRaisesRegex(ValueError, "missing=.*new_result"):
            self.check()

    def test_input_edits_invalidate_review(self):
        for name in ["formalization.yaml", "comparator.json", "Challenge.lean"]:
            with self.subTest(name=name):
                path = self.root / name; original = path.read_bytes()
                path.write_bytes(original + b"\n")
                with self.assertRaisesRegex(ValueError, "Stale"):
                    self.check()
                path.write_bytes(original)

    def test_repeated_and_unknown_theorems_rejected(self):
        original = copy.deepcopy(self.ledger)
        for name in ["recovery", "unknown"]:
            self.ledger = copy.deepcopy(original)
            self.ledger["families"][1]["theorems"].append(name); self.write_ledger()
            with self.assertRaisesRegex(ValueError, "coverage differs"):
                self.check()

    def test_empty_quote_cannot_cover_family(self):
        self.ledger["families"][1]["abstract_quotes"] = [" "]; self.write_ledger()
        with self.assertRaisesRegex(ValueError, "Missing abstract quotes"):
            self.check()

    def test_wrong_input_paths_rejected(self):
        self.ledger["metadata_path"] = "other.yaml"; self.write_ledger()
        with self.assertRaisesRegex(ValueError, "metadata_path differs"):
            self.check()

    def test_review_cannot_be_missing_or_automatic(self):
        for review in [{}, {"method": "keyword-match", "reviewer": "Tool"}]:
            self.ledger["review"] = review; self.write_ledger()
            with self.assertRaisesRegex(ValueError, "manual semantic review"):
                self.check()

    def test_yaml_folded_whitespace_is_accepted(self):
        self.ledger["families"][1]["abstract_quotes"] = ["native and\n specification backdoor lower bounds"]
        self.write_ledger(); self.assertEqual(self.check()["status"], "pass")


if __name__ == "__main__":
    unittest.main(verbosity=2)
