"""The schema of docs/completion-audit.json (documented in docs/audit-schema.md)."""
from __future__ import annotations

import json
import re

from common import AUDIT

SCHEMA_VERSION = 2

# Requirement statuses, in the order used by the documentation.
STATUSES = {
    "matched": "proved as printed",
    "stronger": "a stronger statement is proved",
    "proof_repaired": "true as printed, but the printed proof is wrong; a repaired proof is "
                      "formalised",
    "corrected": "the printed statement is amended (by the addenda or by the formalisation) and "
                 "the amended form is proved; the printed form is not formally refuted",
    "refuted": "the printed statement is formally false in some case (a counterexample is "
               "proved in Lean); a corrected form is proved",
}
DISCREPANCIES = ("proof_repaired", "corrected", "refuted")
QUALIFIERS = {
    "coordinate_model": "in the coordinate-ideal model rather than for schemes",
    "by_composition": "by composing other audited results",
}
DEPENDENCY_STATUSES = {
    "proved_internally": "proved in this library, in at least the scope the paper needs",
    "vendored": "proof vendored or adapted from another Lean project (see vendor/)",
    "mathlib": "a theorem of the pinned Mathlib",
}
LABEL = re.compile(
    r"(?:Theorem|Proposition|Lemma|Corollary|Definition|Remark) \d+(?:\.\d+)*"
    r"|Equation \(\d+-\d+\)"
    r"|Section \d+(?:\.\d+)*, .+"
)
EVIDENCE_ROOTS = ("CCDN/", "CCDNPaper/", "vendor/", ".lake/packages/mathlib/")

TOP_LEVEL = {
    "schema_version", "title", "schema", "created_utc", "baseline_commit", "source_documents",
    "text_extraction", "consolidated_from", "last_full_verification", "path_convention",
    "dependency_revisions", "model_caveats", "requirements", "external_dependencies", "evidence",
}
REQUIREMENT_REQUIRED = {"id", "source_label", "source_line", "requirement", "statement_status",
                        "scope", "evidence_refs"}
REQUIREMENT_OPTIONAL = {"qualifier", "in_addenda", "correction", "counterexample_refs",
                        "dependency_refs"}
EXTERNAL_KEYS = {"id", "reference", "contract", "dependency_status", "evidence_refs"}
EVIDENCE_KEYS = {"id", "file", "declaration"}
VERIFICATION_KEYS = {"date", "command", "result", "note"}


def load() -> dict:
    return json.loads(AUDIT.read_text(encoding="utf-8"))


def _keys(where: str, item: dict, required: set[str], optional: set[str] = frozenset()) -> list:
    problems = [f"{where}: missing key {key!r}" for key in sorted(required - item.keys())]
    problems += [f"{where}: unknown key {key!r}"
                 for key in sorted(item.keys() - required - optional)]
    return problems


def validate(audit: dict) -> list[str]:
    """Every schema violation in `audit`; an empty list means the audit is well formed."""
    problems = _keys("top level", audit, TOP_LEVEL)
    if audit.get("schema_version") != SCHEMA_VERSION:
        problems.append(f"schema_version must be {SCHEMA_VERSION}")
    problems += _keys("last_full_verification", audit.get("last_full_verification", {}),
                      VERIFICATION_KEYS)

    evidence = audit.get("evidence", [])
    requirements = audit.get("requirements", [])
    externals = audit.get("external_dependencies", [])
    evidence_ids = [item.get("id") for item in evidence]
    node_ids = [item.get("id") for item in requirements + externals]
    for kind, ids in (("evidence", evidence_ids), ("requirement/external", node_ids)):
        duplicates = sorted({i for i in ids if ids.count(i) > 1})
        if duplicates:
            problems.append(f"duplicate {kind} ids: {duplicates}")
    referenced: set[str] = set()

    def refs(where: str, values, allowed, field: str) -> None:
        if not isinstance(values, list) or not values:
            problems.append(f"{where}: {field} must be a non-empty list")
            return
        for value in values:
            if value not in allowed:
                problems.append(f"{where}: {field} entry {value!r} does not exist")

    for item in requirements:
        where = f"requirement {item.get('id')}"
        problems += _keys(where, item, REQUIREMENT_REQUIRED, REQUIREMENT_OPTIONAL)
        status = item.get("statement_status")
        if status not in STATUSES:
            problems.append(f"{where}: unknown statement_status {status!r}")
        if not LABEL.fullmatch(str(item.get("source_label"))):
            problems.append(f"{where}: source_label {item.get('source_label')!r} does not follow "
                            "'Lemma 2.2', 'Equation (5-4)' or 'Section 6, ...'")
        line = item.get("source_line")
        if line is not None and not (isinstance(line, int) and line > 0):
            problems.append(f"{where}: source_line must be a positive integer or null")
        if "qualifier" in item and (item["qualifier"] not in QUALIFIERS or status != "matched"):
            problems.append(f"{where}: qualifier must be one of {sorted(QUALIFIERS)}, "
                            "and only with status 'matched'")
        discrepancy = status in DISCREPANCIES
        for field in ("in_addenda", "correction"):
            if discrepancy != (field in item):
                problems.append(f"{where}: {field} is required exactly for statuses "
                                f"{list(DISCREPANCIES)}")
        if "in_addenda" in item and not isinstance(item["in_addenda"], bool):
            problems.append(f"{where}: in_addenda must be true or false")
        if "correction" in item and not (isinstance(item["correction"], str)
                                         and item["correction"].strip()):
            problems.append(f"{where}: correction must be a non-empty string")
        refs(where, item.get("evidence_refs"), set(evidence_ids), "evidence_refs")
        referenced.update(item.get("evidence_refs") or [])
        counterexamples = item.get("counterexample_refs")
        if status == "refuted" and not counterexamples:
            problems.append(f"{where}: a refuted requirement needs counterexample_refs")
        if counterexamples is not None:
            if status not in ("refuted", "proof_repaired"):
                problems.append(f"{where}: counterexample_refs only with refuted/proof_repaired")
            refs(where, counterexamples, set(item.get("evidence_refs") or []),
                 "counterexample_refs")
        if "dependency_refs" in item:
            refs(where, item["dependency_refs"], set(node_ids), "dependency_refs")

    for item in externals:
        where = f"external dependency {item.get('id')}"
        problems += _keys(where, item, EXTERNAL_KEYS)
        if item.get("dependency_status") not in DEPENDENCY_STATUSES:
            problems.append(f"{where}: unknown dependency_status {item.get('dependency_status')!r}")
        refs(where, item.get("evidence_refs"), set(evidence_ids), "evidence_refs")
        referenced.update(item.get("evidence_refs") or [])

    for item in evidence:
        where = f"evidence {item.get('id')}"
        problems += _keys(where, item, EVIDENCE_KEYS)
        if not str(item.get("file", "")).startswith(EVIDENCE_ROOTS):
            problems.append(f"{where}: file must lie below one of {list(EVIDENCE_ROOTS)}")
        if item.get("id") not in referenced:
            problems.append(f"{where}: not referenced by any requirement or external dependency")
    return problems
