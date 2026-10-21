# Completion-audit schema

[`completion-audit.json`](completion-audit.json) maps the numbered statements of the paper,
and the external results it cites, to Lean declarations. This page describes its format
(schema version 2). [`scripts/audit_schema.py`](../scripts/audit_schema.py) encodes the same
rules, and [`scripts/audit-evidence.py`](../scripts/audit-evidence.py) enforces them in
`scripts/check.sh`: an unknown key, status or reference fails the check.
[`statements.md`](statements.md) is generated from the file by `scripts/update-docs.py`.

## Top level

| Key | Content |
| --- | --- |
| `schema_version` | `2`. |
| `title`, `schema` | A title, and the path of this page. |
| `created_utc`, `baseline_commit` | When the audit was consolidated, and the commit it was consolidated at. |
| `source_documents` | The paper and the authors' addenda: URL, date and `text_sha256`. |
| `text_extraction` | How the texts were extracted: `text_sha256` is the SHA-256 of `pdftotext -layout` output (poppler 24.02), so anyone can recompute it from the PDFs. |
| `consolidated_from` | Names of the three per-section audits merged into this file. They were working files and are not kept in the repository. |
| `last_full_verification` | `date`, `command`, `result` and `note` of the last complete run of the checks. Counts are deliberately not recorded: they would go stale, and CI logs show them for every commit. |
| `path_convention` | How evidence paths are written. |
| `dependency_revisions` | The pinned Mathlib commit and the PrimeNumberTheoremAnd revision behind the Mertens adaptation. Both are checked against `lake-manifest.json` and `vendor/mertens/upstream.json`. |
| `model_caveats` | Modelling choices that apply to many requirements. |
| `requirements` | The audited statements of the paper (see below). |
| `external_dependencies` | Results the paper cites from the literature (see below). |
| `evidence` | The Lean declarations cited above (see below). |

## Requirements

| Key | Required | Content |
| --- | --- | --- |
| `id` | yes | A stable identifier, such as `2.2` or `main.theorem_1`. |
| `source_label` | yes | The paper's name for the statement: `Lemma 2.2`, `Theorem 1`, `Equation (5-4)`, or `Section 6, <description>` for an unnumbered claim. |
| `source_line` | yes | The line of the statement in the paper's text extraction, or `null` for an unnumbered claim. |
| `requirement` | yes | What has to be proved. |
| `statement_status` | yes | One of the statuses below. |
| `qualifier` | no | Only with `matched`: `coordinate_model` (proved for the coordinate-ideal model of varieties, not for Mathlib schemes) or `by_composition` (obtained by composing other audited results). |
| `in_addenda` | for discrepancies | Whether the authors' addenda of 20 April 2026 record the problem. |
| `correction` | for discrepancies | What is wrong with the printed statement or proof, and what is proved instead. |
| `scope` | yes | The exact scope of the Lean statement. |
| `evidence_refs` | yes | Evidence ids, at least one. |
| `counterexample_refs` | for `refuted` | The evidence ids (a subset of `evidence_refs`) that are formal counterexamples. Also allowed for `proof_repaired`, where the counterexample refutes a step of the printed proof. |
| `dependency_refs` | no | Ids of requirements or external dependencies the proof uses. |

### Statuses

Each requirement gets exactly one status, by the first rule that applies:

1. `refuted`: the printed statement is false in at least one case, and a Lean counterexample proves it. A corrected form is proved.
2. `corrected`: the printed statement is amended, by the addenda or by the formalisation (for example by an extra hypothesis), and the amended form is proved. The printed form is not formally refuted.
3. `proof_repaired`: the statement is true as printed and proved as printed, but the printed proof contains an error. The formalisation proves it another way.
4. `stronger`: a statement that implies the printed one is proved.
5. `matched`: the statement is proved as printed.

The first three are the discrepancies, which need `in_addenda` and `correction`. A statement
refuted only in an edge case, such as Lemma 2.2 for `n = 1` or Lemma 5.2 for `m = 0`, is still
`refuted`.

## External dependencies

| Key | Content |
| --- | --- |
| `id` | An identifier beginning with `external.`. |
| `reference` | The cited result. |
| `contract` | What the paper needs from it, and what the formalisation proves. |
| `dependency_status` | `proved_internally` (proved in this library, at least in the scope the paper needs), `vendored` (a proof vendored or adapted from another Lean project, see `vendor/`) or `mathlib` (a theorem of the pinned Mathlib). No external result is assumed. |
| `evidence_refs` | Evidence ids, at least one. |

## Evidence

| Key | Content |
| --- | --- |
| `id` | `e001`, `e002`, … |
| `file` | The declaring file, relative to the repository root: below `CCDN/`, `vendor/`, or `.lake/packages/mathlib/` for Mathlib. |
| `declaration` | The fully qualified Lean name. |

`audit-evidence.py` parses the file (it skips comments and tracks `namespace` and `section`)
and fails unless it declares that name. Mathlib evidence is checked only when Mathlib has been
fetched; the revision is pinned by `dependency_revisions.mathlib`. When a declaration is
renamed or moved, edit its entry by hand. Line numbers are not stored: `update-docs.py`
computes the `#L` anchors in `statements.md` when it generates the file, and `--check` only
reports anchors that have drifted, without failing.
