# Verification record

Checked on 21 September 2026 with Lean 4.33.1 and the dependency revisions in
`lake-manifest.json`. All nine dependency repositories were at their pinned
commits with clean tracked sources.

The following commands completed successfully on Linux:

```sh
bash checks/run_comparator.sh
lake build Eden Solution Challenge
python3 checks/check_axioms.py
```

Comparator accepted all 219 declarations listed in `comparator.json` and
replayed their proofs with the Lean kernel. Its output included:

```text
Lean default kernel accepts the solution
Your solution is okay!
```

The build reported:

```text
Build completed successfully (3650 jobs).
```

The axiom check reported:

```text
PASS: checks/FinalAxioms.lean: 219 declarations; all axioms permitted.
PASS: checks/SupportingAxioms.lean: 777 declarations; all axioms permitted.
```

The permitted axioms are `propext`, `Classical.choice` and `Quot.sound`.
Each command exited with status zero. The release metadata also passed
validation against the published `formalization.yaml` v0.4 schema.

The GitHub workflow runs compilation and axiom checks on pushes and pull
requests. Comparator can be run separately using [the Linux instructions](README.md).
