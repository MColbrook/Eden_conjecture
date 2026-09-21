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

## Independent Palomar statement

On 22 September 2026, the independent statement and proof wrapper were built
in an isolated Linux checkout using Lean 4.33.1 and the pinned dependency
manifest:

```sh
lake build PalomarSolution PalomarChallenge
python3 checks/check_axioms.py
```

The build completed successfully (3650 jobs). The axiom checker accepted all
219 original final declarations, 777 supporting theorems and
`EdenPalomar.main_theorem`, using only the three permitted axioms above.
The intentional `sorry` in `PalomarChallenge.lean` is the comparison target;
it is not imported by `PalomarSolution.lean`.

The new statement was checked against Theorem 1.1 and equations (1.1)--(1.7)
of the public Zenodo paper. Its dimensions use the ambient Euclidean derivative,
the flow's existence and forward uniqueness are explicit conclusions, and
attainment of the local-dimension supremum and existence of the exponent limits
are proved. See [PALOMAR.md](../PALOMAR.md) for the correspondence.

The independent pair also passed the documented local Comparator and Lean-kernel
replay after giving the index-nonemptiness helper a stable public name in both
modules. This diagnostic used the local Comparator revision listed above and
did not run NanoDa; the full Palomar workflow below supplies that check.

This build and axiom audit are distinct from Palomar's complete mechanical
preflight. That check is run through `.github/workflows/palomar.yml`, pinned to
PalomarSubmission commit `3561d237dcc4b28482558ad28a64d767d7cc8615`, with
`mode: full` and `palomar-comparator.json`. The GitHub Actions mechanical report
identifies its exact checked source commit and result; a passing report is
required before actual submission.
