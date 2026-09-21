# Palomar submission

The entry title is **A counterexample to the unrestricted form of Eden's conjecture**.
It is supplied by `project.name` in [formalization.yaml](formalization.yaml).

## Submission selection

| Field | Value |
| --- | --- |
| Repository | `MColbrook/Eden_conjecture` |
| Commit | The full 40-character SHA that passed the full preflight |
| Project path | Leave blank (repository root) |
| Comparator configuration | `palomar-comparator.json` |
| Metadata path | Leave blank (`formalization.yaml` at repository root) |
| Relationship | Responsible author or maintainer of the substantive formalization |
| Existing Palomar ID | Leave blank for the first submission |

The selected declaration is `EdenPalomar.main_theorem`.
[PalomarChallenge.lean](PalomarChallenge.lean) is its independent statement;
[PalomarSolution.lean](PalomarSolution.lean) supplies the proof. The Challenge
imports only Mathlib. The Solution uses the substantive development in this
repository through `Solution.lean`.

The original [comparator.json](comparator.json) continues to select all 219
declarations in `EdenVerified`. It is an internal comprehensive comparison
suite, not the Palomar submission configuration. The submission records the
main counterexample as one theorem; it does not separately register every
supporting calculation, both lemmas, or the further results in Section 3.

## Mathematical correspondence

The source of record is the public paper at
[DOI 10.5281/zenodo.22883032](https://doi.org/10.5281/zenodo.22883032), published
21 September 2026. The metadata hash identifies the PDF in that version-specific
record. The source's full title is retained in its bibliographic entry.

| Paper | Independent formal statement |
| --- | --- |
| Ambient Euclidean space | `PhaseSpace = EuclideanSpace ℝ (Fin 5)` |
| Polynomial ODE (1.6) | `vectorField`, with the exact real-coordinate formula |
| Attractor and torus (1.7) | `attractor` and `torus`, using squared radii |
| Singular-value function (1.1) | `singularValueFunction`, a truncated-weight product on `[0,5]` |
| Finite-time dimension (1.2) | `finiteTimeDimension`, with maximum attainment proved in the theorem |
| Global dimension (1.3) | `globalLyapunovDimension`, with the same infimum/supremum order |
| Exponents (1.4) | `lyapunovExponent`, with real-time convergence proved |
| Kaplan--Yorke convention (1.5) | `kaplanYorkeDimension`, including zero partial sums and endpoint cases |
| Forward completeness and global attractor | Existence of a forward ODE flow, uniqueness, semigroup law, compactness, strict invariance and uniform attraction of every bounded set |
| Negative divergence | Trace of the Fréchet derivative, with the exact identity and global bound |
| Maxima and maximisers (1.8)--(1.9) | Greatest values `4 + 4/c` and equality sets exactly the unit torus |
| Equilibria and periodic orbits (1.10) | Explicit vector-field zeros and positive return times, intersected with the attractor; both maxima are `3` |
| Aperiodicity and convergence | No positive return on the torus; exact angular motion with frequencies `1, √2`; pointwise convergence of local dimensions |

The flow is existentially quantified, and the theorem supplies its ODE and
initial condition rather than assuming an abstract flow with the desired
properties. Its forward uniqueness is also proved. The proof uses the existing
explicit `Eden.evolution`; the other definitions reduce to their counterparts
in the original development. This preserves the connection to the ambient
derivative and ordinary singular values.

Time is real, and the ODE and completeness claims concern nonnegative time.
The theorem additionally provides the exact angular formula on the torus for
all real times. The dimension `sSup` is a maximum because attainment is included
explicitly; the `limUnder` exponents are actual limits because convergence is
included explicitly. The index convention includes neutral directions.

The result concerns the unrestricted conjecture. The constructed attractor is
nontransitive, as discussed on page 2 of the paper and proved in the broader
library. This submission does not claim to settle variants restricted to
transitive, strange, or typical attractors. Historical and literature assertions
are not Lean theorem statements.

## Authorship, automation and review

Matthew J. Colbrook is the author and responsible maintainer. The paper's
page 9 AI declaration records ChatGPT 6 discussions, use of Codex to explore
the conjecture and obtain the counterexample, and AI assistance with the Lean
verification. It also records the author's checking of the proof and problem
formulation against the paper, the use of Lean Comparator and axiom checks,
and the author's adoption of and responsibility for the paper's contents.

Codex prepared the independent Palomar statement and proof wrapper, checked
their correspondence with the published definitions and Theorem 1.1, and
prepared the metadata and preflight workflow. This is not a claim that the new
wrapper has received a separate human review. The original development's
verification record is in [checks/VERIFICATION.md](checks/VERIFICATION.md).
Current build and preflight results are available through GitHub Actions.

The repository is licensed under [Apache-2.0](LICENSE). The paper has its
separate CC-BY-4.0 licence. See [NOTICE.md](NOTICE.md) for reused-material credits.

## Checks before submission

```sh
lake exe cache get
lake build Eden Solution Challenge PalomarChallenge PalomarSolution
python3 checks/check_axioms.py
```

Run the **Palomar full preflight** workflow on the intended commit. Its reusable
workflow reference and `pipeline_commit` input are pinned to the same revision
of `PalomarRegistry/PalomarSubmission`. It uses `mode: full`, the normal
`palomar-standard-v1` resource profile, and `palomar-comparator.json`.

```sh
git rev-parse HEAD
gh workflow run palomar.yml --ref main -f commit=FULL_40_CHARACTER_SHA
gh run list --workflow palomar.yml
```

Inspect the uploaded mechanical report: it must report `status: pass` for that
exact repository, commit and configuration. A local build, the regular Lean CI,
or the older comparison suite is not a substitute. The full preflight checks
Challenge provenance, repository licensing and metadata, and replays the
exported proof through Lean and NanoDa. It does not perform Palomar's editorial
review or create a registry entry. If files change, commit and push them and run
the full preflight on the new commit before submitting.

## Actual submission by the maintainer

1. Review the independent statement and metadata, including the entry title,
   source citation, scope and production/review disclosure.
2. Open [Palomar's submission form](https://submit.palomar-registry.org/).
   Enter the values in the table above and the exact SHA from the passing
   preflight. Select the author/maintainer relationship.
3. Complete the GitHub sign-in yourself to establish repository write access.
   Save the private status-page link; it is needed to return to the submission.
4. Wait for Palomar's mechanical verification and automated editorial review.
   Address any requested source changes through a new commit and submission.
5. Read the review before choosing **Register**. Registration publishes the
   immutable record and review and is intended to be permanent. The entry
   becomes registered after its database pull request merges. Keep the final
   version-specific Palomar URL for citation.

An agent should instead follow Palomar's documented API authentication route,
not automate the human GitHub sign-in. Neither route should be used until the
full preflight has passed. See the current
[submission policy](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md)
and [agent/preflight protocol](https://submit.palomar-registry.org/llms.txt).
