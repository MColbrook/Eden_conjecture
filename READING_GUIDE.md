# Reading the formalisation

The essential human check is that the formal statements and definitions express the mathematics in the paper. Once the Lean kernel checks, the Comparator run and the permitted-axiom checks are trusted for these files, the deductions between those statements are certified. Reading every tactic is unnecessary for that purpose.

Comparator compares the formal statements in `Challenge.lean` and `Solution.lean`. Both import the same `Eden` library. Agreement between them therefore does not by itself establish that a shared definition agrees with the manuscript. The reading below concentrates on that correspondence.

## 1. Read the main statements

Open the manuscript alongside [Challenge.lean](Challenge.lean). Begin with `main_theorem`, `example_c_eight`, `attractor_lemma` and `planar_singular_value_lemma`. Read each declaration from `theorem` through its proposition, stopping at `:= by`. The `sorry` in this file is a specification placeholder. The corresponding proofs are in [Solution.lean](Solution.lean), which does not import Challenge.

For `main_theorem`, check the following against the manuscript:

- The only parameter restriction is `c : ℝ` with `4 < c`.
- The initial-value problem and its uniqueness concern every point of the ambient five-dimensional space. Forward time includes zero; the dimension conclusions use every positive real time.
- The derivative is the ambient derivative. C¹ regularity and invertibility of the derivative are conclusions.
- Global attraction includes uniform attraction of bounded sets.
- Divergence is negative throughout the ambient space.
- The maximum dimension is `4 + 4 / c`, attained precisely on the stated torus, both at finite time and asymptotically.
- The maximum over the equilibrium and periodic set is `3`, including attainment.
- Every torus point has no positive real return time. The angular formula has frequencies `1` and `sqrt 2`.
- Convergence of local dimensions holds at every point of the attractor through real time.

The attraction lemma quantifies over arbitrary bounded sets. The planar singular-value lemma quantifies over every planar point, including the origin, arbitrary real angular frequency, and every positive real time. Its multiset equality retains both singular values and their multiplicities.

Check the numerical example separately: `c = 8` gives `9 / 2` globally and `3` on the equilibrium and periodic set.

## 2. Resolve the names in those statements

The following files contain the principal definitions. Read the definitions themselves, rather than relying on their names or comments.

| File and declarations | Mathematical check |
| --- | --- |
| [Basic.lean](Eden/Basic.lean): `PhaseSpace`, `radiusSq₁`, `radiusSq₂`, `q`, `vectorField`, `attractor`, `torus`, `radialRate`, `tangentialRate` | `PhaseSpace` is `EuclideanSpace ℝ (Fin 5)`. Coordinates are `(Re z₁, Im z₁, Re z₂, Im z₂, w)`. Check every sign and coefficient in the field, the frequencies, and the fifth component `-c*w`. The variables `radiusSq₁` and `radiusSq₂` are squared radii: the disc bound is `2`, and the torus value is `1`. The variational rates are `-5*s^2 + 9*s - 2` and `-s^2 + 3*s - 2`. |
| [Evolution.lean](Eden/Evolution.lean): `evolution` | This is the map used throughout the conclusions. Its identification with the intended flow is certified by the initial-condition, ODE and uniqueness clauses in `main_theorem`. Those clauses let the reader establish its meaning without independently checking the explicit radial solution formula. |
| [PlanarVectorField.lean](Eden/PlanarVectorField.lean) and [PlanarDerivative.lean](Eden/PlanarDerivative.lean): `PlanarSpace`, `planarVectorField`, `planarEvolution` | For the planar lemma, check the Euclidean two-dimensional space and the arbitrary-frequency version of one planar block. Read `planarEvolution_zero_time`, `hasDerivAt_planarEvolution` and `contDiff_planarEvolution` to identify the map and its derivative. |
| [TorusAngles.lean](Eden/TorusAngles.lean): `torusPoint` | Check the cosine/sine parametrisation. `D06_torus_angle_coordinates` identifies its image with the whole torus and states the two angular periods. |
| [UniformAttraction.lean](Eden/UniformAttraction.lean): `UniformlyAttractsBounded`, `IsGlobalAttractor` | Check nonemptiness, compactness, strict invariance `evolution c t '' K = K`, and the order of quantifiers in attraction: for each bounded set and each positive tolerance, one time works for every initial point in the set. Minimality is separately stated in this file and among the final dynamics results. |
| [Divergence.lean](Eden/Divergence.lean): `divergence` | It is the trace of the Fréchet derivative of `vectorField`. The polynomial expression is a proved identity. |
| [SingularValueFunction.lean](Eden/SingularValueFunction.lean): `singularWeight`, `spectralProduct`, `singularValueFunction`, `admissibleDimensions`, `mapLyapunovDimension`, `finiteTimeDimension`, `globalLyapunovDimension` | The factors are Mathlib's ordered singular values of the ambient derivative. For `d = k + α`, the function is the product of the first `k` singular values times the next one to power `α`. The full dimension interval is `[0,5]`; admissibility includes equality with `1`. The global definition takes the spatial supremum first and then the infimum over positive real times. |
| [LyapunovExponents.lean](Eden/LyapunovExponents.lean): `normalizedLogSingularValues`, `lyapunovExponent` | These are logarithms of ordered derivative singular values divided by real time. The `Tendsto` clause of the main theorem establishes the existence of every limit. |
| [KaplanYorke.lean](Eden/KaplanYorke.lean): `spectrumPartialSum`, `nonnegativeSumIndices`, `kaplanYorkeIndex`, `kaplanYorkeDimension`, `asymptoticDimension` | The index is the largest integer from `0` through `5` with a nonnegative partial sum. Zero partial sums count. Check the branches at indices `0` and `5`, and the denominator involving the next exponent in the middle branch. |
| [PeriodicSets.lean](Eden/PeriodicSets.lean): `equilibriumSet`, `positiveReturnSet`, `periodicEquilibriumSet` | The set is defined using the vector field and existence of a positive real return time, intersected with the attractor. The four circles are subsequently proved to classify the nonstationary periodic orbits. |

Several short interfaces in Challenge make these identifications explicit: `D02_euclidean_geometry`, `D04_polynomial_field`, `D05_actual_forward_flow`, `D07_ordered_positive_singular_values`, `D08_singular_value_function`, `D09_attainment_and_infimum`, the three `D10` convention/exponent statements, and `D11_periodic_union_and_orbits`.

A few Lean conventions deserve attention:

| Lean notation | Meaning in this development |
| --- | --- |
| `(hc : 4 < c)` before the colon | A hypothesis. Check every such argument, including implicit arguments in braces. |
| `∀ p ∈ attractor, ...` | Every point of the attractor; no almost-everywhere qualification. |
| `f '' A` | The image set `{f(x) : x ∈ A}`. |
| `IsGreatest S a` | `a` belongs to `S` and bounds every element of `S` above; the maximum is attained. |
| `Icc 0 5`, `Ici 0` | The closed interval `[0,5]` and the half-line `[0,∞)`. |
| `Fin 5` | Five indices numbered `0,...,4`; Lean index `4` is the fifth exponent. |
| `Tendsto f atTop (𝓝 L)` with real input | The ordinary limit of `f(t)` as real `t` tends to infinity. |
| `limUnder` | A selected limit value. Its definition alone does not assert convergence; read the accompanying `Tendsto` theorem. |
| `sSup`, `sInf` | Supremum and infimum. Check the domain, order of operations and the theorems establishing the required bounds or attainment. |
| `fderiv ℝ f p` | The ambient Fréchet derivative. Its useful derivative interpretation is supported here by the differentiability conclusions. |

For the standard library conventions, the pinned Mathlib files are `Mathlib/Analysis/InnerProductSpace/SingularValues.lean` and `Mathlib/Topology/MetricSpace/HausdorffDimension.lean`. The first defines singular values as square roots of the ordered Gram-operator eigenvalues, with multiplicity; the second defines Hausdorff dimension. They are downloaded with the pinned dependency and need not be copied into this repository.

## 3. Check the further mathematical statements

Continue through the geometric and dynamical consequences and the periodic-growth and concavity sections of [Challenge.lean](Challenge.lean). These supplement the main theorem.

| Topic and final declarations | Definitions to inspect and distinctions to preserve |
| --- | --- |
| Exterior growth: `s01_*`, `s04_exterior_operator_identity` | [ExteriorGeometry.lean](Eden/ExteriorGeometry.lean), [ExteriorMaximalGrowth.lean](Eden/ExteriorMaximalGrowth.lean), [ExteriorOperatorNorm.lean](Eden/ExteriorOperatorNorm.lean). These use the canonical exterior power of the ambient derivative. A nonzero vector is fixed before the time limit; the subsequent maximum over vectors is attained. |
| Common-index dimension: `s02_*`, `s03_periodic_common_index` | [ExponentSums.lean](Eden/ExponentSums.lean), [CommonIndex.lean](Eden/CommonIndex.lean). The index is chosen over the whole attractor and remains fixed when points are restricted to the periodic set. The periodic value under this convention is `4 - 2/c`; the pointwise Kaplan–Yorke maximum is `3`. |
| Global growth and its interpolant: `s04_global_growth`, `s05_real_time_limit`, `s06_*` | [GlobalGrowth.lean](Eden/GlobalGrowth.lean), [GlobalGrowthLimits.lean](Eden/GlobalGrowthLimits.lean), [GlobalGrowthDimension.lean](Eden/GlobalGrowthDimension.lean). The order is singular-value product, spatial supremum, logarithm, division by real time, then limit. The interpolation uses the global partial sums at integer nodes. |
| Hausdorff dimensions and torus directions: `s07_*` | [HausdorffDimensions.lean](Eden/HausdorffDimensions.lean), [TorusDirections.lean](Eden/TorusDirections.lean). Check Mathlib's `dimH` in the Euclidean metric, giving `4` for the attractor and `2` for the torus. The five ambient directions include both expanding radial directions. |
| Nontransitivity: `s08_*` | [Nontransitivity.lean](Eden/Nontransitivity.lean). The radial regions are subsets of the attractor and are open in its subspace topology. The results concern both dense orbits and the open-set transitivity condition. |
| Recurrence: `s09_recurrent_aperiodic_torus` | [TorusRecurrence.lean](Eden/TorusRecurrence.lean). `torusEvolution` is the restriction of the same flow. There is a return to every neighbourhood after every prescribed time bound; separately, no positive real time fixes the point. |
| Frequency changes: `s10_*` | [FrequencyEvolution.lean](Eden/FrequencyEvolution.lean), [FrequencyAttractor.lean](Eden/FrequencyAttractor.lean), [FrequencyDimensions.lean](Eden/FrequencyDimensions.lean), [RationalFrequency.lean](Eden/RationalFrequency.lean). Only the second angular frequency changes. Read the new attractor, dimension and periodic-set definitions. The nearby frequencies are positive rationals arbitrarily close to `sqrt 2`; `2*pi*b` for frequency `a/b` is a common period. |
| Nonlinear instability: `s11_*` | [NonlinearInstability.lean](Eden/NonlinearInstability.lean). Check a fixed positive escape distance for arbitrarily small initial perturbations, with perturbations inside the attractor. The planar-circle statements additionally restrict them to their own coordinate planes. |
| Periodic-set global growth: `periodic_global_growth`, `periodic_global_dimension` | [PeriodicGlobalGrowth.lean](Eden/PeriodicGlobalGrowth.lean), [PeriodicGlobalDimension.lean](Eden/PeriodicGlobalDimension.lean). The supremum is over the full equilibrium and periodic set before the time limit. The six partial-sum nodes, including order zero, are `(0,2,2,0,-2,-2-c)`. The resulting interpolation dimension is `3`. |
| Concavity: `concave_interpolants` | [LogarithmicInterpolation.lean](Eden/LogarithmicInterpolation.lean), [InterpolationConcavity.lean](Eden/InterpolationConcavity.lean). The finite-time function is `log(ω_d)/t`, and the limiting function interpolates partial sums. Both use the whole closed interval `[0,5]`; finite time is positive. |

When another project-defined name occurs in one of these statements, follow its definition or a theorem identifying it with the intended mathematical object. A result about a quantity defined by a convenient formula acquires its intended meaning through those identifications.

## 4. Account for the proof calculations

For a review of the entire mathematical content, continue to the definitions, dynamics and spectral sections of Challenge. Together its six sections contain 219 declarations:

| Section | Declarations |
| --- | ---: |
| Main results | 4 |
| Geometric and dynamical consequences | 28 |
| Periodic growth and concavity | 3 |
| Definitions and basic properties | 14 |
| Dynamics | 94 |
| Spectral properties | 76 |

For each assertion or calculation in the paper, identify its formal statement and check its assumptions, quantifiers, constants and conclusion. [COVERAGE.md](COVERAGE.md) provides the subject map. Counts alone cannot establish completeness of the correspondence.

To follow the principal argument, the useful sequence is [PlanarSingularValues.lean](Eden/PlanarSingularValues.lean), [VolumeGrowth.lean](Eden/VolumeGrowth.lean), [FiniteTimeDimension.lean](Eden/FiniteTimeDimension.lean), [SpectrumTable.lean](Eden/SpectrumTable.lean), [DimensionTable.lean](Eden/DimensionTable.lean), [PeriodicOrbits.lean](Eden/PeriodicOrbits.lean), [PeriodicDimensions.lean](Eden/PeriodicDimensions.lean), and [DimensionConvergence.lean](Eden/DimensionConvergence.lean).

Their theorem statements expose the planar variational formula, sharp four-value product, equality set, six limiting spectra, periodic classification and dimension convergence. The neutral-exponent cases merit particular attention when matching the paper's argument. Inspecting their proofs can clarify that correspondence, although the trusted kernel already certifies the formal deductions.

The formalisation proves the stated mathematics through a Lean development. This is distinct from certifying every sentence of the manuscript word for word. Literature interpretation, historical assertions and the identification of the conjecture being refuted remain matters for mathematical reading and source review.

## 5. Confirm the checking scope

Inspect [comparator.json](comparator.json): it selects `Challenge`, `Solution` and all 219 final declarations, and permits only `propext`, `Classical.choice` and `Quot.sound`. The proof module imports `Eden`, not `Challenge`. The deliberate Challenge placeholders therefore supply specification statements rather than assumptions to the solution.

[checks/FinalAxioms.lean](checks/FinalAxioms.lean) lists the final results; [checks/SupportingAxioms.lean](checks/SupportingAxioms.lean) lists the 777 supporting theorems. [checks/VERIFICATION.md](checks/VERIFICATION.md) contains the completed checking record. The exact Lean version and dependencies are in [lean-toolchain](lean-toolchain), [lakefile.toml](lakefile.toml) and [lake-manifest.json](lake-manifest.json).

The correspondence review applies to the manuscript revision being compared and to the checked formal sources. Changes to a theorem, definition or proof require renewed checking; changes to the manuscript require checking the affected correspondence.

## 6. Publishing the repository

The contents of `eden_lean` form the repository root. Preserve the directories `Eden/`, `checks/`, `licenses/` and `.github/`, and include all root source, configuration and documentation files, including `.gitignore` and `.gitattributes`. `lean-toolchain` and `lakefile.toml` belong at the root, not inside an additional `eden_lean/` directory.

The local `.git/` directory is Git's repository database and is not a file upload. Build caches such as `.lake/` are excluded. All proof sources are present; Lake obtains the pinned dependencies during setup.

GitHub's browser uploader accepts at most 100 files per upload. The `Eden/` directory contains 97 files, so it can be uploaded as one batch and the remaining files as another, preserving their paths. A Git push can transfer the complete repository in one operation. See [GitHub's upload documentation](https://docs.github.com/en/repositories/working-with-files/managing-files/adding-a-file-to-a-repository).

The project licence is currently `UNLICENSED` in `formalization.yaml`; [NOTICE.md](NOTICE.md) preserves the licences and attribution of reused material.
