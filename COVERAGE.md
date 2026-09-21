# Mathematical scope

The formalisation covers the mathematical results and proof calculations in *Aperiodic maximisers of Lyapunov dimension: a counterexample to the unrestricted form of Eden's conjecture*, by Matthew J. Colbrook. The literature survey and historical statements are outside this scope.

The ambient space is Euclidean ℝ⁵, identified with ℂ² × ℝ. For $c>4$, the vector field is

$$
\dot z_1=(q(|z_1|^2)+i)z_1,\qquad
\dot z_2=(q(|z_2|^2)+i\sqrt2)z_2,\qquad
\dot w=-cw,
\quad q(s)=-(s-1)(s-2).
$$

The attractor and maximising torus are

$$
A=\{(z_1,z_2,0):|z_1|,|z_2|\le\sqrt2\},\qquad
\mathcal T=\{(z_1,z_2,0):|z_1|=|z_2|=1\}.
$$

All derivatives and singular values use the ambient Euclidean structure. All time limits are limits through real time. The formal development uses squared radii for several calculations and proves their correspondence with the ordinary radii used in the paper.

## Principal results

The declarations in [Solution.lean](Solution.lean) belong to the namespace `EdenVerified`.

| Declaration | Result |
| --- | --- |
| `main_theorem` | Theorem 1.1: forward completeness, the compact global attractor, negative divergence, the exact finite-time and asymptotic dimension maxima, their maximising sets, the periodic-orbit gap, aperiodicity of the torus, and convergence of the local dimensions. |
| `example_c_eight` | The example $c=8$, with global dimension $9/2$ and maximum $3$ over equilibria and periodic orbits. |
| `attractor_lemma` | The attractor lemma, including strict invariance and uniform attraction of bounded sets. |
| `planar_singular_value_lemma` | The planar singular-value lemma, for arbitrary real angular frequency, every initial point, and every positive real time. |

The supplementary results include growth of exterior vectors, common-index dimensions, subadditive global growth and its real-time limits, Hausdorff dimensions, nontransitivity, recurrence, rational changes of angular frequency, and nonlinear instability. In particular, they establish:

- Hausdorff dimensions $\dim_{\mathrm H}A=4$ and $\dim_{\mathrm H}\mathcal T=2$.
- Common-index dimension $4+4/c$ on $A$, and maximum $4-2/c$ on the equilibrium and periodic set when the global index is retained.
- Dimension $4+4/c$ from interpolation of the global growth sums.
- Periodic-set growth sums $(2,2,0,-2,-2-c)$, with interpolation dimension $3$.
- Concavity of the finite-time and limiting partial-sum interpolants throughout $[0,5]$.
- Positive rational angular frequencies arbitrarily close to $\sqrt2$ for which the same torus consists of periodic maximisers.

## Final declarations

The 219 declarations in `Solution.lean` are grouped as follows. Each has a corresponding statement in [Challenge.lean](Challenge.lean).

| Group | Number | Contents |
| --- | ---: | --- |
| Main results | 4 | The main theorem, the $c=8$ example, and both lemmas. |
| Supplementary results | 28 | Exterior growth, dimension conventions, geometry, recurrence, frequency changes, and instability. |
| Periodic global growth and concavity | 3 | The periodic growth sums and dimension; concavity of both interpolants. |
| Definitions and conventions | 14 | Euclidean geometry, the polynomial field and its flow, singular-value functions, dimension conventions, and the periodic set. |
| Dynamics calculations | 94 | Radial flow, attraction, planar variation, periodic orbits, and convergence of local dimensions. |
| Spectral calculations | 76 | Ambient derivatives, growth factors, exact singular-value identities, limiting spectra, and dimension calculations. |

## Library organisation

[Eden.lean](Eden.lean) imports the complete supporting library. The following modules provide entry points to its main parts.

| Subject | Modules |
| --- | --- |
| Scalar and planar dynamics | `ScalarFlow`, `ScalarCalculus`, `PlanarFlow`, `RadialDynamics`, `PhysicalRadius` |
| Ambient flow and vector field | `Evolution`, `Uniqueness`, `JointSmoothness`, `PolynomialVectorField`, `Divergence` |
| Global attractor | `InvariantSets`, `StrictInvariance`, `UniformAttraction`, `CompleteTrajectories` |
| Derivatives and singular values | `CartesianDerivative`, `DerivativeDecomposition`, `SingularValues`, `PlanarSingularValues`, `PlanarMovingFrame` |
| Exact finite-time dimensions | `VolumeGrowth`, `SingularValueFunction`, `FiniteTimeDimension` |
| Limiting spectra and dimensions | `LyapunovExponents`, `SpectrumTable`, `KaplanYorke`, `DimensionTable` |
| Convergence of local dimensions | `LogarithmicInterpolation`, `FiniteTimeKaplanYorke`, `DimensionConvergence`, `EventualDimensionFormulas` |
| Periodic orbits | `PeriodicSets`, `PeriodicOrbits`, `PeriodicDimensions`, `PeriodicGap` |
| Exterior growth and common-index dimensions | `ExteriorLimits`, `ExteriorMaximalGrowth`, `CommonIndex`, `CommonIndexPeriodic` |
| Global growth and interpolation | `ExteriorSingularValues`, `GlobalGrowthLimits`, `ExactGlobalGrowth`, `GlobalGrowthDimension`, `PeriodicGlobalDimension`, `InterpolationConcavity` |
| Geometry and recurrence | `HausdorffDimensions`, `TorusDirections`, `Nontransitivity`, `TorusRecurrence` |
| Frequency changes and instability | `FrequencyEvolution`, `FrequencyDimensions`, `RationalFrequency`, `NonlinearInstability` |

The 777 public supporting theorems develop these arguments. Statement comparison is configured for the 219 declarations in `Solution.lean`; axiom reports are provided for both collections. The compilation and comparison commands are described in [README.md](README.md) and [checks/README.md](checks/README.md).
