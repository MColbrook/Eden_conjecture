import Eden.Algebra
import Eden.ScalarFlow
import Eden.ScalarCalculus
import Eden.PlanarFlow
import Eden.Evolution
import Eden.Uniqueness
import Eden.InitialDerivative
import Eden.CartesianDerivative
import Eden.GrowthRates
import Eden.OrthogonalFrames
import Eden.DerivativeFrames
import Eden.DerivativeDecomposition
import Eden.SingularValues
import Eden.StationaryFactors
import Eden.RadialDynamics
import Eden.InvariantSets
import Eden.StrictInvariance
import Eden.FactorBounds
import Eden.VolumeGrowth
import Eden.PhysicalRadius
import Eden.AttractorDistance
import Eden.UniformAttraction
import Eden.CompleteTrajectories
import Eden.SingularValueFunction
import Eden.FiniteTimeDimension
import Eden.OrderedStationarySpectrum
import Eden.RealTimeAverages
import Eden.FactorLimits
import Eden.Sorting
import Eden.LyapunovExponents
import Eden.KaplanYorke
import Eden.SpectrumTable
import Eden.DimensionTable
import Eden.LogarithmicInterpolation
import Eden.InterpolationSign
import Eden.FiniteTimeKaplanYorke
import Eden.DimensionConvergenceCriteria
import Eden.NeutralDimensionBounds
import Eden.LimitingInterpolation
import Eden.DimensionConvergence
import Eden.EventualDimensionFormulas
import Eden.RadialReturns
import Eden.RotationReturns
import Eden.PeriodicSets
import Eden.CircleOrbits
import Eden.PeriodicOrbits
import Eden.PeriodicDimensions
import Eden.PeriodicGap
import Eden.TorusAngles
import Eden.VectorFieldDerivative
import Eden.Divergence
import Eden.PlanarVectorField
import Eden.PolynomialVectorField
import Eden.JointSmoothness
import Eden.RadialQualitative
import Eden.AngularLifts
import Eden.VolumeConsequences
import Eden.PlanarDerivative
import Eden.PlanarSingularValues
import Eden.PlanarMovingFrame
import Eden.ExteriorGeometry
import Eden.LogarithmicSums
import Eden.ExteriorLimits
import Eden.SelectedSums
import Eden.ExteriorMaximalGrowth
import Eden.ExponentSums
import Eden.CommonIndex
import Eden.CommonIndexPeriodic
import Eden.Nontransitivity
import Eden.SelectedProducts
import Eden.ExteriorOperatorNorm
import Eden.ExteriorGram
import Eden.ExteriorSingularValues
import Eden.ExteriorCocycle
import Eden.IntegerGrowthBounds
import Eden.GlobalGrowth
import Eden.RealSubadditive
import Eden.GlobalGrowthLimits
import Eden.ExactGlobalGrowth
import Eden.GlobalGrowthDimension
import Eden.HausdorffGeometry
import Eden.HausdorffDimensions
import Eden.TorusDirections
import Eden.TorusRecurrence
import Eden.FrequencyEvolution
import Eden.FrequencyUniqueness
import Eden.FrequencyRotation
import Eden.FrequencyAttractor
import Eden.FrequencySingularValues
import Eden.FrequencyDimensions
import Eden.RationalFrequency
import Eden.InstabilityGeometry
import Eden.NonlinearInstability
import Eden.PeriodicGlobalGrowth
import Eden.PeriodicGlobalDimension
import Eden.InterpolationConcavity

/-!
# Eden's conjecture: a counterexample

The construction is a polynomial flow on five-dimensional Euclidean space. Its
compact global attractor has Lyapunov dimension 4+4/c, attained precisely on an
invariant irrational torus, whereas the maximum over equilibria and periodic
points is three. The parameter satisfies c>4.

The modules establish the flow, attractor, singular-value formulas, limiting
spectra and dimension formulas. Further results treat exterior powers,
subadditive growth, Hausdorff dimensions, recurrence, instability and rational
perturbations of the angular frequency. The principal statements are collected
in `Solution.lean`.
-/
