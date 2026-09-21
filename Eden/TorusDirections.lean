import Eden.StationaryFactors
import Eden.ExponentSums
import Eden.HausdorffDimensions

/-!
# The five orthogonal directions on the invariant torus

The radial frame is an orthonormal basis of ambient Euclidean space. On the
torus its first/third vectors are radial, its second/fourth vectors are tangent
to the unit circles, and its fifth vector is the w direction. Their derivative
norms and real-time logarithmic limits are proved below. The Hausdorff and
Lyapunov dimensions are compared.
-/

noncomputable section
open Set Filter Topology MeasureTheory
namespace Eden

/-- The fixed initial radial frame as a complete ambient orthonormal basis. -/
def radialOrthonormalBasis (p : PhaseSpace) : OrthonormalBasis (Fin 5) ℝ PhaseSpace :=
  (EuclideanSpace.basisFun (Fin 5) ℝ).map (radialFrame p)

/-- Explicit unit vectors in radial/tangential/radial/tangential/w order on T. -/
theorem radialOrthonormalBasis_on_torus {p : PhaseSpace} (hp : p ∈ torus) :
    (fun i => radialOrthonormalBasis p i) =
      ![!₂[p 0, p 1, 0, 0, 0], !₂[-p 1, p 0, 0, 0, 0],
        !₂[0, 0, p 2, p 3, 0], !₂[0, 0, -p 3, p 2, 0], !₂[0, 0, 0, 0, 1]] := by
  have h₁ : p 0 ^ 2 + p 1 ^ 2 = 1 := hp.1
  have h₂ : p 2 ^ 2 + p 3 ^ 2 = 1 := hp.2.1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [radialOrthonormalBasis, radialFrame, rotateBlocks,
      EuclideanSpace.basisFun_apply, radialCos, radialSin, h₁, h₂]

theorem diagonalLinear_basisFun (d : PhaseSpace) (i : Fin 5) :
    diagonalLinear d (EuclideanSpace.basisFun (Fin 5) ℝ i) =
      d i • EuclideanSpace.basisFun (Fin 5) ℝ i := by
  ext j
  by_cases hij : i = j
  · subst j
    simp [EuclideanSpace.basisFun_apply]
  · simp [EuclideanSpace.basisFun_apply, Ne.symm hij]

theorem norm_fderiv_evolution_radialBasis (c : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (p : PhaseSpace) (i : Fin 5) :
    ‖fderiv ℝ (evolution c t) p (radialOrthonormalBasis p i)‖ = derivativeFactors c t p i := by
  change ‖fderiv ℝ (evolution c t) p (radialFrame p (EuclideanSpace.basisFun (Fin 5) ℝ i))‖ = _
  rw [fderiv_evolution_radialFrame c ht, (angularRotation t).norm_map,
    (radialFrame p).norm_map, diagonalLinear_basisFun, norm_smul,
    (EuclideanSpace.basisFun (Fin 5) ℝ).orthonormal.norm_eq_one]
  simp [Real.norm_eq_abs, abs_of_pos (derivativeFactors_pos c ht p i)]

/-- Exact norms in radial/tangential/radial/tangential/w order, all t≥0. -/
theorem norm_fderiv_torus_directions (c : ℝ) {t : ℝ} (ht : 0 ≤ t)
    {p : PhaseSpace} (hp : p ∈ torus) (i : Fin 5) :
    ‖fderiv ℝ (evolution c t) p (radialOrthonormalBasis p i)‖ =
      Real.exp ((![2, 0, 2, 0, -c] : Fin 5 → ℝ) i * t) := by
  rw [norm_fderiv_evolution_radialBasis c ht, derivativeFactors_on_torus c ht hp]
  fin_cases i <;> simp

/-- Each displayed direction has its stated ordinary real-time growth limit. -/
theorem tendsto_torus_direction_growth (c : ℝ) {p : PhaseSpace} (hp : p ∈ torus)
    (i : Fin 5) :
    Tendsto (fun t : ℝ => Real.log
      ‖fderiv ℝ (evolution c t) p (radialOrthonormalBasis p i)‖ / t)
      atTop (𝓝 ((![2, 0, 2, 0, -c] : Fin 5 → ℝ) i)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [norm_fderiv_torus_directions c ht.le hp i, Real.log_exp,
    mul_div_cancel_right₀ _ ht.ne']

/-- The sorted ambient exponents are (2,2,0,0,-c), with positive expansion rate two
and negative contracting rate -c for c>4. -/
theorem torus_direction_rates_and_ordered_exponents {c : ℝ} (hc : 4 < c)
    {p : PhaseSpace} (hp : p ∈ torus) :
    lyapunovExponent c p = ![2, 2, 0, 0, -c] ∧
      0 < (2 : ℝ) ∧ -c < 0 := by
  exact ⟨exponentSum_on_torus hc hp, by norm_num, by linarith⟩

/-- The geometric dimension of A is strictly below its global Lyapunov dimension. -/
theorem dimH_attractor_lt_globalLyapunovDimension {c : ℝ} (hc : 4 < c) :
    (dimH attractor).toReal < globalLyapunovDimension c attractor := by
  rw [dimH_attractor, globalLyapunovDimension_attractor hc]
  norm_num
  positivity

/-- The geometric torus dimension is strictly below the finite-time dimension there. -/
theorem dimH_torus_lt_finiteTimeDimension {c t : ℝ} (hc : 4 < c) (ht : 0 < t)
    {p : PhaseSpace} (hp : p ∈ torus) :
    (dimH torus).toReal < finiteTimeDimension c t p := by
  rw [dimH_torus, finiteTimeDimension_on_torus hc ht hp]
  norm_num
  have hd := (targetDimension_bounds hc).1
  dsimp [targetDimension] at hd
  linarith

end Eden
