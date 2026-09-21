import Eden.RealTimeAverages
import Eden.GrowthRates
import Eden.InvariantSets
import Eden.DerivativeDecomposition

/-!
# Limits of the logarithmic derivative factors

Every nonnegative initial squared radius has a proved limiting squared
radius. Continuity of the rate polynomials and the real-time mean value
argument give the limits of the logarithmic factors and their integral
averages. These are the unsorted factors of the ambient derivative;
ordering the five limiting exponents is a separate step.
-/

noncomputable section
open Set Filter
open scoped Topology
namespace Eden

/-- The limiting squared radius, whose dynamical meaning is proved below. -/
def limitingSquaredRadius (s : ℝ) : ℝ :=
  if s < 1 then 0 else if s = 1 then 1 else 2

theorem tendsto_squaredRadiusEvolution_all (s : ℝ) :
    Tendsto (fun t => squaredRadiusEvolution t s) atTop (𝓝 (limitingSquaredRadius s)) := by
  rcases lt_trichotomy s 1 with hs | hs | hs
  · simpa [limitingSquaredRadius, hs] using tendsto_squaredRadiusEvolution_of_lt_one hs
  · subst s
    simp [limitingSquaredRadius]
  · simpa [limitingSquaredRadius, not_lt.mpr hs.le, ne_of_gt hs] using
      tendsto_squaredRadiusEvolution_of_one_lt hs

theorem tendsto_log_radialAmplitude_div {s : ℝ} (hs : 0 ≤ s) :
    Tendsto (fun t => Real.log (radialAmplitude t s) / t) atTop
      (𝓝 (radialRate (limitingSquaredRadius s))) := by
  apply tendsto_div_time_of_hasDerivAt
    (fun t ht => hasDerivAt_log_radialAmplitude ht hs)
  have hcont : Continuous radialRate := by unfold radialRate; fun_prop
  exact hcont.continuousAt.tendsto.comp (tendsto_squaredRadiusEvolution_all s)

theorem tendsto_log_planarAmplitude_div {s : ℝ} (hs : 0 ≤ s) :
    Tendsto (fun t => Real.log (planarAmplitude t s) / t) atTop
      (𝓝 (tangentialRate (limitingSquaredRadius s))) := by
  apply tendsto_div_time_of_hasDerivAt
    (fun t ht => hasDerivAt_log_planarAmplitude ht hs)
  have hcont : Continuous tangentialRate := by unfold tangentialRate; fun_prop
  exact hcont.continuousAt.tendsto.comp (tendsto_squaredRadiusEvolution_all s)

/-- The radial integral average converges along all real positive times. -/
theorem tendsto_radialRate_average {s : ℝ} (hs : 0 ≤ s) :
    Tendsto (fun t => (∫ τ in (0 : ℝ)..t,
      radialRate (squaredRadiusEvolution τ s)) / t) atTop
      (𝓝 (radialRate (limitingSquaredRadius s))) := by
  apply (tendsto_log_radialAmplitude_div hs).congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  rw [log_radialAmplitude_eq_integral ht hs]

/-- The tangential integral average converges along all real positive times. -/
theorem tendsto_tangentialRate_average {s : ℝ} (hs : 0 ≤ s) :
    Tendsto (fun t => (∫ τ in (0 : ℝ)..t,
      tangentialRate (squaredRadiusEvolution τ s)) / t) atTop
      (𝓝 (tangentialRate (limitingSquaredRadius s))) := by
  apply (tendsto_log_planarAmplitude_div hs).congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  rw [log_planarAmplitude_eq_integral ht hs]

theorem limiting_rates_of_lt_one {s : ℝ} (hs : s < 1) :
    radialRate (limitingSquaredRadius s) = -2 ∧
      tangentialRate (limitingSquaredRadius s) = -2 := by
  norm_num [limitingSquaredRadius, hs, radialRate, tangentialRate]

theorem limiting_rates_at_one :
    radialRate (limitingSquaredRadius 1) = 2 ∧
      tangentialRate (limitingSquaredRadius 1) = 0 := by
  norm_num [limitingSquaredRadius, radialRate, tangentialRate]

theorem limiting_rates_of_one_lt {s : ℝ} (hs : 1 < s) :
    radialRate (limitingSquaredRadius s) = -4 ∧
      tangentialRate (limitingSquaredRadius s) = 0 := by
  norm_num [limitingSquaredRadius, not_lt.mpr hs.le, ne_of_gt hs, radialRate, tangentialRate]

/-- Limits in radial/tangential block order; these are not yet sorted. -/
def factorExponents (c : ℝ) (p : PhaseSpace) : Fin 5 → ℝ :=
  ![radialRate (limitingSquaredRadius (radiusSq₁ p)),
    tangentialRate (limitingSquaredRadius (radiusSq₁ p)),
    radialRate (limitingSquaredRadius (radiusSq₂ p)),
    tangentialRate (limitingSquaredRadius (radiusSq₂ p)), -c]

theorem tendsto_log_derivativeFactors_div (c : ℝ) (p : PhaseSpace) (i : Fin 5) :
    Tendsto (fun t => Real.log (derivativeFactors c t p i) / t) atTop
      (𝓝 (factorExponents c p i)) := by
  fin_cases i
  · simpa [derivativeFactors, factorExponents] using
      tendsto_log_radialAmplitude_div (radiusSq₁_nonneg p)
  · simpa [derivativeFactors, factorExponents] using
      tendsto_log_planarAmplitude_div (radiusSq₁_nonneg p)
  · simpa [derivativeFactors, factorExponents] using
      tendsto_log_radialAmplitude_div (radiusSq₂_nonneg p)
  · simpa [derivativeFactors, factorExponents] using
      tendsto_log_planarAmplitude_div (radiusSq₂_nonneg p)
  · apply (tendsto_const_nhds (x := -c)).congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    simp [derivativeFactors]
    field_simp

end Eden
