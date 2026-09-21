import Eden.FrequencySingularValues
import Eden.DimensionConvergence

/-!
# Dimensions in the frequency family

Equality of the ambient singular values gives equality of the finite-time
dimensions, Lyapunov exponents and limiting dimensions throughout the
frequency family.
-/

noncomputable section
open Set Filter Topology
namespace Eden

theorem singularValueFunction_frequencyEvolution (c ν : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (p : PhaseSpace) (d : ℝ) :
    singularValueFunction (fderiv ℝ (frequencyEvolution c ν t) p).toLinearMap d =
      singularValueFunction (fderiv ℝ (evolution c t) p).toLinearMap d := by
  simp only [singularValueFunction, singularValues_frequencyEvolution_eq c ν ht p]

/-- Finite-time dimension of the new ambient derivative. -/
def frequencyFiniteTimeDimension (c ν t : ℝ) (p : PhaseSpace) : ℝ :=
  mapLyapunovDimension (fderiv ℝ (frequencyEvolution c ν t) p).toLinearMap

theorem frequencyFiniteTimeDimension_eq (c ν : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (p : PhaseSpace) : frequencyFiniteTimeDimension c ν t p = finiteTimeDimension c t p := by
  simp only [frequencyFiniteTimeDimension, finiteTimeDimension, mapLyapunovDimension,
    admissibleDimensions, singularValueFunction_frequencyEvolution c ν ht]

/-- The same real-positive-time infimum of spatial suprema for the new flow. -/
def frequencyGlobalLyapunovDimension (c ν : ℝ) (K : Set PhaseSpace) : ℝ :=
  sInf {v : ℝ | ∃ t : ℝ, 0 < t ∧ v = sSup (frequencyFiniteTimeDimension c ν t '' K)}

theorem frequencyGlobalLyapunovDimension_eq (c ν : ℝ) (K : Set PhaseSpace) :
    frequencyGlobalLyapunovDimension c ν K = globalLyapunovDimension c K := by
  unfold frequencyGlobalLyapunovDimension globalLyapunovDimension
  congr 1
  ext v
  constructor <;> rintro ⟨t, ht, h⟩ <;> refine ⟨t, ht, ?_⟩
  · simpa only [frequencyFiniteTimeDimension_eq c ν ht.le] using h
  · simpa only [frequencyFiniteTimeDimension_eq c ν ht.le] using h

/-- Lyapunov exponent defined by the limiting normalized singular-value logarithm. -/
def frequencyLyapunovExponent (c ν : ℝ) (p : PhaseSpace) (i : Fin 5) : ℝ :=
  limUnder atTop (fun t : ℝ => Real.log
    ((fderiv ℝ (frequencyEvolution c ν t) p).toLinearMap.singularValues i) / t)

theorem tendsto_frequencyLogSingularValue (c ν : ℝ) (p : PhaseSpace) (i : Fin 5) :
    Tendsto (fun t : ℝ => Real.log
      ((fderiv ℝ (frequencyEvolution c ν t) p).toLinearMap.singularValues i) / t)
      atTop (𝓝 (lyapunovExponent c p i)) := by
  apply (tendsto_lyapunovExponent c p i).congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  rw [singularValues_frequencyEvolution_eq c ν ht p]

theorem frequencyLyapunovExponent_eq (c ν : ℝ) (p : PhaseSpace) (i : Fin 5) :
    frequencyLyapunovExponent c ν p i = lyapunovExponent c p i :=
  (tendsto_frequencyLogSingularValue c ν p i).limUnder_eq

/-- Ordinary real-time exponent limits for all real parameters and ambient initial points. -/
theorem tendsto_frequencyLyapunovExponent (c ν : ℝ) (p : PhaseSpace) (i : Fin 5) :
    Tendsto (fun t : ℝ => Real.log
      ((fderiv ℝ (frequencyEvolution c ν t) p).toLinearMap.singularValues i) / t)
      atTop (𝓝 (frequencyLyapunovExponent c ν p i)) := by
  rw [frequencyLyapunovExponent_eq]
  exact tendsto_frequencyLogSingularValue c ν p i

/-- The Kaplan--Yorke dimension of the new ordered exponent limits. -/
def frequencyAsymptoticDimension (c ν : ℝ) (p : PhaseSpace) : ℝ :=
  kaplanYorkeDimension (frequencyLyapunovExponent c ν p)

theorem frequencyAsymptoticDimension_eq (c ν : ℝ) (p : PhaseSpace) :
    frequencyAsymptoticDimension c ν p = asymptoticDimension c p := by
  unfold frequencyAsymptoticDimension asymptoticDimension
  congr 1
  funext i
  exact frequencyLyapunovExponent_eq c ν p i

/-- On A, finite-time dimensions converge for every real frequency when c > 4. -/
theorem tendsto_frequencyFiniteTimeDimension {c : ℝ} (hc : 4 < c) (ν : ℝ)
    {p : PhaseSpace} (hp : p ∈ attractor) :
    Tendsto (fun t : ℝ => frequencyFiniteTimeDimension c ν t p) atTop
      (𝓝 (frequencyAsymptoticDimension c ν p)) := by
  rw [frequencyAsymptoticDimension_eq]
  apply (tendsto_finiteTimeDimension hc hp).congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  exact (frequencyFiniteTimeDimension_eq c ν ht p).symm

/-- The finite-time maximum and exactly the same torus of maximisers. -/
theorem frequencyFiniteTimeDimension_bound_and_eq {c t : ℝ} (hc : 4 < c)
    (ν : ℝ) (ht : 0 < t) {p : PhaseSpace} (hp : p ∈ attractor) :
    frequencyFiniteTimeDimension c ν t p ≤ targetDimension c ∧
      (frequencyFiniteTimeDimension c ν t p = targetDimension c ↔ p ∈ torus) := by
  rw [frequencyFiniteTimeDimension_eq c ν ht.le]
  exact ⟨finiteTimeDimension_le_target hc ht hp, finiteTimeDimension_eq_target_iff hc ht hp⟩

/-- The limiting maximum and exactly the same torus of maximisers. -/
theorem frequencyAsymptoticDimension_bound_and_eq {c : ℝ} (hc : 4 < c)
    (ν : ℝ) {p : PhaseSpace} (hp : p ∈ attractor) :
    frequencyAsymptoticDimension c ν p ≤ targetDimension c ∧
      (frequencyAsymptoticDimension c ν p = targetDimension c ↔ p ∈ torus) := by
  rw [frequencyAsymptoticDimension_eq]
  exact ⟨asymptoticDimension_le_target hc p, asymptoticDimension_eq_target_iff hc hp⟩

theorem frequencyFiniteTimeDimension_isGreatest {c t : ℝ} (hc : 4 < c) (ν : ℝ)
    (ht : 0 < t) :
    IsGreatest (frequencyFiniteTimeDimension c ν t '' attractor) (targetDimension c) := by
  simp only [frequencyFiniteTimeDimension_eq c ν ht.le]
  exact finiteTimeDimension_attractor_isGreatest hc ht

theorem frequencyAsymptoticDimension_isGreatest {c : ℝ} (hc : 4 < c) (ν : ℝ) :
    IsGreatest (frequencyAsymptoticDimension c ν '' attractor) (targetDimension c) := by
  simp only [frequencyAsymptoticDimension_eq]
  exact asymptoticDimension_attractor_isGreatest hc

/-- The positive-time infimum of the spatial suprema on A equals 4 + 4/c. -/
theorem frequencyGlobalLyapunovDimension_attractor {c : ℝ} (hc : 4 < c) (ν : ℝ) :
    frequencyGlobalLyapunovDimension c ν attractor = 4 + 4 / c := by
  rw [frequencyGlobalLyapunovDimension_eq, globalLyapunovDimension_attractor hc]

end Eden
