import Eden

/-!
# Statements for independent comparison

The theorem statements corresponding to `Solution.lean`, with proof placeholders
for Lean Comparator. Time is real and the ambient space carries the Euclidean
norm.
-/

noncomputable section
open Set Filter
open scoped Topology
open Eden

namespace EdenVerified

/-!
## Main results
-/

theorem main_theorem (c : ℝ) (hc : 4 < c) :
    (∀ p : PhaseSpace, evolution c 0 p = p ∧
      ∀ t : ℝ, 0 ≤ t → HasDerivAt (fun τ => evolution c τ p)
        (vectorField c (evolution c t p)) t) ∧
    (∀ (p : PhaseSpace) (f : ℝ → PhaseSpace),
      ContinuousOn f (Ici 0) →
      (∀ t : ℝ, 0 ≤ t → HasDerivWithinAt f (vectorField c (f t)) (Ici t) t) →
      f 0 = p → EqOn f (fun t => evolution c t p) (Ici 0)) ∧
    (∀ (s t : ℝ), 0 ≤ s → 0 ≤ t → ∀ p : PhaseSpace,
      evolution c (s + t) p = evolution c t (evolution c s p)) ∧
    (∀ t : ℝ, 0 ≤ t → ContDiff ℝ 1 (evolution c t)) ∧
    (∀ t : ℝ, 0 ≤ t → ∀ p : PhaseSpace,
      Function.Bijective (fderiv ℝ (evolution c t) p)) ∧
    IsGlobalAttractor c attractor ∧
    (∀ p : PhaseSpace,
      divergence c p = 4 - c - 6 * (radiusSq₁ p - 1) ^ 2 -
        6 * (radiusSq₂ p - 1) ^ 2 ∧ divergence c p ≤ 4 - c ∧ 4 - c < 0) ∧
    (4 < 4 + 4 / c ∧ 4 + 4 / c < 5) ∧
    (∀ t : ℝ, 0 < t →
      IsGreatest (finiteTimeDimension c t '' attractor) (4 + 4 / c) ∧
      {p ∈ attractor | finiteTimeDimension c t p = 4 + 4 / c} = torus) ∧
    (∀ p ∈ attractor, ∀ i : Fin 5,
      Tendsto (fun t : ℝ => Real.log
        ((fderiv ℝ (evolution c t) p).toLinearMap.singularValues i) / t)
        atTop (𝓝 (lyapunovExponent c p i))) ∧
    (globalLyapunovDimension c attractor = 4 + 4 / c) ∧
    IsGreatest (asymptoticDimension c '' attractor) (4 + 4 / c) ∧
    ({p ∈ attractor | asymptoticDimension c p = 4 + 4 / c} = torus) ∧
    IsGreatest (asymptoticDimension c '' periodicEquilibriumSet c) 3 ∧
    (∀ t : ℝ, 0 < t →
      IsGreatest (finiteTimeDimension c t '' periodicEquilibriumSet c) 3) ∧
    (∀ (t : ℝ) (p : PhaseSpace), p ∈ torus → evolution c t p ∈ torus) ∧
    (∀ p ∈ torus, ∀ t : ℝ, 0 < t → evolution c t p ≠ p) ∧
    (∀ t θ₁ θ₂ : ℝ, evolution c t (torusPoint θ₁ θ₂) =
      torusPoint (θ₁ + t) (θ₂ + Real.sqrt 2 * t)) ∧
    (∀ p ∈ attractor, Tendsto (fun t : ℝ => finiteTimeDimension c t p)
      atTop (𝓝 (asymptoticDimension c p))) := by
  sorry

theorem example_c_eight :
    globalLyapunovDimension 8 attractor = 9 / 2 ∧
    IsGreatest (asymptoticDimension 8 '' periodicEquilibriumSet 8) 3 ∧
    (∀ t : ℝ, 0 < t →
      IsGreatest (finiteTimeDimension 8 t '' periodicEquilibriumSet 8) 3) := by
  sorry

theorem attractor_lemma (c : ℝ) (hc : 4 < c) :
    (∀ p : PhaseSpace, ∃ f : ℝ → PhaseSpace, f 0 = p ∧
      ∀ t : ℝ, 0 ≤ t → HasDerivAt f (vectorField c (f t)) t) ∧
    attractor.Nonempty ∧ IsCompact attractor ∧
    (∀ t : ℝ, 0 ≤ t → evolution c t '' attractor = attractor) ∧
    (∀ B : Set PhaseSpace, Bornology.IsBounded B → ∀ ε : ℝ, 0 < ε →
      ∃ T : ℝ, 0 ≤ T ∧ ∀ t : ℝ, T ≤ t → ∀ p ∈ B,
        ∃ q ∈ attractor, dist (evolution c t p) q < ε) := by
  sorry

theorem planar_singular_value_lemma (Ω : ℝ) (p : PlanarSpace)
    (t : ℝ) (ht : 0 < t) :
    Finset.univ.val.map (fun i : Fin 2 =>
      (fderiv ℝ (planarEvolution Ω t) p).toLinearMap.singularValues i) =
      {Real.exp (∫ τ in (0 : ℝ)..t, radialRate
          (planarEvolution Ω τ p 0 ^ 2 + planarEvolution Ω τ p 1 ^ 2)),
       Real.exp (∫ τ in (0 : ℝ)..t, tangentialRate
          (planarEvolution Ω τ p 0 ^ 2 + planarEvolution Ω τ p 1 ^ 2))} := by
  sorry

/-!
## Geometric and dynamical consequences
-/

theorem s01_fixed_vector (c : ℝ) (p : PhaseSpace) (k : ℕ)
    (v : ExteriorSpace k) (hv : v ≠ 0) :
    Tendsto (fun t : ℝ => Real.log ‖exteriorEvolution k c t p v‖ / t) atTop
      (𝓝 (exteriorGrowthRate k c p v)) ∧
    limsup (fun t : ℝ => Real.log ‖exteriorEvolution k c t p v‖ / t) atTop =
      exteriorGrowthRate k c p v := by
  sorry

theorem s01_maximal_growth (c : ℝ) (p : PhaseSpace) (k : ℕ) (hk : k ≤ 5) :
    IsGreatest (exteriorGrowthRate k c p '' {v : ExteriorSpace k | ‖v‖ = 1})
      (spectrumPartialSum (lyapunovExponent c p) k) ∧
    IsGreatest (exteriorGrowthRate k c p '' {v : ExteriorSpace k | v ≠ 0})
      (spectrumPartialSum (lyapunovExponent c p) k) := by
  sorry

theorem s01_basis_and_norm (c : ℝ) (p : PhaseSpace) (k : ℕ) :
    (∀ s : ExteriorIndex k, ‖initialExteriorBasisVector k p s‖ = 1 ∧
      exteriorGrowthRate k c p (initialExteriorBasisVector k p s) =
        ∑ j ∈ s.val, factorExponents c p j) ∧
    (∀ t : ℝ, 0 ≤ t → ∀ v : ExteriorSpace k,
      ‖exteriorEvolution k c t p v‖ ^ 2 = ∑ s : ExteriorIndex k,
        (exteriorFactor k (derivativeFactors c t p) s *
          exteriorInitialCoordinates k p v s) ^ 2) := by
  sorry

theorem s02_index_and_sums (c : ℝ) (hc : 4 < c) :
    IsLeast (commonIndexCandidates c) 4 ∧ commonIndex c = 4 ∧
    (∀ p : PhaseSpace, lyapunovExponent c p 4 = -c) ∧
    IsGreatest ((fun p => spectrumPartialSum (lyapunovExponent c p) 4) '' attractor) 4 ∧
    IsGreatest ((fun p => spectrumPartialSum (lyapunovExponent c p) 5) '' attractor) (4-c) ∧
    4-c < 0 := by
  sorry

theorem s02_common_index_dimension (c : ℝ) (hc : 4 < c) :
    (∀ p : PhaseSpace, commonIndexLocalDimension c p =
      4 + spectrumPartialSum (lyapunovExponent c p) 4 / c) ∧
    commonIndexDimension c = 4 + 4/c ∧
    IsGreatest (commonIndexLocalDimension c '' attractor) (4 + 4/c) ∧
    (∀ p ∈ attractor, commonIndexLocalDimension c p = 4 + 4/c ↔ p ∈ torus) := by
  sorry

theorem s03_periodic_common_index (c : ℝ) (hc : 4 < c) :
    IsGreatest (commonIndexLocalDimension c '' periodicEquilibriumSet c) (4-2/c) ∧
    sSup (commonIndexLocalDimension c '' periodicEquilibriumSet c) < commonIndexDimension c ∧
    IsGreatest (asymptoticDimension c '' periodicEquilibriumSet c) 3 ∧
    sSup (asymptoticDimension c '' periodicEquilibriumSet c) <
      sSup (commonIndexLocalDimension c '' periodicEquilibriumSet c) := by
  sorry

theorem s04_exterior_operator_identity (k : ℕ) (hk : k ≤ 5)
    (M : PhaseSpace →ₗ[ℝ] PhaseSpace) :
    ‖exteriorOperator k M‖ = singularValueFunction M k := by
  sorry

theorem s04_global_growth (c : ℝ) (hc : 4 < c) (k : ℕ) (hk : k ≤ 5) :
    (∀ t : ℝ, 0 ≤ t → (integerGrowthValues c k t).Nonempty ∧
      BddAbove (integerGrowthValues c k t) ∧ 0 < supremumSingularProduct c k t) ∧
    globalLogGrowth c k 0 = 0 ∧
    (∀ s t : ℝ, 0 ≤ s → 0 ≤ t →
      globalLogGrowth c k (s+t) ≤ globalLogGrowth c k s + globalLogGrowth c k t) ∧
    0 ≤ (k : ℝ) * c ∧
    (∀ t : ℝ, 0 ≤ t → |globalLogGrowth c k t| ≤ ((k : ℝ) * c) * t) := by
  sorry

theorem s05_real_time_limit (c : ℝ) (hc : 4 < c) (k : ℕ) (hk : k ≤ 5) :
    Tendsto (fun t : ℝ => globalLogGrowth c k t / t) atTop
      (𝓝 (globalGrowthRate c k)) ∧
    globalGrowthRate c k = sInf ((fun T : ℝ => globalLogGrowth c k T / T) '' Ioi 0) := by
  sorry

theorem s06_exact_global_rates (c : ℝ) (hc : 4 < c) :
    (∀ t : ℝ, 0 ≤ t → globalLogGrowth c 4 t = 4*t ∧
      globalLogGrowth c 5 t = (4-c)*t) ∧
    globalGrowthRate c 0 = 0 ∧
    (∀ k : ℕ, k ≤ 4 → 0 ≤ globalGrowthRate c k) ∧
    globalGrowthRate c 4 = 4 ∧ globalGrowthRate c 5 = 4-c ∧ globalGrowthRate c 5 < 0 := by
  sorry

theorem s06_global_interpolation (c : ℝ) (hc : 4 < c) :
    (∀ k : ℕ, k ≤ 5 → globalGrowthInterpolation c k = globalGrowthRate c k) ∧
    (∀ k : ℕ, k < 5 → ∀ α : ℝ, 0 ≤ α → α ≤ 1 →
      globalGrowthInterpolation c ((k : ℝ)+α) =
        (1-α)*globalGrowthRate c k + α*globalGrowthRate c (k+1)) ∧
    kaplanYorkeIndex (globalGrowthIncrements c) = 4 ∧
    IsGreatest {d : ℝ | d ∈ Icc 0 5 ∧ 0 ≤ globalGrowthInterpolation c d} (4+4/c) ∧
    globalGrowthDimension c = 4 + globalGrowthRate c 4 /
      (globalGrowthRate c 4 - globalGrowthRate c 5) ∧
    globalGrowthDimension c = 4+4/c := by
  sorry

theorem s07_hausdorff_dimensions :
    dimH attractor = 4 ∧ dimH torus = 2 := by
  sorry

theorem s07_torus_directions (c : ℝ) (hc : 4 < c) (p : PhaseSpace) (hp : p ∈ torus) :
    (fun i => radialOrthonormalBasis p i) =
      ![!₂[p 0, p 1, 0, 0, 0], !₂[-p 1, p 0, 0, 0, 0],
        !₂[0, 0, p 2, p 3, 0], !₂[0, 0, -p 3, p 2, 0], !₂[0, 0, 0, 0, 1]] ∧
    (∀ t : ℝ, 0 ≤ t → ∀ i : Fin 5,
      ‖fderiv ℝ (evolution c t) p (radialOrthonormalBasis p i)‖ =
        Real.exp ((![2, 0, 2, 0, -c] : Fin 5 → ℝ) i*t)) ∧
    (∀ i : Fin 5, Tendsto (fun t : ℝ => Real.log
      ‖fderiv ℝ (evolution c t) p (radialOrthonormalBasis p i)‖ / t) atTop
      (𝓝 ((![2, 0, 2, 0, -c] : Fin 5 → ℝ) i))) ∧
    lyapunovExponent c p = ![2, 2, 0, 0, -c] ∧ 0 < (2 : ℝ) ∧ -c < 0 := by
  sorry

theorem s07_dimension_comparison (c : ℝ) (hc : 4 < c) :
    (dimH attractor).toReal < globalLyapunovDimension c attractor ∧
    (∀ t : ℝ, 0 < t → ∀ p ∈ torus,
      (dimH torus).toReal < finiteTimeDimension c t p) := by
  sorry

theorem s08_radial_regions (c : ℝ) :
    innerRadialRegion.Nonempty ∧ outerRadialRegion.Nonempty ∧
    Disjoint innerRadialRegion outerRadialRegion ∧
    IsOpen {p : attractor | (p : PhaseSpace) ∈ innerRadialRegion} ∧
    IsOpen {p : attractor | (p : PhaseSpace) ∈ outerRadialRegion} ∧
    (∀ t : ℝ, 0 ≤ t → evolution c t '' innerRadialRegion = innerRadialRegion ∧
      evolution c t '' outerRadialRegion = outerRadialRegion ∧
      evolution c t '' unitRadialLevel = unitRadialLevel) := by
  sorry

theorem s08_failure_of_transitivity (c : ℝ) :
    (∀ p : PhaseSpace, ¬ attractor ⊆ closure (forwardOrbit c p)) ∧
    ¬ (∀ U V : Set attractor, IsOpen U → IsOpen V → U.Nonempty → V.Nonempty →
      ∃ (t : ℝ) (ht : 0 ≤ t) (p : attractor), p ∈ U ∧ attractorEvolution c ht p ∈ V) := by
  sorry

theorem s09_recurrent_aperiodic_torus (c : ℝ) (p : torus) :
    (∀ U : Set torus, U ∈ 𝓝 p → ∀ R : ℝ, 0 < R →
      ∃ t : ℝ, R < t ∧ torusEvolution c t p ∈ U) ∧
    (∀ t : ℝ, 0 < t → torusEvolution c t p ≠ p) := by
  sorry

theorem s10_frequency_flow (c ν : ℝ) :
    (∀ p : PhaseSpace, frequencyEvolution c ν 0 p = p ∧
      ∀ t : ℝ, 0 ≤ t → HasDerivAt (fun τ => frequencyEvolution c ν τ p)
        (frequencyVectorField c ν (frequencyEvolution c ν t p)) t) ∧
    (∀ (p : PhaseSpace) (f : ℝ → PhaseSpace), ContinuousOn f (Ici 0) →
      (∀ t : ℝ, 0 ≤ t → HasDerivWithinAt f
        (frequencyVectorField c ν (f t)) (Ici t) t) →
      f 0 = p → EqOn f (fun t => frequencyEvolution c ν t p) (Ici 0)) ∧
    (∀ s t : ℝ, 0 ≤ s → 0 ≤ t → ∀ p : PhaseSpace,
      frequencyEvolution c ν (s+t) p = frequencyEvolution c ν t (frequencyEvolution c ν s p)) ∧
    (∀ t : ℝ, 0 ≤ t → ContDiff ℝ 1 (frequencyEvolution c ν t)) ∧
    frequencyVectorField c (Real.sqrt 2) = vectorField c ∧
    (∀ t : ℝ, frequencyEvolution c (Real.sqrt 2) t = evolution c t) := by
  sorry

theorem s10_radial_and_singular_values (c ν : ℝ) (t : ℝ) (ht : 0 ≤ t) (p : PhaseSpace) :
    radiusSq₁ (frequencyEvolution c ν t p) = squaredRadiusEvolution t (radiusSq₁ p) ∧
    radiusSq₂ (frequencyEvolution c ν t p) = squaredRadiusEvolution t (radiusSq₂ p) ∧
    frequencyEvolution c ν t p 4 = Real.exp (-c*t)*p 4 ∧
    (fderiv ℝ (frequencyEvolution c ν t) p).toLinearMap.singularValues =
      (fderiv ℝ (evolution c t) p).toLinearMap.singularValues ∧
    Finset.univ.val.map (fun i : Fin 5 =>
      (fderiv ℝ (frequencyEvolution c ν t) p).toLinearMap.singularValues i) =
      Finset.univ.val.map (fun i : Fin 5 => derivativeFactors c t p i) ∧
    Function.Bijective (fderiv ℝ (frequencyEvolution c ν t) p) := by
  sorry

theorem s10_attractor (c : ℝ) (hc : 4 < c) (ν : ℝ) :
    IsFrequencyGlobalAttractor c ν attractor ∧
    (∀ t : ℝ, ∀ p ∈ torus, frequencyEvolution c ν t p ∈ torus) ∧
    (∀ C : Set PhaseSpace, IsClosed C →
      FrequencyUniformlyAttractsBounded c ν C → attractor ⊆ C) := by
  sorry

theorem s10_dimensions_unchanged (c ν : ℝ) :
    (∀ t : ℝ, 0 ≤ t → ∀ p : PhaseSpace,
      frequencyFiniteTimeDimension c ν t p = finiteTimeDimension c t p) ∧
    (∀ K : Set PhaseSpace,
      frequencyGlobalLyapunovDimension c ν K = globalLyapunovDimension c K) ∧
    (∀ p : PhaseSpace, ∀ i : Fin 5,
      frequencyLyapunovExponent c ν p i = lyapunovExponent c p i ∧
      Tendsto (fun t : ℝ => Real.log
        ((fderiv ℝ (frequencyEvolution c ν t) p).toLinearMap.singularValues i) / t)
        atTop (𝓝 (frequencyLyapunovExponent c ν p i))) ∧
    (∀ p : PhaseSpace, frequencyAsymptoticDimension c ν p = asymptoticDimension c p) := by
  sorry

theorem s10_maximising_torus (c : ℝ) (hc : 4 < c) (ν : ℝ) :
    (∀ t : ℝ, 0 < t →
      IsGreatest (frequencyFiniteTimeDimension c ν t '' attractor) (4+4/c) ∧
      ∀ p ∈ attractor, frequencyFiniteTimeDimension c ν t p = 4+4/c ↔ p ∈ torus) ∧
    IsGreatest (frequencyAsymptoticDimension c ν '' attractor) (4+4/c) ∧
    (∀ p ∈ attractor, frequencyAsymptoticDimension c ν p = 4+4/c ↔ p ∈ torus) ∧
    frequencyGlobalLyapunovDimension c ν attractor = 4+4/c ∧
    (∀ p ∈ attractor, Tendsto (fun t : ℝ => frequencyFiniteTimeDimension c ν t p) atTop
      (𝓝 (frequencyAsymptoticDimension c ν p))) := by
  sorry

theorem s10_rational_common_period (c : ℝ) (a b : ℕ) (_ha : 0 < a) (hb : 0 < b)
    (p : PhaseSpace) (hp : p ∈ torus) :
    0 < 2 * Real.pi * b ∧
    Function.Periodic (fun t : ℝ => frequencyEvolution c ((a : ℝ)/(b : ℝ)) t p)
      (2 * Real.pi * b) ∧
    frequencyVectorField c ((a : ℝ)/(b : ℝ)) p ≠ 0 := by
  sorry

theorem s10_rational_periodic_maximum (c : ℝ) (hc : 4 < c) (ν : ℚ) (_hν : 0 < ν) :
    torus ⊆ frequencyPeriodicSet c ν ∧
    (∀ p ∈ torus, 0 < 2 * Real.pi * ν.den ∧
      Function.Periodic (fun t : ℝ => frequencyEvolution c ν t p) (2 * Real.pi * ν.den)) ∧
    IsGreatest (frequencyAsymptoticDimension c ν '' frequencyPeriodicSet c ν) (4+4/c) ∧
    (∀ t : ℝ, 0 < t →
      IsGreatest (frequencyFiniteTimeDimension c ν t '' frequencyPeriodicSet c ν) (4+4/c)) := by
  sorry

theorem s10_arbitrarily_close_periodic_maxima (c : ℝ) (hc : 4 < c) (ε : ℝ) (hε : 0 < ε) :
    ∃ ν : ℚ, 0 < ν ∧ |(ν : ℝ)-Real.sqrt 2| < ε ∧
      IsGreatest (frequencyAsymptoticDimension c ν '' frequencyPeriodicSet c ν) (4+4/c) ∧
      ∀ t : ℝ, 0 < t →
        IsGreatest (frequencyFiniteTimeDimension c ν t '' frequencyPeriodicSet c ν) (4+4/c) := by
  sorry

theorem s11_invariant_unstable_sets (c : ℝ) (K : Set PhaseSpace)
    (hK : K = firstCircle 1 ∨ K = secondCircle 1 ∨ K = torus) :
    (∀ t : ℝ, 0 ≤ t → evolution c t '' K = K) ∧
    (∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 < δ →
      ∃ p ∈ attractor, Metric.infDist p K < δ ∧
        ∃ t : ℝ, 0 ≤ t ∧ ε ≤ Metric.infDist (evolution c t p) K) := by
  sorry

theorem s11_first_circle_in_plane (c : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 < δ →
      ∃ p ∈ attractor ∩ coordinatePlane 0, Metric.infDist p (firstCircle 1) < δ ∧
        ∃ t : ℝ, 0 ≤ t ∧ ε ≤ Metric.infDist (evolution c t p) (firstCircle 1) := by
  sorry

theorem s11_second_circle_in_plane (c : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 < δ →
      ∃ p ∈ attractor ∩ coordinatePlane 1, Metric.infDist p (secondCircle 1) < δ ∧
        ∃ t : ℝ, 0 ≤ t ∧ ε ≤ Metric.infDist (evolution c t p) (secondCircle 1) := by
  sorry

/-!
## Periodic growth and concavity
-/

theorem periodic_global_growth (c : ℝ) (hc : 4 < c) :
    (∀ k : Fin 6, ∀ t : ℝ, 0 ≤ t →
      periodicGlobalLogGrowth c k t = t * (![0, 2, 2, 0, -2, -2 - c] : Fin 6 → ℝ) k) ∧
    (∀ k : Fin 6, Tendsto (fun t : ℝ => periodicGlobalLogGrowth c k t / t)
      atTop (𝓝 ((![0, 2, 2, 0, -2, -2 - c] : Fin 6 → ℝ) k))) ∧
    ((fun k : Fin 6 => periodicGlobalGrowthRate c k) = ![0, 2, 2, 0, -2, -2 - c]) ∧
    (∀ k : ℕ, k < 5 → ∀ α : ℝ, 0 ≤ α → α ≤ 1 →
      periodicGlobalGrowthInterpolation c ((k : ℝ) + α) =
        (1 - α) * periodicGlobalGrowthRate c k + α * periodicGlobalGrowthRate c (k + 1)) := by
  sorry

theorem periodic_global_dimension (c : ℝ) (hc : 4 < c) :
    kaplanYorkeIndex (periodicGlobalGrowthIncrements c) = 3 ∧
    IsGreatest {d : ℝ | d ∈ Icc 0 5 ∧ 0 ≤ periodicGlobalGrowthInterpolation c d} 3 ∧
    periodicGlobalGrowthDimension c = 3 := by
  sorry

theorem concave_interpolants (c : ℝ) (p : PhaseSpace) :
    (∀ t : ℝ, 0 < t → ConcaveOn ℝ (Icc (0 : ℝ) 5) (fun d => Real.log
      (singularValueFunction (fderiv ℝ (evolution c t) p).toLinearMap d) / t)) ∧
    ConcaveOn ℝ (Icc (0 : ℝ) 5) (spectrumInterpolation (lyapunovExponent c p)) := by
  sorry

/-!
## Definitions and basic properties
-/

theorem D01_parameter (c : ℝ) (hc : 4 < c) :
    0 < c ∧ 4 < 4 + 4 / c ∧ 4 + 4 / c < 5 := by
  sorry

theorem D02_euclidean_geometry :
    Module.finrank ℝ PhaseSpace = 5 ∧
    ∀ p : PhaseSpace,
      ‖p‖ ^ 2 = p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2 + p 3 ^ 2 + p 4 ^ 2 := by
  sorry

theorem D03_radii_and_rate (p : PhaseSpace) :
    (radiusSq₁ p = p 0 ^ 2 + p 1 ^ 2) ∧
    (radiusSq₂ p = p 2 ^ 2 + p 3 ^ 2) ∧
    0 ≤ radiusSq₁ p ∧ 0 ≤ radiusSq₂ p ∧
    (‖(⟨p 0, p 1⟩ : ℂ)‖ ^ 2 = radiusSq₁ p) ∧
    (‖(⟨p 2, p 3⟩ : ℂ)‖ ^ 2 = radiusSq₂ p) ∧
    (‖(⟨p 0, p 1⟩ : ℂ)‖ = Real.sqrt (radiusSq₁ p)) ∧
    (‖(⟨p 2, p 3⟩ : ℂ)‖ = Real.sqrt (radiusSq₂ p)) ∧
    0 ≤ Real.sqrt (radiusSq₁ p) ∧ 0 ≤ Real.sqrt (radiusSq₂ p) ∧
    (∀ s : ℝ, q s = -(s - 1) * (s - 2) ∧ q s = -s ^ 2 + 3 * s - 2) ∧
    0 < Real.sqrt 2 := by
  sorry

theorem D04_polynomial_field (c : ℝ) :
    (∀ p : PhaseSpace, vectorField c p =
      !₂[q (radiusSq₁ p) * p 0 - p 1, q (radiusSq₁ p) * p 1 + p 0,
        q (radiusSq₂ p) * p 2 - Real.sqrt 2 * p 3,
        q (radiusSq₂ p) * p 3 + Real.sqrt 2 * p 2, -c * p 4]) ∧
    (∀ (p : PhaseSpace) (i : Fin 5),
      MvPolynomial.eval p (vectorFieldPolynomial c i) = vectorField c p i) ∧
    (∀ i : Fin 5, (vectorFieldPolynomial c i).totalDegree ≤ 5) ∧
    (vectorFieldPolynomial c 0).totalDegree = 5 ∧
    Finset.univ.sup (fun i => (vectorFieldPolynomial c i).totalDegree) = 5 ∧
    (∀ n : WithTop ℕ∞, ContDiff ℝ n (vectorField c)) := by
  sorry

theorem D05_actual_forward_flow (c : ℝ) :
    (∀ p : PhaseSpace, evolution c 0 p = p ∧
      ∀ t : ℝ, 0 ≤ t → HasDerivAt (fun τ => evolution c τ p)
        (vectorField c (evolution c t p)) t) ∧
    (∀ (p : PhaseSpace) (f : ℝ → PhaseSpace),
      ContinuousOn f (Ici 0) →
      (∀ t : ℝ, 0 ≤ t → HasDerivWithinAt f (vectorField c (f t)) (Ici t) t) →
      f 0 = p → EqOn f (fun t => evolution c t p) (Ici 0)) ∧
    (∀ (s t : ℝ), 0 ≤ s → 0 ≤ t → ∀ p : PhaseSpace,
      evolution c (s + t) p = evolution c t (evolution c s p)) ∧
    (∀ (t : ℝ), 0 ≤ t → ∀ n : WithTop ℕ∞, ContDiff ℝ n (evolution c t)) := by
  sorry

theorem D06_attractor_and_torus :
    attractor = {p : PhaseSpace | radiusSq₁ p ≤ 2 ∧ radiusSq₂ p ≤ 2 ∧ p 4 = 0} ∧
    torus = {p : PhaseSpace | radiusSq₁ p = 1 ∧ radiusSq₂ p = 1 ∧ p 4 = 0} ∧
    attractor = {p : PhaseSpace | Real.sqrt (radiusSq₁ p) ≤ Real.sqrt 2 ∧
      Real.sqrt (radiusSq₂ p) ≤ Real.sqrt 2 ∧ p 4 = 0} ∧
    torus = {p : PhaseSpace | Real.sqrt (radiusSq₁ p) = 1 ∧
      Real.sqrt (radiusSq₂ p) = 1 ∧ p 4 = 0} ∧
    attractor.Nonempty ∧ IsCompact attractor ∧
    torus.Nonempty ∧ IsCompact torus ∧ torus ⊆ attractor := by
  sorry

theorem D07_ordered_positive_singular_values (c : ℝ) (t : ℝ) (ht : 0 ≤ t)
    (p : PhaseSpace) :
    Function.Bijective (fderiv ℝ (evolution c t) p) ∧
    Antitone (fun i : Fin 5 =>
      (fderiv ℝ (evolution c t) p).toLinearMap.singularValues i) ∧
    (∀ i : Fin 5, 0 < (fderiv ℝ (evolution c t) p).toLinearMap.singularValues i) ∧
    (Finset.univ.val.map (fun i : Fin 5 =>
      (fderiv ℝ (evolution c t) p).toLinearMap.singularValues i) =
      Finset.univ.val.map (derivativeFactors c t p)) := by
  sorry

theorem D08_singular_value_function (M : PhaseSpace →ₗ[ℝ] PhaseSpace)
    (hM : Function.Injective M) :
    singularValueFunction M 0 = 1 ∧
    (∀ k : ℕ, k < 5 → ∀ α : ℝ, 0 ≤ α → α ≤ 1 →
      singularValueFunction M ((k : ℝ) + α) =
        (∏ i ∈ Finset.range k, M.singularValues i) * M.singularValues k ^ α) ∧
    singularValueFunction M 5 = |M.det| ∧
    ContinuousOn (singularValueFunction M) (Icc 0 5) := by
  sorry

theorem D09_attainment_and_infimum (c : ℝ) (t : ℝ) (ht : 0 ≤ t)
    (p : PhaseSpace) (K : Set PhaseSpace) :
    {d : ℝ | d ∈ Icc 0 5 ∧
      1 ≤ singularValueFunction (fderiv ℝ (evolution c t) p).toLinearMap d}.Nonempty ∧
    IsCompact {d : ℝ | d ∈ Icc 0 5 ∧
      1 ≤ singularValueFunction (fderiv ℝ (evolution c t) p).toLinearMap d} ∧
    IsGreatest {d : ℝ | d ∈ Icc 0 5 ∧
      1 ≤ singularValueFunction (fderiv ℝ (evolution c t) p).toLinearMap d}
      (finiteTimeDimension c t p) ∧
    globalLyapunovDimension c K =
      sInf {v : ℝ | ∃ τ : ℝ, 0 < τ ∧ v = sSup (finiteTimeDimension c τ '' K)} := by
  sorry

theorem D10_kaplan_yorke_convention (a : Fin 5 → ℝ) :
    spectrumPartialSum a 0 = 0 ∧
    kaplanYorkeDimension a ∈ Icc 0 5 ∧
    (∀ k : ℕ, spectrumPartialSum a k = ∑ i ∈ Finset.range k, spectrumEntry a i) ∧
    (kaplanYorkeIndex a ≤ 5 ∧ 0 ≤ spectrumPartialSum a (kaplanYorkeIndex a)) ∧
    (∀ k : ℕ, k ≤ 5 → 0 ≤ spectrumPartialSum a k → k ≤ kaplanYorkeIndex a) ∧
    (kaplanYorkeIndex a = 0 → kaplanYorkeDimension a = 0) ∧
    (kaplanYorkeIndex a = 5 → kaplanYorkeDimension a = 5) ∧
    (0 < kaplanYorkeIndex a → kaplanYorkeIndex a < 5 →
      spectrumEntry a (kaplanYorkeIndex a) < 0 ∧
      kaplanYorkeDimension a = (kaplanYorkeIndex a : ℝ) +
        spectrumPartialSum a (kaplanYorkeIndex a) / |spectrumEntry a (kaplanYorkeIndex a)|) := by
  sorry

theorem D10_actual_exponents (c : ℝ) (p : PhaseSpace) :
    Antitone (lyapunovExponent c p) ∧
    (∀ i : Fin 5, Tendsto (fun t : ℝ => Real.log
      ((fderiv ℝ (evolution c t) p).toLinearMap.singularValues i) / t)
      atTop (𝓝 (lyapunovExponent c p i))) ∧
    asymptoticDimension c p = kaplanYorkeDimension (lyapunovExponent c p) := by
  sorry

theorem D10_finite_time_convention (c : ℝ) (t : ℝ) (ht : 0 < t)
    (p : PhaseSpace) :
    {d : ℝ | d ∈ Icc 0 5 ∧
      1 ≤ singularValueFunction (fderiv ℝ (evolution c t) p).toLinearMap d} =
      Icc 0 (kaplanYorkeDimension (normalizedLogSingularValues c t p)) ∧
    finiteTimeDimension c t p =
      kaplanYorkeDimension (normalizedLogSingularValues c t p) := by
  sorry

theorem D06_torus_angle_coordinates :
    (∀ θ₁ θ₂ : ℝ, torusPoint θ₁ θ₂ ∈ torus) ∧
    (∀ p ∈ torus, ∃ θ₁ θ₂ : ℝ, torusPoint θ₁ θ₂ = p) ∧
    (∀ θ₁ θ₂ : ℝ, torusPoint (θ₁ + 2 * Real.pi) θ₂ = torusPoint θ₁ θ₂) ∧
    (∀ θ₁ θ₂ : ℝ, torusPoint θ₁ (θ₂ + 2 * Real.pi) = torusPoint θ₁ θ₂) := by
  sorry

theorem D11_periodic_union_and_orbits (c : ℝ) (hc : 0 < c) :
    periodicEquilibriumSet c = attractor ∩
      ({p : PhaseSpace | vectorField c p = 0} ∪
       {p : PhaseSpace | ∃ τ : ℝ, 0 < τ ∧ evolution c τ p = p}) ∧
    periodicEquilibriumSet c =
      {p : PhaseSpace | p ∈ attractor ∧ ∃ τ : ℝ, 0 < τ ∧ evolution c τ p = p} ∧
    geometricPeriodicOrbits c =
      {O : Set PhaseSpace | ∃ p : PhaseSpace,
        (∃ τ : ℝ, 0 < τ ∧ evolution c τ p = p) ∧ vectorField c p ≠ 0 ∧
        {z : PhaseSpace | ∃ τ : ℝ, 0 ≤ τ ∧ evolution c τ p = z} = O} ∧
    geometricPeriodicOrbits c =
      {firstCircle 1, firstCircle 2, secondCircle 1, secondCircle 2} ∧
    (geometricPeriodicOrbits c).encard = 4 := by
  sorry

/-!
## Dynamics
-/

theorem p01_hasDerivAt_radiusEvolution :
    ∀ {t r : ℝ} (ht : 0 ≤ t) (hr : 0 ≤ r),
    HasDerivAt (fun τ => radiusEvolution τ r) (radialField (radiusEvolution t r)) t := by
  sorry

theorem p01_exists_planar_angular_lift :
    ∀ (Ω x y : ℝ) (hxy : x ^ 2 + y ^ 2 ≠ 0),
    ∃ θ : ℝ,
      (∀ t : ℝ, HasDerivAt (fun τ => θ + Ω * τ) Ω t) ∧
      ∀ t : ℝ, 0 ≤ t →
        0 < radiusEvolution t (Real.sqrt (x ^ 2 + y ^ 2)) ∧
        planarX Ω t x y = radiusEvolution t (Real.sqrt (x ^ 2 + y ^ 2)) *
          Real.cos (θ + Ω * t) ∧
        planarY Ω t x y = radiusEvolution t (Real.sqrt (x ^ 2 + y ^ 2)) *
          Real.sin (θ + Ω * t) := by
  sorry

theorem p01_planarX_origin :
    ∀ (Ω t : ℝ),
    planarX Ω t 0 0 = 0 := by
  sorry

theorem p01_planarY_origin :
    ∀ (Ω t : ℝ),
    planarY Ω t 0 0 = 0 := by
  sorry

theorem p01_radius₁_evolution :
    ∀ (c : ℝ) {t : ℝ} (ht : 0 ≤ t) (p : PhaseSpace),
    Real.sqrt (radiusSq₁ (evolution c t p)) = radiusEvolution t (Real.sqrt (radiusSq₁ p)) := by
  sorry

theorem p01_radius₂_evolution :
    ∀ (c : ℝ) {t : ℝ} (ht : 0 ≤ t) (p : PhaseSpace),
    Real.sqrt (radiusSq₂ (evolution c t p)) = radiusEvolution t (Real.sqrt (radiusSq₂ p)) := by
  sorry

theorem p02_radialField_eq_zero_iff :
    ∀ {r : ℝ} (hr : 0 ≤ r),
    radialField r = 0 ↔ r = 0 ∨ r = 1 ∨ r = Real.sqrt 2 := by
  sorry

theorem p02_radialField_neg_below_one :
    ∀ {r : ℝ} (hr : 0 < r) (hr₁ : r < 1),
    radialField r < 0 := by
  sorry

theorem p02_radialField_pos_between :
    ∀ {r : ℝ} (hr₁ : 1 < r) (hr₂ : r < Real.sqrt 2),
    radialField r > 0 := by
  sorry

theorem p02_radialField_neg_above :
    ∀ {r : ℝ} (hr : Real.sqrt 2 < r),
    radialField r < 0 := by
  sorry

theorem p02_strictMono_squaredRadiusEvolution :
    ∀ {t : ℝ} (ht : 0 ≤ t),
    StrictMono (squaredRadiusEvolution t) := by
  sorry

theorem p02_radiusEvolution_mono :
    ∀ {t r R : ℝ} (ht : 0 ≤ t) (hr : 0 ≤ r) (hrR : r ≤ R),
    radiusEvolution t r ≤ radiusEvolution t R := by
  sorry

theorem p02_squaredRadiusEvolution_pos_iff :
    ∀ {t s : ℝ} (ht : 0 ≤ t),
    0 < squaredRadiusEvolution t s ↔ 0 < s := by
  sorry

theorem p02_squaredRadiusEvolution_lt_one_iff :
    ∀ {t s : ℝ} (ht : 0 ≤ t),
    squaredRadiusEvolution t s < 1 ↔ s < 1 := by
  sorry

theorem p02_one_lt_squaredRadiusEvolution_iff :
    ∀ {t s : ℝ} (ht : 0 ≤ t),
    1 < squaredRadiusEvolution t s ↔ 1 < s := by
  sorry

theorem p02_squaredRadiusEvolution_lt_two_iff :
    ∀ {t s : ℝ} (ht : 0 ≤ t),
    squaredRadiusEvolution t s < 2 ↔ s < 2 := by
  sorry

theorem p02_two_lt_squaredRadiusEvolution_iff :
    ∀ {t s : ℝ} (ht : 0 ≤ t),
    2 < squaredRadiusEvolution t s ↔ 2 < s := by
  sorry

theorem p02_squaredRadiusEvolution_eq_self_iff :
    ∀ {t s : ℝ} (ht : 0 < t),
    squaredRadiusEvolution t s = s ↔ s = 0 ∨ s = 1 ∨ s = 2 := by
  sorry

theorem p03_radiusEvolution_zero_time :
    ∀ {r : ℝ} (hr : 0 ≤ r),
    radiusEvolution 0 r = r := by
  sorry

theorem p03_radiusEvolution_nonneg :
    ∀ (t r : ℝ),
    0 ≤ radiusEvolution t r := by
  sorry

theorem p03_radiusEvolution_le_max :
    ∀ {t r : ℝ} (ht : 0 ≤ t) (hr : 0 ≤ r),
    radiusEvolution t r ≤ max r (Real.sqrt 2) := by
  sorry

theorem p03_radiusEvolution_at_zero :
    ∀ (t : ℝ),
    radiusEvolution t 0 = 0 := by
  sorry

theorem p03_radiusEvolution_at_one :
    ∀ (t : ℝ),
    radiusEvolution t 1 = 1 := by
  sorry

theorem p03_radiusEvolution_at_sqrt_two :
    ∀ (t : ℝ),
    radiusEvolution t (Real.sqrt 2) = Real.sqrt 2 := by
  sorry

theorem p03_tendsto_radiusEvolution_of_lt_one :
    ∀ {r : ℝ} (hr : 0 ≤ r) (hr₁ : r < 1),
    Tendsto (fun t => radiusEvolution t r) atTop (𝓝 0) := by
  sorry

theorem p03_tendsto_radiusEvolution_of_one_lt :
    ∀ {r : ℝ} (hr : 1 < r),
    Tendsto (fun t => radiusEvolution t r) atTop (𝓝 (Real.sqrt 2)) := by
  sorry

theorem p03_tendsto_radiusEvolution_one_iff :
    ∀ {r : ℝ} (hr : 0 ≤ r),
    Tendsto (fun t => radiusEvolution t r) atTop (𝓝 1) ↔ r = 1 := by
  sorry

theorem p04_abs_fifth_evolution :
    ∀ (c t : ℝ) (p : PhaseSpace),
    |evolution c t p 4| = Real.exp (-c * t) * |p 4| := by
  sorry

theorem p04_isBounded_evolution_image_interval :
    ∀ (c T : ℝ) (p : PhaseSpace),
    Bornology.IsBounded ((fun t => evolution c t p) '' Icc 0 T) := by
  sorry

theorem p04_exists_global_forward_solution :
    ∀ (c : ℝ) (p : PhaseSpace),
    ∃ f : ℝ → PhaseSpace, f 0 = p ∧
      ∀ t, 0 ≤ t → HasDerivAt f (vectorField c (f t)) t := by
  sorry

theorem p05_exists_complete_solution_in_attractor :
    ∀ (c : ℝ) {p : PhaseSpace} (hp : p ∈ attractor),
    ∃ f : ℝ → PhaseSpace, f 0 = p ∧ ∀ t : ℝ,
      f t ∈ attractor ∧ HasDerivAt f (vectorField c (f t)) t := by
  sorry

theorem p05_hasDerivAt_evolution_of_mem_attractor :
    ∀ (c t : ℝ) {p : PhaseSpace}
    (hp : p ∈ attractor),
    HasDerivAt (fun τ => evolution c τ p) (vectorField c (evolution c t p)) t := by
  sorry

theorem p05_evolution_mem_attractor_all_time :
    ∀ (c t : ℝ) {p : PhaseSpace} (hp : p ∈ attractor),
    evolution c t p ∈ attractor := by
  sorry

theorem p05_radiusEvolution_mem_lower_interval :
    ∀ (t : ℝ) {r : ℝ} (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1),
    radiusEvolution t r ∈ Set.Icc 0 1 := by
  sorry

theorem p05_radiusEvolution_mem_upper_interval :
    ∀ (t : ℝ) {r : ℝ}
    (hr₁ : 1 ≤ r) (hr₂ : r ≤ Real.sqrt 2),
    radiusEvolution t r ∈ Set.Icc 1 (Real.sqrt 2) := by
  sorry

theorem p05_evolution_image_attractor :
    ∀ (c : ℝ) {t : ℝ} (ht : 0 ≤ t),
    evolution c t '' attractor = attractor := by
  sorry

theorem p06_bounded_set_radius_bounds :
    ∀ {B : Set PhaseSpace} (hB : Bornology.IsBounded B),
    ∃ M W : ℝ, Real.sqrt 2 < M ∧ 0 ≤ W ∧ ∀ p ∈ B,
      Real.sqrt (radiusSq₁ p) ≤ M ∧ Real.sqrt (radiusSq₂ p) ≤ M ∧ |p 4| ≤ W := by
  sorry

theorem p06_radial_excess_le :
    ∀ {t r M : ℝ} (ht : 0 ≤ t) (hr : 0 ≤ r)
    (hrM : r ≤ M) (hM : Real.sqrt 2 ≤ M),
    max (radiusEvolution t r - Real.sqrt 2) 0 ≤ radiusEvolution t M - Real.sqrt 2 := by
  sorry

theorem p06_radiusEvolution_antitoneOn :
    ∀ {R : ℝ} (hR : Real.sqrt 2 ≤ R),
    AntitoneOn (fun t => radiusEvolution t R) (Ici 0) := by
  sorry

theorem p06_infDist_evolution_attractor_sq_le :
    ∀ (c : ℝ) {M W t : ℝ} (ht : 0 ≤ t)
    (hM : Real.sqrt 2 ≤ M) {p : PhaseSpace}
    (h₁ : Real.sqrt (radiusSq₁ p) ≤ M) (h₂ : Real.sqrt (radiusSq₂ p) ≤ M)
    (hw : |p 4| ≤ W),
    Metric.infDist (evolution c t p) attractor ^ 2 ≤ attractionBound c M W t := by
  sorry

theorem p06_tendsto_attractionBound :
    ∀ {c M : ℝ} (hc : 0 < c) (hM : Real.sqrt 2 < M) (W : ℝ),
    Tendsto (fun t => attractionBound c M W t) atTop (𝓝 0) := by
  sorry

theorem p07_attractor_minimal :
    ∀ {c : ℝ} {C : Set PhaseSpace} (hcompact : IsCompact C)
    (hC : UniformlyAttractsBounded c C),
    attractor ⊆ C := by
  sorry

theorem p07_empty_not_uniformlyAttractsBounded :
    ∀ (c : ℝ),
    ¬UniformlyAttractsBounded c (∅ : Set PhaseSpace) := by
  sorry

theorem p08_deriv_q :
    ∀ (s : ℝ),
    deriv q s = -2 * s + 3 := by
  sorry

theorem p08_radialRate_eq_q_add_deriv :
    ∀ (s : ℝ),
    radialRate s = q s + 2 * s * deriv q s := by
  sorry

theorem p08_tangentialRate_eq_q :
    ∀ (s : ℝ),
    tangentialRate s = q s := by
  sorry

theorem p08_q_expansion :
    ∀ (s : ℝ),
    q s = -s ^ 2 + 3 * s - 2 := by
  sorry

theorem p09_toMatrix_fderiv_planarVectorField :
    ∀ (Ω : ℝ) (p : PlanarSpace),
    (fderiv ℝ (planarVectorField Ω) p).toLinearMap.toMatrix
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis =
      q (p 0 ^ 2 + p 1 ^ 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        (2 * deriv q (p 0 ^ 2 + p 1 ^ 2)) •
          Matrix.vecMulVec (fun i => p i) (fun i => p i) +
        Ω • !![0, -1; 1, 0] := by
  sorry

theorem p10_fderiv_planarEvolution_orthogonal_decomposition :
    ∀ (Ω : ℝ) {t : ℝ}
    (ht : 0 ≤ t) (p : PlanarSpace),
    (fderiv ℝ (planarEvolution Ω t) p).toLinearMap =
      ((planarRadialFrame p).trans (planarAngularRotation Ω t)).toLinearMap ∘ₗ
        planarDiagonal (planarFactors t p) ∘ₗ (planarRadialFrame p).symm.toLinearMap := by
  sorry

theorem p10_planarMovingPerturbation_zero_time :
    ∀ (Ω : ℝ) (p v : PlanarSpace),
    planarMovingPerturbation Ω 0 p v = v := by
  sorry

theorem p10_hasDerivAt_planarMovingPerturbation :
    ∀ (Ω : ℝ) {t : ℝ} (ht : 0 < t)
    (p v : PlanarSpace),
    HasDerivAt (fun τ => planarMovingPerturbation Ω τ p v)
      (!₂[radialRate (planarEvolution Ω t p 0 ^ 2 + planarEvolution Ω t p 1 ^ 2) *
          planarMovingPerturbation Ω t p v 0,
        tangentialRate (planarEvolution Ω t p 0 ^ 2 + planarEvolution Ω t p 1 ^ 2) *
          planarMovingPerturbation Ω t p v 1]) t := by
  sorry

theorem p10_hasDerivWithinAt_planarMovingPerturbation :
    ∀ (Ω : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (p v : PlanarSpace),
    HasDerivWithinAt (fun τ => planarMovingPerturbation Ω τ p v)
      (!₂[radialRate (planarEvolution Ω t p 0 ^ 2 + planarEvolution Ω t p 1 ^ 2) *
          planarMovingPerturbation Ω t p v 0,
        tangentialRate (planarEvolution Ω t p 0 ^ 2 + planarEvolution Ω t p 1 ^ 2) *
          planarMovingPerturbation Ω t p v 1]) (Set.Ici 0) t := by
  sorry

theorem p10_radialAmplitude_eq_exp_integral :
    ∀ {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s),
    radialAmplitude t s =
      Real.exp (∫ τ in (0 : ℝ)..t, radialRate (squaredRadiusEvolution τ s)) := by
  sorry

theorem p10_planarAmplitude_eq_exp_integral :
    ∀ {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s),
    planarAmplitude t s =
      Real.exp (∫ τ in (0 : ℝ)..t, tangentialRate (squaredRadiusEvolution τ s)) := by
  sorry

theorem p11_fderiv_planarEvolution_origin :
    ∀ (Ω : ℝ) {t : ℝ} (ht : 0 ≤ t) (v : PlanarSpace),
    fderiv ℝ (planarEvolution Ω t) 0 v =
      Real.exp (-2 * t) • planarAngularRotation Ω t v := by
  sorry

theorem p11_rates_at_stationary_radii :
    radialRate 0 = -2 ∧ tangentialRate 0 = -2 ∧
    radialRate 1 = 2 ∧ tangentialRate 1 = 0 ∧
    radialRate 2 = -4 ∧ tangentialRate 2 = 0 := by
  sorry

theorem p24_equilibriumSet_eq_singleton :
    ∀ {c : ℝ} (hc : c ≠ 0),
    equilibriumSet c = {0} := by
  sorry

theorem p24_singularValues_at_origin :
    ∀ {c t : ℝ} (hc : 2 ≤ c) (ht : 0 ≤ t),
    (fun i : Fin 5 => (fderiv ℝ (evolution c t) 0).toLinearMap.singularValues i) =
      ![Real.exp (-2 * t), Real.exp (-2 * t), Real.exp (-2 * t),
        Real.exp (-2 * t), Real.exp (-c * t)] := by
  sorry

theorem p24_finiteTimeDimension_at_origin :
    ∀ {c t : ℝ} (hc : 4 < c) (ht : 0 < t),
    finiteTimeDimension c t 0 = 0 := by
  sorry

theorem p24_asymptoticDimension_at_origin :
    ∀ {c : ℝ} (hc : 4 < c),
    asymptoticDimension c 0 = 0 := by
  sorry

theorem p25_stationary_radii_of_evolution_return :
    ∀ (c : ℝ) {t : ℝ} (ht : 0 < t)
    {p : PhaseSpace} (h : evolution c t p = p),
    (radiusSq₁ p = 0 ∨ radiusSq₁ p = 1 ∨ radiusSq₁ p = 2) ∧
    (radiusSq₂ p = 0 ∨ radiusSq₂ p = 1 ∨ radiusSq₂ p = 2) := by
  sorry

theorem p25_fifth_eq_zero_of_evolution_return :
    ∀ {c t : ℝ} (hc : 0 < c) (ht : 0 < t)
    {p : PhaseSpace} (h : evolution c t p = p),
    p 4 = 0 := by
  sorry

theorem p25_not_simultaneous_rotation_returns :
    ∀ {t : ℝ} (ht : 0 < t),
    ¬(Real.cos t = 1 ∧ Real.cos (Real.sqrt 2 * t) = 1) := by
  sorry

theorem p25_one_radius_zero_of_evolution_return :
    ∀ (c : ℝ) {t : ℝ} (ht : 0 < t)
    {p : PhaseSpace} (h : evolution c t p = p),
    radiusSq₁ p = 0 ∨ radiusSq₂ p = 0 := by
  sorry

theorem p25_mem_positiveReturnSet_iff :
    ∀ {c : ℝ} (hc : 0 < c) (p : PhaseSpace),
    p ∈ positiveReturnSet c ↔ p = 0 ∨ p ∈ firstCircle 1 ∨ p ∈ firstCircle 2 ∨
      p ∈ secondCircle 1 ∨ p ∈ secondCircle 2 := by
  sorry

theorem p26_geometricPeriodicOrbits_eq :
    ∀ {c : ℝ} (hc : 0 < c),
    geometricPeriodicOrbits c = {firstCircle 1, firstCircle 2, secondCircle 1, secondCircle 2} := by
  sorry

theorem p26_geometricPeriodicOrbits_encard :
    ∀ {c : ℝ} (hc : 0 < c),
    (geometricPeriodicOrbits c).encard = 4 := by
  sorry

theorem p26_forwardOrbit_eq_firstCircle :
    ∀ (c : ℝ) {s : ℝ} (hs : s = 1 ∨ s = 2)
    {p : PhaseSpace} (hp : p ∈ firstCircle s),
    forwardOrbit c p = firstCircle s := by
  sorry

theorem p26_forwardOrbit_eq_secondCircle :
    ∀ (c : ℝ) {s : ℝ} (hs : s = 1 ∨ s = 2)
    {p : PhaseSpace} (hp : p ∈ secondCircle s),
    forwardOrbit c p = secondCircle s := by
  sorry

theorem p26_first_plane_return :
    ∀ (c : ℝ) {p : PhaseSpace}
    (h₁ : radiusSq₁ p = 1 ∨ radiusSq₁ p = 2)
    (h₂ : radiusSq₂ p = 0) (hw : p 4 = 0),
    evolution c (2 * Real.pi) p = p := by
  sorry

theorem p26_second_plane_return :
    ∀ (c : ℝ) {p : PhaseSpace}
    (h₁ : radiusSq₁ p = 0) (h₂ : radiusSq₂ p = 1 ∨ radiusSq₂ p = 2)
    (hw : p 4 = 0),
    evolution c (2 * Real.pi / Real.sqrt 2) p = p := by
  sorry

theorem p26_normalizedLogSingularValues_unit_circle :
    ∀ {c t : ℝ} (hc : 4 < c)
    (ht : 0 < t) {p : PhaseSpace} (hp : p ∈ firstCircle 1 ∨ p ∈ secondCircle 1),
    normalizedLogSingularValues c t p = ![2, 0, -2, -2, -c] := by
  sorry

theorem p26_normalizedLogSingularValues_outer_circle :
    ∀ {c t : ℝ} (hc : 4 < c)
    (ht : 0 < t) {p : PhaseSpace} (hp : p ∈ firstCircle 2 ∨ p ∈ secondCircle 2),
    normalizedLogSingularValues c t p = ![0, -2, -2, -4, -c] := by
  sorry

theorem p26_finiteTimeDimension_eq_asymptotic_on_periodic :
    ∀ {c t : ℝ} (hc : 0 < c)
    (ht : 0 < t) {p : PhaseSpace} (hp : p ∈ periodicEquilibriumSet c),
    finiteTimeDimension c t p = asymptoticDimension c p := by
  sorry

theorem p26_asymptoticDimension_first_unit_circle :
    ∀ {c : ℝ} (hc : 4 < c)
    {p : PhaseSpace} (hp : p ∈ firstCircle 1),
    asymptoticDimension c p = 3 := by
  sorry

theorem p26_asymptoticDimension_second_unit_circle :
    ∀ {c : ℝ} (hc : 4 < c)
    {p : PhaseSpace} (hp : p ∈ secondCircle 1),
    asymptoticDimension c p = 3 := by
  sorry

theorem p26_asymptoticDimension_first_outer_circle :
    ∀ {c : ℝ} (hc : 4 < c)
    {p : PhaseSpace} (hp : p ∈ firstCircle 2),
    asymptoticDimension c p = 1 := by
  sorry

theorem p26_asymptoticDimension_second_outer_circle :
    ∀ {c : ℝ} (hc : 4 < c)
    {p : PhaseSpace} (hp : p ∈ secondCircle 2),
    asymptoticDimension c p = 1 := by
  sorry

theorem p27_log_singularValueFunction_div_time :
    ∀ (c : ℝ) {t : ℝ} (ht : 0 < t)
    (p : PhaseSpace) (d : ℝ),
    Real.log (singularValueFunction (fderiv ℝ (evolution c t) p).toLinearMap d) / t =
      spectrumInterpolation (normalizedLogSingularValues c t p) d := by
  sorry

theorem p27_tendstoUniformlyOn_log_singularValueFunction :
    ∀ (c : ℝ) (p : PhaseSpace),
    TendstoUniformlyOn (fun t d => Real.log
      (singularValueFunction (fderiv ℝ (evolution c t) p).toLinearMap d) / t)
      (spectrumInterpolation (lyapunovExponent c p)) atTop (Icc 0 5) := by
  sorry

theorem p28_eventually_dimension_zero_of_limiting_radii :
    ∀ {c : ℝ} (hc : 4 < c)
    (p : PhaseSpace) (h₁ : limitingSquaredRadius (radiusSq₁ p) = 0)
    (h₂ : limitingSquaredRadius (radiusSq₂ p) = 0),
    ∀ᶠ t in atTop, (∀ i, normalizedLogSingularValues c t p i < 0) ∧
      finiteTimeDimension c t p = 0 := by
  sorry

theorem p28_finiteTimeDimension_of_limiting_unit_radii :
    ∀ {c t : ℝ} (hc : 4 < c)
    (ht : 0 < t) {p : PhaseSpace} (hp : p ∈ attractor)
    (h₁ : limitingSquaredRadius (radiusSq₁ p) = 1)
    (h₂ : limitingSquaredRadius (radiusSq₂ p) = 1),
    finiteTimeDimension c t p = targetDimension c := by
  sorry

theorem p29_tangentialRate_along_nonneg :
    ∀ {s t : ℝ} (hs₁ : 1 ≤ s) (hs₂ : s ≤ 2)
    (ht : 0 ≤ t),
    0 ≤ tangentialRate (squaredRadiusEvolution t s) := by
  sorry

theorem p29_eventually_dimension_formula_zero_two :
    ∀ {c : ℝ} (hc : 4 < c)
    {p : PhaseSpace} (hp : p ∈ attractor)
    (hpair : (limitingSquaredRadius (radiusSq₁ p) = 0 ∧
        limitingSquaredRadius (radiusSq₂ p) = 2) ∨
      (limitingSquaredRadius (radiusSq₁ p) = 2 ∧
        limitingSquaredRadius (radiusSq₂ p) = 0)),
    ∀ᶠ t in atTop, 0 ≤ normalizedLogSingularValues c t p 0 ∧
      spectrumPartialSum (normalizedLogSingularValues c t p) 2 < 0 ∧
      normalizedLogSingularValues c t p 1 < 0 ∧
      finiteTimeDimension c t p = 1 +
        spectrumPartialSum (normalizedLogSingularValues c t p) 1 /
          -normalizedLogSingularValues c t p 1 := by
  sorry

theorem p29_eventually_dimension_formula_two_two :
    ∀ {c : ℝ} (hc : 4 < c)
    {p : PhaseSpace} (hp : p ∈ attractor)
    (h₁ : limitingSquaredRadius (radiusSq₁ p) = 2)
    (h₂ : limitingSquaredRadius (radiusSq₂ p) = 2),
    ∀ᶠ t in atTop,
      (∀ i : Fin 5, i.val < 2 → 0 ≤ normalizedLogSingularValues c t p i) ∧
      spectrumPartialSum (normalizedLogSingularValues c t p) 3 < 0 ∧
      normalizedLogSingularValues c t p 2 < 0 ∧
      finiteTimeDimension c t p = 2 +
        spectrumPartialSum (normalizedLogSingularValues c t p) 2 /
          -normalizedLogSingularValues c t p 2 := by
  sorry

theorem p01_fifth_coordinate (c t : ℝ) (p : PhaseSpace) :
    evolution c t p 4 = Real.exp (-c*t)*p 4 := by
  sorry

theorem p26_unit_circle_dimensions (c : ℝ) (hc : 4 < c) (t : ℝ) (ht : 0 < t)
    (p : PhaseSpace) (hp : p ∈ firstCircle 1 ∨ p ∈ secondCircle 1) :
    finiteTimeDimension c t p = 3 ∧ asymptoticDimension c p = 3 := by
  sorry

theorem p26_outer_circle_dimensions (c : ℝ) (hc : 4 < c) (t : ℝ) (ht : 0 < t)
    (p : PhaseSpace) (hp : p ∈ firstCircle 2 ∨ p ∈ secondCircle 2) :
    finiteTimeDimension c t p = 1 ∧ asymptoticDimension c p = 1 := by
  sorry

theorem p28_zero_one_root_and_convergence (c : ℝ) (hc : 4 < c)
    (p : PhaseSpace) (hp : p ∈ attractor)
    (hpair : (limitingSquaredRadius (radiusSq₁ p) = 0 ∧ limitingSquaredRadius (radiusSq₂ p) = 1) ∨
      (limitingSquaredRadius (radiusSq₁ p) = 1 ∧ limitingSquaredRadius (radiusSq₂ p) = 0)) :
    (∀ d : ℝ, d ∈ Ioo 0 3 → 0 < spectrumInterpolation (lyapunovExponent c p) d) ∧
    spectrumInterpolation (lyapunovExponent c p) 3 = 0 ∧
    (∀ d : ℝ, d ∈ Ioc 3 5 → spectrumInterpolation (lyapunovExponent c p) d < 0) ∧
    Tendsto (fun t : ℝ => finiteTimeDimension c t p) atTop (𝓝 3) := by
  sorry

theorem p28_one_two_root_and_convergence (c : ℝ) (hc : 4 < c)
    (p : PhaseSpace) (hp : p ∈ attractor)
    (hpair : (limitingSquaredRadius (radiusSq₁ p) = 1 ∧ limitingSquaredRadius (radiusSq₂ p) = 2) ∨
      (limitingSquaredRadius (radiusSq₁ p) = 2 ∧ limitingSquaredRadius (radiusSq₂ p) = 1)) :
    (∀ d : ℝ, d ∈ Ioo 0 (7/2) → 0 < spectrumInterpolation (lyapunovExponent c p) d) ∧
    spectrumInterpolation (lyapunovExponent c p) (7/2) = 0 ∧
    (∀ d : ℝ, d ∈ Ioc (7/2) 5 → spectrumInterpolation (lyapunovExponent c p) d < 0) ∧
    Tendsto (fun t : ℝ => finiteTimeDimension c t p) atTop (𝓝 (7/2)) := by
  sorry

theorem p29_zero_two_limits (c : ℝ) (hc : 4 < c) (p : PhaseSpace) (hp : p ∈ attractor)
    (hpair : (limitingSquaredRadius (radiusSq₁ p) = 0 ∧ limitingSquaredRadius (radiusSq₂ p) = 2) ∨
      (limitingSquaredRadius (radiusSq₁ p) = 2 ∧ limitingSquaredRadius (radiusSq₂ p) = 0)) :
    Tendsto (fun t : ℝ => normalizedLogSingularValues c t p 0) atTop (𝓝 0) ∧
    Tendsto (fun t : ℝ => normalizedLogSingularValues c t p 1) atTop (𝓝 (-2)) ∧
    Tendsto (fun t : ℝ => finiteTimeDimension c t p) atTop (𝓝 1) := by
  sorry

theorem p29_two_two_limits (c : ℝ) (hc : 4 < c) (p : PhaseSpace) (hp : p ∈ attractor)
    (h₁ : limitingSquaredRadius (radiusSq₁ p) = 2)
    (h₂ : limitingSquaredRadius (radiusSq₂ p) = 2) :
    (∀ i : Fin 5, i.val < 2 →
      Tendsto (fun t : ℝ => normalizedLogSingularValues c t p i) atTop (𝓝 0)) ∧
    Tendsto (fun t : ℝ => normalizedLogSingularValues c t p 2) atTop (𝓝 (-4)) ∧
    Tendsto (fun t : ℝ => finiteTimeDimension c t p) atTop (𝓝 2) := by
  sorry

theorem p28_zero_zero_limit (c : ℝ) (hc : 4 < c) (p : PhaseSpace) (hp : p ∈ attractor)
    (h₁ : limitingSquaredRadius (radiusSq₁ p) = 0)
    (h₂ : limitingSquaredRadius (radiusSq₂ p) = 0) :
    Tendsto (fun t : ℝ => finiteTimeDimension c t p) atTop (𝓝 0) := by
  sorry

theorem p28_unit_unit_limit (c : ℝ) (hc : 4 < c) (p : PhaseSpace) (hp : p ∈ attractor)
    (h₁ : limitingSquaredRadius (radiusSq₁ p) = 1)
    (h₂ : limitingSquaredRadius (radiusSq₂ p) = 1) :
    Tendsto (fun t : ℝ => finiteTimeDimension c t p) atTop (𝓝 (4+4/c)) := by
  sorry

/-!
## Spectral properties
-/

theorem p13_fderiv_evolution_apply :
    ∀ (c : ℝ) {t : ℝ} (ht : 0 ≤ t) (p v : PhaseSpace),
    fderiv ℝ (evolution c t) p v =
      !₂[planarDerivativeX 1 t (p 0) (p 1) (v 0) (v 1),
         planarDerivativeY 1 t (p 0) (p 1) (v 0) (v 1),
         planarDerivativeX (Real.sqrt 2) t (p 2) (p 3) (v 2) (v 3),
         planarDerivativeY (Real.sqrt 2) t (p 2) (p 3) (v 2) (v 3),
         Real.exp (-c * t) * v 4] := by
  sorry

theorem p13_fderiv_evolution_radialFrame :
    ∀ (c : ℝ) {t : ℝ} (ht : 0 ≤ t) (p v : PhaseSpace),
    fderiv ℝ (evolution c t) p (radialFrame p v) =
      angularRotation t (radialFrame p (diagonalLinear (derivativeFactors c t p) v)) := by
  sorry

theorem p13_fderiv_evolution_orthogonal_decomposition :
    ∀ (c : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (p : PhaseSpace),
    (fderiv ℝ (evolution c t) p).toLinearMap =
      (angularRotation t).toLinearEquiv.toLinearMap ∘ₗ
        (radialFrame p).toLinearEquiv.toLinearMap ∘ₗ
          diagonalLinear (derivativeFactors c t p) ∘ₗ
            (radialFrame p).symm.toLinearEquiv.toLinearMap := by
  sorry

theorem p13_derivativeFactors_pos :
    ∀ (c : ℝ) {t : ℝ} (ht : 0 ≤ t) (p : PhaseSpace) (i : Fin 5),
    0 < derivativeFactors c t p i := by
  sorry

theorem p13_singularValues_fderiv_evolution :
    ∀ (c : ℝ) {t : ℝ} (ht : 0 ≤ t) (p : PhaseSpace),
    Finset.univ.val.map (fun i : Fin 5 => (fderiv ℝ (evolution c t) p).toLinearMap.singularValues i) =
      Finset.univ.val.map (fun i : Fin 5 => derivativeFactors c t p i) := by
  sorry

theorem p13_log_planarAmplitude_eq_integral :
    ∀ {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s),
    Real.log (planarAmplitude t s) =
      ∫ τ in (0 : ℝ)..t, tangentialRate (squaredRadiusEvolution τ s) := by
  sorry

theorem p13_log_radialAmplitude_eq_integral :
    ∀ {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s),
    Real.log (radialAmplitude t s) =
      ∫ τ in (0 : ℝ)..t, radialRate (squaredRadiusEvolution τ s) := by
  sorry

theorem p13_planarAmplitude_eq_exp_integral :
    ∀ {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s),
    planarAmplitude t s =
      Real.exp (∫ τ in (0 : ℝ)..t, tangentialRate (squaredRadiusEvolution τ s)) := by
  sorry

theorem p13_radialAmplitude_eq_exp_integral :
    ∀ {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s),
    radialAmplitude t s =
      Real.exp (∫ τ in (0 : ℝ)..t, radialRate (squaredRadiusEvolution τ s)) := by
  sorry

theorem p14_radialRate_add_four :
    ∀ (s : ℝ),
    radialRate s + 4 = (2 - s) * (5 * s + 1) := by
  sorry

theorem p14_tangentialRate_add_two :
    ∀ (s : ℝ),
    tangentialRate s + 2 = s * (3 - s) := by
  sorry

theorem p14_rates_sum :
    ∀ (s : ℝ),
    radialRate s + tangentialRate s = 2 - 6 * (s - 1) ^ 2 := by
  sorry

theorem p15_radialRate_lower_bound :
    ∀ {s : ℝ} (hs₀ : 0 ≤ s) (hs₂ : s ≤ 2),
    -4 ≤ radialRate s := by
  sorry

theorem p15_tangentialRate_lower_bound :
    ∀ {s : ℝ} (hs₀ : 0 ≤ s) (hs₂ : s ≤ 2),
    -2 ≤ tangentialRate s := by
  sorry

theorem p16_radiusSq₁_evolution :
    ∀ (c : ℝ) {t : ℝ} (ht : 0 ≤ t) (p : PhaseSpace),
    radiusSq₁ (evolution c t p) = squaredRadiusEvolution t (radiusSq₁ p) := by
  sorry

theorem p16_radiusSq₂_evolution :
    ∀ (c : ℝ) {t : ℝ} (ht : 0 ≤ t) (p : PhaseSpace),
    radiusSq₂ (evolution c t p) = squaredRadiusEvolution t (radiusSq₂ p) := by
  sorry

theorem p16_evolution_mem_attractor :
    ∀ (c : ℝ) {t : ℝ} (ht : 0 ≤ t)
    {p : PhaseSpace} (hp : p ∈ attractor),
    evolution c t p ∈ attractor := by
  sorry

theorem p16_derivativeFactors_planar_lower_bound :
    ∀ (c : ℝ) {t : ℝ} (ht : 0 ≤ t)
    {p : PhaseSpace} (hp : p ∈ attractor) (i : Fin 4),
    Real.exp (-4 * t) ≤ derivativeFactors c t p i.castSucc := by
  sorry

theorem p16_exp_fifth_lt_planar_bound :
    ∀ {c t : ℝ} (hc : 4 < c) (ht : 0 < t),
    Real.exp (-c * t) < Real.exp (-4 * t) := by
  sorry

theorem p16_derivativeFactors_fifth_lt_planar :
    ∀ {c t : ℝ} (hc : 4 < c) (ht : 0 < t)
    {p : PhaseSpace} (hp : p ∈ attractor) (i : Fin 4),
    derivativeFactors c t p 4 < derivativeFactors c t p i.castSucc := by
  sorry

theorem p16_singularValues_fderiv_evolution_fifth :
    ∀ {c t : ℝ} (hc : 4 ≤ c) (ht : 0 ≤ t)
    {p : PhaseSpace} (hp : p ∈ attractor),
    (fderiv ℝ (evolution c t) p).toLinearMap.singularValues 4 = Real.exp (-c * t) := by
  sorry

theorem p17_volumeDefect_eq_integral_evolution :
    ∀ (c : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (p : PhaseSpace),
    volumeDefect t p = ∫ τ in (0 : ℝ)..t,
      ((radiusSq₁ (evolution c τ p) - 1) ^ 2 +
        (radiusSq₂ (evolution c τ p) - 1) ^ 2) := by
  sorry

theorem p17_continuousOn_volumeDefect_integrand :
    ∀ (c : ℝ) (p : PhaseSpace),
    ContinuousOn (fun τ => (radiusSq₁ (evolution c τ p) - 1) ^ 2 +
      (radiusSq₂ (evolution c τ p) - 1) ^ 2) (Set.Ici 0) := by
  sorry

theorem p17_volumeDefect_integrand_nonneg :
    ∀ (c τ : ℝ) (p : PhaseSpace),
    0 ≤ (radiusSq₁ (evolution c τ p) - 1) ^ 2 +
      (radiusSq₂ (evolution c τ p) - 1) ^ 2 := by
  sorry

theorem p17_volumeDefect_nonneg :
    ∀ {t : ℝ} (ht : 0 ≤ t) (p : PhaseSpace),
    0 ≤ volumeDefect t p := by
  sorry

theorem p17_log_singularValues_fderiv_evolution_prod_four :
    ∀ {c t : ℝ}
    (hc : 4 ≤ c) (ht : 0 ≤ t) {p : PhaseSpace} (hp : p ∈ attractor),
    Real.log (∏ i : Fin 4, (fderiv ℝ (evolution c t) p).toLinearMap.singularValues i) =
      4 * t - 6 * volumeDefect t p := by
  sorry

theorem p17_singularValues_fderiv_evolution_prod_four :
    ∀ {c t : ℝ} (hc : 4 ≤ c) (ht : 0 ≤ t)
    {p : PhaseSpace} (hp : p ∈ attractor),
    (∏ i : Fin 4, (fderiv ℝ (evolution c t) p).toLinearMap.singularValues i) =
      Real.exp (4 * t - 6 * volumeDefect t p) := by
  sorry

theorem p18_volumeDefect_eq_zero_iff :
    ∀ {t : ℝ} (ht : 0 < t)
    {p : PhaseSpace} (hp : p ∈ attractor),
    volumeDefect t p = 0 ↔ p ∈ torus := by
  sorry

theorem p18_singularValues_fderiv_evolution_prod_four_le :
    ∀ {c t : ℝ}
    (hc : 4 ≤ c) (ht : 0 ≤ t) {p : PhaseSpace} (hp : p ∈ attractor),
    (∏ i : Fin 4, (fderiv ℝ (evolution c t) p).toLinearMap.singularValues i) ≤
      Real.exp (4 * t) := by
  sorry

theorem p18_singularValues_fderiv_evolution_prod_four_eq_iff :
    ∀ {c t : ℝ}
    (hc : 4 ≤ c) (ht : 0 < t) {p : PhaseSpace} (hp : p ∈ attractor),
    (∏ i : Fin 4, (fderiv ℝ (evolution c t) p).toLinearMap.singularValues i) =
      Real.exp (4 * t) ↔ p ∈ torus := by
  sorry

theorem p19_singularValueFunction_evolution_on_four_five :
    ∀ {c t d : ℝ}
    (hc : 4 ≤ c) (ht : 0 ≤ t) {p : PhaseSpace} (hp : p ∈ attractor)
    (hd₄ : 4 ≤ d) (hd₅ : d ≤ 5),
    singularValueFunction (fderiv ℝ (evolution c t) p).toLinearMap d =
      Real.exp (4 * t - 6 * volumeDefect t p - c * t * (d - 4)) := by
  sorry

theorem p19_singularValueFunction_evolution_at_target :
    ∀ {c t : ℝ}
    (hc : 4 < c) (ht : 0 ≤ t) {p : PhaseSpace} (hp : p ∈ attractor),
    singularValueFunction (fderiv ℝ (evolution c t) p).toLinearMap (targetDimension c) =
      Real.exp (-6 * volumeDefect t p) := by
  sorry

theorem p19_singularValueFunction_evolution_above_target :
    ∀ {c t d : ℝ}
    (hc : 4 < c) (ht : 0 < t) {p : PhaseSpace} (hp : p ∈ attractor)
    (hd : targetDimension c < d) (hd₅ : d ≤ 5),
    singularValueFunction (fderiv ℝ (evolution c t) p).toLinearMap d =
      Real.exp (-6 * volumeDefect t p - c * t * (d - targetDimension c)) := by
  sorry

theorem p19_singularValueFunction_evolution_above_target_lt_one :
    ∀ {c t d : ℝ}
    (hc : 4 < c) (ht : 0 < t) {p : PhaseSpace} (hp : p ∈ attractor)
    (hd : targetDimension c < d) (hd₅ : d ≤ 5),
    singularValueFunction (fderiv ℝ (evolution c t) p).toLinearMap d < 1 := by
  sorry

theorem p19_finiteTimeDimension_le_target :
    ∀ {c t : ℝ} (hc : 4 < c) (ht : 0 < t)
    {p : PhaseSpace} (hp : p ∈ attractor),
    finiteTimeDimension c t p ≤ targetDimension c := by
  sorry

theorem p20_singularValues_on_torus :
    ∀ {c t : ℝ} (hc : 0 ≤ c) (ht : 0 ≤ t)
    {p : PhaseSpace} (hp : p ∈ torus),
    (fun i : Fin 5 => (fderiv ℝ (evolution c t) p).toLinearMap.singularValues i) =
      ![Real.exp (2 * t), Real.exp (2 * t), 1, 1, Real.exp (-c * t)] := by
  sorry

theorem p20_finiteTimeDimension_eq_target_iff :
    ∀ {c t : ℝ} (hc : 4 < c) (ht : 0 < t)
    {p : PhaseSpace} (hp : p ∈ attractor),
    finiteTimeDimension c t p = targetDimension c ↔ p ∈ torus := by
  sorry

theorem p20_finiteTimeDimension_attractor_isGreatest :
    ∀ {c t : ℝ} (hc : 4 < c) (ht : 0 < t),
    IsGreatest (finiteTimeDimension c t '' attractor) (targetDimension c) := by
  sorry

theorem p21_tendsto_radialRate_average :
    ∀ {s : ℝ} (hs : 0 ≤ s),
    Tendsto (fun t => (∫ τ in (0 : ℝ)..t,
      radialRate (squaredRadiusEvolution τ s)) / t) atTop
      (𝓝 (radialRate (limitingSquaredRadius s))) := by
  sorry

theorem p21_tendsto_tangentialRate_average :
    ∀ {s : ℝ} (hs : 0 ≤ s),
    Tendsto (fun t => (∫ τ in (0 : ℝ)..t,
      tangentialRate (squaredRadiusEvolution τ s)) / t) atTop
      (𝓝 (tangentialRate (limitingSquaredRadius s))) := by
  sorry

theorem p21_limiting_rates_of_lt_one :
    ∀ {s : ℝ} (hs : s < 1),
    radialRate (limitingSquaredRadius s) = -2 ∧
      tangentialRate (limitingSquaredRadius s) = -2 := by
  sorry

theorem p21_limiting_rates_at_one :
    radialRate (limitingSquaredRadius 1) = 2 ∧
      tangentialRate (limitingSquaredRadius 1) = 0 := by
  sorry

theorem p21_limiting_rates_of_one_lt :
    ∀ {s : ℝ} (hs : 1 < s),
    radialRate (limitingSquaredRadius s) = -4 ∧
      tangentialRate (limitingSquaredRadius s) = 0 := by
  sorry

theorem p21_tendsto_log_derivativeFactors_div :
    ∀ (c : ℝ) (p : PhaseSpace) (i : Fin 5),
    Tendsto (fun t => Real.log (derivativeFactors c t p i) / t) atTop
      (𝓝 (factorExponents c p i)) := by
  sorry

theorem p22_lipschitzWith_descending :
    ∀ (n : ℕ),
    LipschitzWith 1 (descending : (Fin n → ℝ) → (Fin n → ℝ)) := by
  sorry

theorem p22_normalizedLogSingularValues_eq_descending :
    ∀ (c : ℝ) {t : ℝ} (ht : 0 < t)
    (p : PhaseSpace),
    normalizedLogSingularValues c t p =
      descending (fun i => Real.log (derivativeFactors c t p i) / t) := by
  sorry

theorem p22_tendsto_normalizedLogSingularValues :
    ∀ (c : ℝ) (p : PhaseSpace),
    Tendsto (fun t => normalizedLogSingularValues c t p) atTop
      (𝓝 (descending (factorExponents c p))) := by
  sorry

theorem p22_lyapunovExponent_eq_descending :
    ∀ (c : ℝ) (p : PhaseSpace) (i : Fin 5),
    lyapunovExponent c p i = descending (factorExponents c p) i := by
  sorry

theorem p22_tendsto_lyapunovExponent :
    ∀ (c : ℝ) (p : PhaseSpace) (i : Fin 5),
    Tendsto (fun t => Real.log
      ((fderiv ℝ (evolution c t) p).toLinearMap.singularValues i) / t) atTop
      (𝓝 (lyapunovExponent c p i)) := by
  sorry

theorem p22_lyapunovExponent_eq_radiusPairSpectrum :
    ∀ (c : ℝ) (p : PhaseSpace),
    lyapunovExponent c p = descending (radiusPairSpectrum c
      (limitingSquaredRadius (radiusSq₁ p)) (limitingSquaredRadius (radiusSq₂ p))) := by
  sorry

theorem p22_limitingSquaredRadius_cases :
    ∀ (s : ℝ),
    limitingSquaredRadius s = 0 ∨ limitingSquaredRadius s = 1 ∨ limitingSquaredRadius s = 2 := by
  sorry

theorem p22_limitingSquaredRadius_eq_one_iff :
    ∀ (s : ℝ),
    limitingSquaredRadius s = 1 ↔ s = 1 := by
  sorry

theorem p22_descending_radiusPairSpectrum_swap :
    ∀ (c s₁ s₂ : ℝ),
    descending (radiusPairSpectrum c s₁ s₂) = descending (radiusPairSpectrum c s₂ s₁) := by
  sorry

theorem p22_lyapunovExponent_eq_of_limiting_radii :
    ∀ (c : ℝ) (p : PhaseSpace) {s₁ s₂ : ℝ}
    (h : (limitingSquaredRadius (radiusSq₁ p) = s₁ ∧
        limitingSquaredRadius (radiusSq₂ p) = s₂) ∨
      (limitingSquaredRadius (radiusSq₁ p) = s₂ ∧
        limitingSquaredRadius (radiusSq₂ p) = s₁)),
    lyapunovExponent c p = descending (radiusPairSpectrum c s₁ s₂) := by
  sorry

theorem p22_descending_radiusPairSpectrum_zero_zero :
    ∀ {c : ℝ} (hc : 4 < c),
    descending (radiusPairSpectrum c 0 0) = ![-2, -2, -2, -2, -c] := by
  sorry

theorem p22_descending_radiusPairSpectrum_zero_one :
    ∀ {c : ℝ} (hc : 4 < c),
    descending (radiusPairSpectrum c 0 1) = ![2, 0, -2, -2, -c] := by
  sorry

theorem p22_descending_radiusPairSpectrum_zero_two :
    ∀ {c : ℝ} (hc : 4 < c),
    descending (radiusPairSpectrum c 0 2) = ![0, -2, -2, -4, -c] := by
  sorry

theorem p22_descending_radiusPairSpectrum_one_one :
    ∀ {c : ℝ} (hc : 4 < c),
    descending (radiusPairSpectrum c 1 1) = ![2, 2, 0, 0, -c] := by
  sorry

theorem p22_descending_radiusPairSpectrum_one_two :
    ∀ {c : ℝ} (hc : 4 < c),
    descending (radiusPairSpectrum c 1 2) = ![2, 0, 0, -4, -c] := by
  sorry

theorem p22_descending_radiusPairSpectrum_two_two :
    ∀ {c : ℝ} (hc : 4 < c),
    descending (radiusPairSpectrum c 2 2) = ![0, 0, -4, -4, -c] := by
  sorry

theorem p22_kaplanYorkeDimension_zero_zero :
    ∀ {c : ℝ} (hc : 4 < c),
    kaplanYorkeDimension ![-2, -2, -2, -2, -c] = 0 := by
  sorry

theorem p22_kaplanYorkeDimension_zero_one :
    ∀ {c : ℝ} (hc : 4 < c),
    kaplanYorkeDimension ![2, 0, -2, -2, -c] = 3 := by
  sorry

theorem p22_kaplanYorkeDimension_zero_two :
    ∀ {c : ℝ} (hc : 4 < c),
    kaplanYorkeDimension ![0, -2, -2, -4, -c] = 1 := by
  sorry

theorem p22_kaplanYorkeDimension_one_one :
    ∀ {c : ℝ} (hc : 4 < c),
    kaplanYorkeDimension ![2, 2, 0, 0, -c] = targetDimension c := by
  sorry

theorem p22_kaplanYorkeDimension_one_two :
    ∀ {c : ℝ} (hc : 4 < c),
    kaplanYorkeDimension ![2, 0, 0, -4, -c] = 7 / 2 := by
  sorry

theorem p22_kaplanYorkeDimension_two_two :
    ∀ {c : ℝ} (hc : 4 < c),
    kaplanYorkeDimension ![0, 0, -4, -4, -c] = 2 := by
  sorry

theorem p23_kaplanYorkeDimension_radiusPair_bound_and_eq :
    ∀ {c s₁ s₂ : ℝ} (hc : 4 < c)
    (hs₁ : s₁ = 0 ∨ s₁ = 1 ∨ s₁ = 2) (hs₂ : s₂ = 0 ∨ s₂ = 1 ∨ s₂ = 2),
    kaplanYorkeDimension (descending (radiusPairSpectrum c s₁ s₂)) ≤ targetDimension c ∧
      (kaplanYorkeDimension (descending (radiusPairSpectrum c s₁ s₂)) = targetDimension c ↔
        s₁ = 1 ∧ s₂ = 1) := by
  sorry

theorem p23_asymptoticDimension_le_target :
    ∀ {c : ℝ} (hc : 4 < c) (p : PhaseSpace),
    asymptoticDimension c p ≤ targetDimension c := by
  sorry

theorem p23_asymptoticDimension_eq_target_iff_radii :
    ∀ {c : ℝ} (hc : 4 < c) (p : PhaseSpace),
    asymptoticDimension c p = targetDimension c ↔ radiusSq₁ p = 1 ∧ radiusSq₂ p = 1 := by
  sorry

theorem p23_asymptoticDimension_eq_target_iff :
    ∀ {c : ℝ} (hc : 4 < c) {p : PhaseSpace}
    (hp : p ∈ attractor),
    asymptoticDimension c p = targetDimension c ↔ p ∈ torus := by
  sorry

theorem p23_asymptoticDimension_lt_target_of_not_mem_torus :
    ∀ {c : ℝ} (hc : 4 < c)
    {p : PhaseSpace} (hp : p ∈ attractor) (hT : p ∉ torus),
    asymptoticDimension c p < targetDimension c := by
  sorry

theorem s04_fderiv_evolution_add :
    ∀ (c : ℝ) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    (p : PhaseSpace),
    fderiv ℝ (evolution c (s + t)) p =
      (fderiv ℝ (evolution c t) (evolution c s p)).comp (fderiv ℝ (evolution c s) p) := by
  sorry

theorem s04_exteriorOperator_comp :
    ∀ (k : ℕ) (A B : PhaseSpace →ₗ[ℝ] PhaseSpace),
    exteriorOperator k (A ∘ₗ B) = (exteriorOperator k A).comp (exteriorOperator k B) := by
  sorry

theorem s04_singularValueFunction_integer_comp_le :
    ∀ {k : ℕ} (hk : k ≤ 5)
    (A B : PhaseSpace →ₗ[ℝ] PhaseSpace),
    singularValueFunction (A ∘ₗ B) k ≤ singularValueFunction A k * singularValueFunction B k := by
  sorry

theorem p18_zero_defect_entire_interval (c : ℝ) {t : ℝ} (ht : 0 < t)
    {p : PhaseSpace} (hp : p ∈ attractor) :
    volumeDefect t p = 0 ↔ ∀ τ ∈ Icc (0 : ℝ) t,
      radiusSq₁ (evolution c τ p) = 1 ∧ radiusSq₂ (evolution c τ p) = 1 := by
  sorry

theorem p16_radius_domain (c : ℝ) {p : PhaseSpace} (hp : p ∈ attractor)
    {t : ℝ} (ht : 0 ≤ t) : ∀ τ ∈ Icc (0 : ℝ) t,
      radiusSq₁ (evolution c τ p) ∈ Icc (0 : ℝ) 2 ∧
      radiusSq₂ (evolution c τ p) ∈ Icc (0 : ℝ) 2 := by
  sorry

end EdenVerified
