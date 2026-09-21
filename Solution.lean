import Eden

/-!
# Formal results for the Eden counterexample

Theorems for the polynomial flow, its attractor and Lyapunov dimensions,
followed by the geometric, dynamical and spectral results of the paper. Time is
real and the ambient space carries the Euclidean norm.
-/

noncomputable section
open Set Filter
open scoped Topology
open Eden

namespace EdenVerified

/-!
## Main results
-/

/-- The joint main theorem, including the ambient ODE and its uniqueness. All time
variables are real; all derivatives use the ambient Euclidean norm. -/
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
  refine ⟨?_, ?_, ?_, ?_, ?_, attractor_isGlobalAttractor (by linarith), ?_,
    targetDimension_bounds hc, ?_, ?_, globalLyapunovDimension_attractor hc,
    asymptoticDimension_attractor_isGreatest hc, ?_,
    asymptoticDimension_periodic_isGreatest hc, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun p => ⟨evolution_zero_time c p, fun t ht => hasDerivAt_evolution c ht p⟩
  · exact fun p f hf hf' h0 => evolution_unique c p hf hf' h0
  · exact fun s t hs ht p => evolution_add c hs ht p
  · exact fun t ht => contDiff_evolution c ht 1
  · exact fun t ht p => fderiv_evolution_bijective c ht p
  · exact fun p => ⟨divergence_eq c p, divergence_le c p, by linarith⟩
  · intro t ht
    refine ⟨finiteTimeDimension_attractor_isGreatest hc ht, ?_⟩
    ext p
    constructor
    · exact fun hp => (finiteTimeDimension_eq_target_iff hc ht hp.1).mp hp.2
    · exact fun hp => ⟨torus_subset_attractor hp,
        (finiteTimeDimension_eq_target_iff hc ht (torus_subset_attractor hp)).mpr hp⟩
  · exact fun p _ i => tendsto_lyapunovExponent c p i
  · ext p
    constructor
    · exact fun hp => (asymptoticDimension_eq_target_iff hc hp.1).mp hp.2
    · exact fun hp => ⟨torus_subset_attractor hp,
        (asymptoticDimension_eq_target_iff hc (torus_subset_attractor hp)).mpr hp⟩
  · exact fun t ht => finiteTimeDimension_periodic_isGreatest hc ht
  · exact fun t p hp => torus_invariant_all_real c t hp
  · exact fun p hp t ht => torus_no_positive_return c hp ht
  · exact evolution_torusPoint c
  · exact fun p hp => tendsto_finiteTimeDimension hc hp

/-- The numerical example immediately following the main theorem. -/
theorem example_c_eight :
    globalLyapunovDimension 8 attractor = 9 / 2 ∧
    IsGreatest (asymptoticDimension 8 '' periodicEquilibriumSet 8) 3 ∧
    (∀ t : ℝ, 0 < t →
      IsGreatest (finiteTimeDimension 8 t '' periodicEquilibriumSet 8) 3) :=
  ⟨globalLyapunovDimension_attractor_eight,
    asymptoticDimension_periodic_isGreatest (by norm_num),
    fun t ht => finiteTimeDimension_periodic_isGreatest (by norm_num) ht⟩

/-- Manuscript Lemma `lem:attractor`, with the paper's parameter assumption. -/
theorem attractor_lemma (c : ℝ) (hc : 4 < c) :
    (∀ p : PhaseSpace, ∃ f : ℝ → PhaseSpace, f 0 = p ∧
      ∀ t : ℝ, 0 ≤ t → HasDerivAt f (vectorField c (f t)) t) ∧
    attractor.Nonempty ∧ IsCompact attractor ∧
    (∀ t : ℝ, 0 ≤ t → evolution c t '' attractor = attractor) ∧
    (∀ B : Set PhaseSpace, Bornology.IsBounded B → ∀ ε : ℝ, 0 < ε →
      ∃ T : ℝ, 0 ≤ T ∧ ∀ t : ℝ, T ≤ t → ∀ p ∈ B,
        ∃ q ∈ attractor, dist (evolution c t p) q < ε) :=
  ⟨exists_global_forward_solution c, attractor_nonempty, isCompact_attractor,
    fun t ht => evolution_image_attractor c ht,
    attractor_uniformlyAttractsBounded (by linarith)⟩

/-- Manuscript Lemma `lem:sv`: any real angular frequency, every point of the
Euclidean plane, and every positive real time, including zero initial radius. -/
theorem planar_singular_value_lemma (Ω : ℝ) (p : PlanarSpace)
    (t : ℝ) (ht : 0 < t) :
    Finset.univ.val.map (fun i : Fin 2 =>
      (fderiv ℝ (planarEvolution Ω t) p).toLinearMap.singularValues i) =
      {Real.exp (∫ τ in (0 : ℝ)..t, radialRate
          (planarEvolution Ω τ p 0 ^ 2 + planarEvolution Ω τ p 1 ^ 2)),
       Real.exp (∫ τ in (0 : ℝ)..t, tangentialRate
          (planarEvolution Ω τ p 0 ^ 2 + planarEvolution Ω τ p 1 ^ 2))} :=
  singularValues_fderiv_planarEvolution_integrals Ω ht.le p

/-!
## Geometric and dynamical consequences
-/

/-- Ordinary limits for every fixed nonzero exterior vector. -/
theorem s01_fixed_vector (c : ℝ) (p : PhaseSpace) (k : ℕ)
    (v : ExteriorSpace k) (hv : v ≠ 0) :
    Tendsto (fun t : ℝ => Real.log ‖exteriorEvolution k c t p v‖ / t) atTop
      (𝓝 (exteriorGrowthRate k c p v)) ∧
    limsup (fun t : ℝ => Real.log ‖exteriorEvolution k c t p v‖ / t) atTop =
      exteriorGrowthRate k c p v :=
  ⟨tendsto_exteriorGrowthRate c p hv, limsup_exteriorGrowthRate c p hv⟩

/-- Maxima are attained over both unit and nonzero exterior vectors. -/
theorem s01_maximal_growth (c : ℝ) (p : PhaseSpace) (k : ℕ) (hk : k ≤ 5) :
    IsGreatest (exteriorGrowthRate k c p '' {v : ExteriorSpace k | ‖v‖ = 1})
      (spectrumPartialSum (lyapunovExponent c p) k) ∧
    IsGreatest (exteriorGrowthRate k c p '' {v : ExteriorSpace k | v ≠ 0})
      (spectrumPartialSum (lyapunovExponent c p) k) :=
  ⟨isGreatest_exteriorGrowthRate_unit hk c p, isGreatest_exteriorGrowthRate_nonzero hk c p⟩

/-- Growth rates of fixed initial basis wedges. -/
theorem s01_basis_and_norm (c : ℝ) (p : PhaseSpace) (k : ℕ) :
    (∀ s : ExteriorIndex k, ‖initialExteriorBasisVector k p s‖ = 1 ∧
      exteriorGrowthRate k c p (initialExteriorBasisVector k p s) =
        ∑ j ∈ s.val, factorExponents c p j) ∧
    (∀ t : ℝ, 0 ≤ t → ∀ v : ExteriorSpace k,
      ‖exteriorEvolution k c t p v‖ ^ 2 = ∑ s : ExteriorIndex k,
        (exteriorFactor k (derivativeFactors c t p) s *
          exteriorInitialCoordinates k p v s) ^ 2) := by
  constructor
  · intro s
    exact ⟨norm_initialExteriorBasisVector k p s,
      (exteriorGrowthRate_basis k c p s).trans (exteriorRate_eq_sum k c p s)⟩
  · exact fun t ht v => norm_sq_exteriorEvolution k c ht p v

/-- The least global index and the corresponding attained exponent sums. -/
theorem s02_index_and_sums (c : ℝ) (hc : 4 < c) :
    IsLeast (commonIndexCandidates c) 4 ∧ commonIndex c = 4 ∧
    (∀ p : PhaseSpace, lyapunovExponent c p 4 = -c) ∧
    IsGreatest ((fun p => spectrumPartialSum (lyapunovExponent c p) 4) '' attractor) 4 ∧
    IsGreatest ((fun p => spectrumPartialSum (lyapunovExponent c p) 5) '' attractor) (4-c) ∧
    4-c < 0 :=
  ⟨commonIndexCandidates_isLeast hc, commonIndex_eq_four hc, lyapunovExponent_fifth hc,
    exponentSum_four_isGreatest hc, exponentSum_five_isGreatest hc, by linarith⟩

/-- The common-index dimension and its maximising torus. -/
theorem s02_common_index_dimension (c : ℝ) (hc : 4 < c) :
    (∀ p : PhaseSpace, commonIndexLocalDimension c p =
      4 + spectrumPartialSum (lyapunovExponent c p) 4 / c) ∧
    commonIndexDimension c = 4 + 4/c ∧
    IsGreatest (commonIndexLocalDimension c '' attractor) (4 + 4/c) ∧
    (∀ p ∈ attractor, commonIndexLocalDimension c p = 4 + 4/c ↔ p ∈ torus) :=
  ⟨commonIndexLocalDimension_eq hc, commonIndexDimension_eq_target hc,
    commonIndexLocalDimension_isGreatest hc,
    fun p hp => commonIndexLocalDimension_eq_target_iff hc hp⟩

/-- The global index remains fixed when maximisation is restricted to periodic
points. -/
theorem s03_periodic_common_index (c : ℝ) (hc : 4 < c) :
    IsGreatest (commonIndexLocalDimension c '' periodicEquilibriumSet c) (4-2/c) ∧
    sSup (commonIndexLocalDimension c '' periodicEquilibriumSet c) < commonIndexDimension c ∧
    IsGreatest (asymptoticDimension c '' periodicEquilibriumSet c) 3 ∧
    sSup (asymptoticDimension c '' periodicEquilibriumSet c) <
      sSup (commonIndexLocalDimension c '' periodicEquilibriumSet c) :=
  ⟨commonIndexLocalDimension_periodic_isGreatest hc, commonIndex_periodic_gap hc,
    asymptoticDimension_periodic_isGreatest hc, periodic_dimension_conventions_distinct hc⟩

/-- The canonical exterior operator norm, for arbitrary ambient linear maps. -/
theorem s04_exterior_operator_identity (k : ℕ) (hk : k ≤ 5)
    (M : PhaseSpace →ₗ[ℝ] PhaseSpace) :
    ‖exteriorOperator k M‖ = singularValueFunction M k :=
  norm_exteriorOperator_eq_singularValueFunction hk M

/-- Finite spatial suprema, real-time subadditivity and an explicit linear bound. -/
theorem s04_global_growth (c : ℝ) (hc : 4 < c) (k : ℕ) (hk : k ≤ 5) :
    (∀ t : ℝ, 0 ≤ t → (integerGrowthValues c k t).Nonempty ∧
      BddAbove (integerGrowthValues c k t) ∧ 0 < supremumSingularProduct c k t) ∧
    globalLogGrowth c k 0 = 0 ∧
    (∀ s t : ℝ, 0 ≤ s → 0 ≤ t →
      globalLogGrowth c k (s+t) ≤ globalLogGrowth c k s + globalLogGrowth c k t) ∧
    0 ≤ (k : ℝ) * c ∧
    (∀ t : ℝ, 0 ≤ t → |globalLogGrowth c k t| ≤ ((k : ℝ) * c) * t) := by
  refine ⟨?_, globalLogGrowth_zero hk hc.le, ?_, ?_, ?_⟩
  · exact fun t ht => ⟨integerGrowthValues_nonempty c k t,
      integerGrowthValues_bddAbove hk hc.le ht, supremumSingularProduct_pos hk hc.le ht⟩
  · exact fun s t hs ht => globalLogGrowth_subadditive hk hc.le hs ht
  · positivity
  · exact fun t ht => abs_globalLogGrowth_le hk hc.le ht

/-- The limit runs through real time and equals the infimum over all positive real
times. -/
theorem s05_real_time_limit (c : ℝ) (hc : 4 < c) (k : ℕ) (hk : k ≤ 5) :
    Tendsto (fun t : ℝ => globalLogGrowth c k t / t) atTop
      (𝓝 (globalGrowthRate c k)) ∧
    globalGrowthRate c k = sInf ((fun T : ℝ => globalLogGrowth c k T / T) '' Ioi 0) :=
  ⟨tendsto_globalGrowthRate hk hc.le, globalGrowthRate_eq_inf hk hc.le⟩

/-- Exact finite-time fourth/fifth growth and all required signs of their limits. -/
theorem s06_exact_global_rates (c : ℝ) (hc : 4 < c) :
    (∀ t : ℝ, 0 ≤ t → globalLogGrowth c 4 t = 4*t ∧
      globalLogGrowth c 5 t = (4-c)*t) ∧
    globalGrowthRate c 0 = 0 ∧
    (∀ k : ℕ, k ≤ 4 → 0 ≤ globalGrowthRate c k) ∧
    globalGrowthRate c 4 = 4 ∧ globalGrowthRate c 5 = 4-c ∧ globalGrowthRate c 5 < 0 :=
  ⟨fun t ht => ⟨globalLogGrowth_four hc.le ht, globalLogGrowth_five hc.le ht⟩,
    globalGrowthRate_zero hc.le, fun k hk => globalGrowthRate_nonneg hk hc.le,
    globalGrowthRate_four hc.le, globalGrowthRate_five hc.le, globalGrowthRate_five_neg hc⟩

/-- Interpolation uses maximised sums, with all integer endpoints and the attained
root. -/
theorem s06_global_interpolation (c : ℝ) (hc : 4 < c) :
    (∀ k : ℕ, k ≤ 5 → globalGrowthInterpolation c k = globalGrowthRate c k) ∧
    (∀ k : ℕ, k < 5 → ∀ α : ℝ, 0 ≤ α → α ≤ 1 →
      globalGrowthInterpolation c ((k : ℝ)+α) =
        (1-α)*globalGrowthRate c k + α*globalGrowthRate c (k+1)) ∧
    kaplanYorkeIndex (globalGrowthIncrements c) = 4 ∧
    IsGreatest {d : ℝ | d ∈ Icc 0 5 ∧ 0 ≤ globalGrowthInterpolation c d} (4+4/c) ∧
    globalGrowthDimension c = 4 + globalGrowthRate c 4 /
      (globalGrowthRate c 4 - globalGrowthRate c 5) ∧
    globalGrowthDimension c = 4+4/c :=
  ⟨fun k hk => globalGrowthInterpolation_integer hc.le hk,
    fun k hk α hα₀ hα₁ => globalGrowthInterpolation_interpolate hc.le hk hα₀ hα₁,
    globalGrowthIndex_eq_four hc, globalGrowthInterpolation_isGreatest hc,
    globalGrowthDimension_eq_rate_ratio hc, globalGrowthDimension_eq_target hc⟩

/-- Hausdorff dimensions in the ambient Euclidean metric. -/
theorem s07_hausdorff_dimensions :
    dimH attractor = 4 ∧ dimH torus = 2 :=
  ⟨dimH_attractor, dimH_torus⟩

/-- The orthonormal radial/tangential directions, in that order. -/
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
    lyapunovExponent c p = ![2, 2, 0, 0, -c] ∧ 0 < (2 : ℝ) ∧ -c < 0 :=
  ⟨radialOrthonormalBasis_on_torus hp,
    fun t ht i => norm_fderiv_torus_directions c ht hp i,
    tendsto_torus_direction_growth c hp, torus_direction_rates_and_ordered_exponents hc hp⟩

/-- Geometric dimension is strictly smaller than the Lyapunov dimensions here. -/
theorem s07_dimension_comparison (c : ℝ) (hc : 4 < c) :
    (dimH attractor).toReal < globalLyapunovDimension c attractor ∧
    (∀ t : ℝ, 0 < t → ∀ p ∈ torus,
      (dimH torus).toReal < finiteTimeDimension c t p) :=
  ⟨dimH_attractor_lt_globalLyapunovDimension hc,
    fun t ht p hp => dimH_torus_lt_finiteTimeDimension hc ht hp⟩

/-- The nonempty disjoint relatively open regions and their strict invariance. -/
theorem s08_radial_regions (c : ℝ) :
    innerRadialRegion.Nonempty ∧ outerRadialRegion.Nonempty ∧
    Disjoint innerRadialRegion outerRadialRegion ∧
    IsOpen {p : attractor | (p : PhaseSpace) ∈ innerRadialRegion} ∧
    IsOpen {p : attractor | (p : PhaseSpace) ∈ outerRadialRegion} ∧
    (∀ t : ℝ, 0 ≤ t → evolution c t '' innerRadialRegion = innerRadialRegion ∧
      evolution c t '' outerRadialRegion = outerRadialRegion ∧
      evolution c t '' unitRadialLevel = unitRadialLevel) :=
  ⟨innerRadialRegion_nonempty, outerRadialRegion_nonempty, radialRegions_disjoint,
    isOpen_innerRadialRegion, isOpen_outerRadialRegion,
    fun t ht => ⟨evolution_image_innerRadialRegion c ht,
      evolution_image_outerRadialRegion c ht, evolution_image_unitRadialLevel c ht⟩⟩

/-- No dense forward orbit, even from outside A, and no open-set transitivity. -/
theorem s08_failure_of_transitivity (c : ℝ) :
    (∀ p : PhaseSpace, ¬ attractor ⊆ closure (forwardOrbit c p)) ∧
    ¬ (∀ U V : Set attractor, IsOpen U → IsOpen V → U.Nonempty → V.Nonempty →
      ∃ (t : ℝ) (ht : 0 ≤ t) (p : attractor), p ∈ U ∧ attractorEvolution c ht p ∈ V) :=
  ⟨attractor_not_subset_closure_forwardOrbit c, not_openSet_transitive_attractor c⟩

/-- Every point is recurrent in the torus topology, and no point is periodic. -/
theorem s09_recurrent_aperiodic_torus (c : ℝ) (p : torus) :
    (∀ U : Set torus, U ∈ 𝓝 p → ∀ R : ℝ, 0 < R →
      ∃ t : ℝ, R < t ∧ torusEvolution c t p ∈ U) ∧
    (∀ t : ℝ, 0 < t → torusEvolution c t p ≠ p) :=
  ⟨fun U hU R hR => torus_recurrence_nhds c p hU hR,
    fun t ht => torusEvolution_no_positive_return c p ht⟩

/-- The changed ODE has unique forward solutions and an evolution law. -/
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
    (∀ t : ℝ, frequencyEvolution c (Real.sqrt 2) t = evolution c t) :=
  ⟨fun p => ⟨frequencyEvolution_zero_time c ν p,
      fun t ht => hasDerivAt_frequencyEvolution c ν ht p⟩,
    fun p f hf hf' h0 => frequencyEvolution_unique c ν p hf hf' h0,
    fun s t hs ht p => frequencyEvolution_add c ν hs ht p,
    fun t ht => contDiff_frequencyEvolution c ν ht 1,
    frequencyVectorField_sqrt_two c, frequencyEvolution_sqrt_two c⟩

/-- Radial trajectories and ambient singular values are independent of frequency. -/
theorem s10_radial_and_singular_values (c ν : ℝ) (t : ℝ) (ht : 0 ≤ t) (p : PhaseSpace) :
    radiusSq₁ (frequencyEvolution c ν t p) = squaredRadiusEvolution t (radiusSq₁ p) ∧
    radiusSq₂ (frequencyEvolution c ν t p) = squaredRadiusEvolution t (radiusSq₂ p) ∧
    frequencyEvolution c ν t p 4 = Real.exp (-c*t)*p 4 ∧
    (fderiv ℝ (frequencyEvolution c ν t) p).toLinearMap.singularValues =
      (fderiv ℝ (evolution c t) p).toLinearMap.singularValues ∧
    Finset.univ.val.map (fun i : Fin 5 =>
      (fderiv ℝ (frequencyEvolution c ν t) p).toLinearMap.singularValues i) =
      Finset.univ.val.map (fun i : Fin 5 => derivativeFactors c t p i) ∧
    Function.Bijective (fderiv ℝ (frequencyEvolution c ν t) p) :=
  ⟨(radiusSq_frequencyEvolution c ν ht p).1, (radiusSq_frequencyEvolution c ν ht p).2,
    frequencyEvolution_fifth c ν t p, singularValues_frequencyEvolution_eq c ν ht p,
    singularValues_fderiv_frequencyEvolution c ν ht p, fderiv_frequencyEvolution_bijective c ν ht p⟩

/-- The same compact global attractor and invariant torus. -/
theorem s10_attractor (c : ℝ) (hc : 4 < c) (ν : ℝ) :
    IsFrequencyGlobalAttractor c ν attractor ∧
    (∀ t : ℝ, ∀ p ∈ torus, frequencyEvolution c ν t p ∈ torus) ∧
    (∀ C : Set PhaseSpace, IsClosed C →
      FrequencyUniformlyAttractsBounded c ν C → attractor ⊆ C) :=
  ⟨attractor_isFrequencyGlobalAttractor (by linarith) ν,
    fun t p hp => frequencyEvolution_mem_torus c ν t hp,
    fun C hC hA => frequency_attractor_minimal hC hA⟩

/-- The dimension formulas are independent of the angular frequency. -/
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
    (∀ p : PhaseSpace, frequencyAsymptoticDimension c ν p = asymptoticDimension c p) :=
  ⟨fun t ht p => frequencyFiniteTimeDimension_eq c ν ht p,
    frequencyGlobalLyapunovDimension_eq c ν,
    fun p i => ⟨frequencyLyapunovExponent_eq c ν p i, tendsto_frequencyLyapunovExponent c ν p i⟩,
    frequencyAsymptoticDimension_eq c ν⟩

/-- Both complete maximising sets remain precisely T, for every frequency. -/
theorem s10_maximising_torus (c : ℝ) (hc : 4 < c) (ν : ℝ) :
    (∀ t : ℝ, 0 < t →
      IsGreatest (frequencyFiniteTimeDimension c ν t '' attractor) (4+4/c) ∧
      ∀ p ∈ attractor, frequencyFiniteTimeDimension c ν t p = 4+4/c ↔ p ∈ torus) ∧
    IsGreatest (frequencyAsymptoticDimension c ν '' attractor) (4+4/c) ∧
    (∀ p ∈ attractor, frequencyAsymptoticDimension c ν p = 4+4/c ↔ p ∈ torus) ∧
    frequencyGlobalLyapunovDimension c ν attractor = 4+4/c ∧
    (∀ p ∈ attractor, Tendsto (fun t : ℝ => frequencyFiniteTimeDimension c ν t p) atTop
      (𝓝 (frequencyAsymptoticDimension c ν p))) :=
  ⟨fun t ht => ⟨frequencyFiniteTimeDimension_isGreatest hc ν ht,
      fun p hp => (frequencyFiniteTimeDimension_bound_and_eq hc ν ht hp).2⟩,
    frequencyAsymptoticDimension_isGreatest hc ν,
    fun p hp => (frequencyAsymptoticDimension_bound_and_eq hc ν hp).2,
    frequencyGlobalLyapunovDimension_attractor hc ν,
    fun p hp => tendsto_frequencyFiniteTimeDimension hc ν hp⟩

/-- The exact common period for any positive rational representation a/b. -/
theorem s10_rational_common_period (c : ℝ) (a b : ℕ) (_ha : 0 < a) (hb : 0 < b)
    (p : PhaseSpace) (hp : p ∈ torus) :
    0 < 2 * Real.pi * b ∧
    Function.Periodic (fun t : ℝ => frequencyEvolution c ((a : ℝ)/(b : ℝ)) t p)
      (2 * Real.pi * b) ∧
    frequencyVectorField c ((a : ℝ)/(b : ℝ)) p ≠ 0 := by
  have h := frequency_torus_common_period c (a := (a : ℤ)) hb
    (show (a : ℝ)/(b : ℝ) = ((a : ℤ) : ℝ)/(b : ℝ) by rw [Int.cast_natCast]) hp
  exact ⟨h.1, h.2, frequency_torus_not_equilibrium c _ hp⟩

/-- All torus points are periodic maximisers for every positive rational frequency. -/
theorem s10_rational_periodic_maximum (c : ℝ) (hc : 4 < c) (ν : ℚ) (_hν : 0 < ν) :
    torus ⊆ frequencyPeriodicSet c ν ∧
    (∀ p ∈ torus, 0 < 2 * Real.pi * ν.den ∧
      Function.Periodic (fun t : ℝ => frequencyEvolution c ν t p) (2 * Real.pi * ν.den)) ∧
    IsGreatest (frequencyAsymptoticDimension c ν '' frequencyPeriodicSet c ν) (4+4/c) ∧
    (∀ t : ℝ, 0 < t →
      IsGreatest (frequencyFiniteTimeDimension c ν t '' frequencyPeriodicSet c ν) (4+4/c)) :=
  ⟨torus_subset_frequencyPeriodicSet c ν, fun p hp => rational_frequency_torus_period c ν hp,
    frequency_periodic_asymptotic_isGreatest hc ν,
    fun t ht => frequency_periodic_finiteTime_isGreatest hc ν ht⟩

/-- Positive rational frequencies with periodic maxima approach sqrt(2) arbitrarily
closely. -/
theorem s10_arbitrarily_close_periodic_maxima (c : ℝ) (hc : 4 < c) (ε : ℝ) (hε : 0 < ε) :
    ∃ ν : ℚ, 0 < ν ∧ |(ν : ℝ)-Real.sqrt 2| < ε ∧
      IsGreatest (frequencyAsymptoticDimension c ν '' frequencyPeriodicSet c ν) (4+4/c) ∧
      ∀ t : ℝ, 0 < t →
        IsGreatest (frequencyFiniteTimeDimension c ν t '' frequencyPeriodicSet c ν) (4+4/c) :=
  exists_nearby_frequency_periodic_maximum hc hε

/-- Strict invariance and nonlinear epsilon-delta instability, already within A. -/
theorem s11_invariant_unstable_sets (c : ℝ) (K : Set PhaseSpace)
    (hK : K = firstCircle 1 ∨ K = secondCircle 1 ∨ K = torus) :
    (∀ t : ℝ, 0 ≤ t → evolution c t '' K = K) ∧
    (∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 < δ →
      ∃ p ∈ attractor, Metric.infDist p K < δ ∧
        ∃ t : ℝ, 0 ≤ t ∧ ε ≤ Metric.infDist (evolution c t p) K) := by
  have h := unit_sets_invariant_and_unstable c hK
  exact ⟨h.1, h.2.1⟩

/-- The first circle's perturbations lie in its own coordinate plane and in A. -/
theorem s11_first_circle_in_plane (c : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 < δ →
      ∃ p ∈ attractor ∩ coordinatePlane 0, Metric.infDist p (firstCircle 1) < δ ∧
        ∃ t : ℝ, 0 ≤ t ∧ ε ≤ Metric.infDist (evolution c t p) (firstCircle 1) :=
  firstCircle_unstableInPlane c

/-- The second circle's perturbations lie in its own coordinate plane and in A. -/
theorem s11_second_circle_in_plane (c : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 < δ →
      ∃ p ∈ attractor ∩ coordinatePlane 1, Metric.infDist p (secondCircle 1) < δ ∧
        ∃ t : ℝ, 0 ≤ t ∧ ε ≤ Metric.infDist (evolution c t p) (secondCircle 1) :=
  secondCircle_unstableInPlane c

/-!
## Periodic growth and concavity
-/

/-- Periodic-set spatial suprema before ordinary real-time limits. -/
theorem periodic_global_growth (c : ℝ) (hc : 4 < c) :
    (∀ k : Fin 6, ∀ t : ℝ, 0 ≤ t →
      periodicGlobalLogGrowth c k t = t * (![0, 2, 2, 0, -2, -2 - c] : Fin 6 → ℝ) k) ∧
    (∀ k : Fin 6, Tendsto (fun t : ℝ => periodicGlobalLogGrowth c k t / t)
      atTop (𝓝 ((![0, 2, 2, 0, -2, -2 - c] : Fin 6 → ℝ) k))) ∧
    ((fun k : Fin 6 => periodicGlobalGrowthRate c k) = ![0, 2, 2, 0, -2, -2 - c]) ∧
    (∀ k : ℕ, k < 5 → ∀ α : ℝ, 0 ≤ α → α ≤ 1 →
      periodicGlobalGrowthInterpolation c ((k : ℝ) + α) =
        (1 - α) * periodicGlobalGrowthRate c k + α * periodicGlobalGrowthRate c (k + 1)) := by
  have hrate (k : Fin 6) := congrFun (periodicGlobalGrowthRate_table hc) k
  refine ⟨?_, ?_, periodicGlobalGrowthRate_table hc, ?_⟩
  · intro k t ht
    rw [periodicGlobalLogGrowth_eq hc ht (by omega),
      ← periodicGlobalGrowthRate_eq hc (by omega), hrate k]
  · intro k
    have h := tendsto_periodicGlobalLogGrowth_div hc (k := k) (by omega)
    rw [← periodicGlobalGrowthRate_eq hc (by omega), hrate k] at h
    exact h
  · exact fun k hk α hα₀ hα₁ => periodicGlobalGrowthInterpolation_interpolate hc hk hα₀ hα₁

/-- The full interpolant has index and dimension three, including its neutral node. -/
theorem periodic_global_dimension (c : ℝ) (hc : 4 < c) :
    kaplanYorkeIndex (periodicGlobalGrowthIncrements c) = 3 ∧
    IsGreatest {d : ℝ | d ∈ Icc 0 5 ∧ 0 ≤ periodicGlobalGrowthInterpolation c d} 3 ∧
    periodicGlobalGrowthDimension c = 3 :=
  ⟨periodicGlobalGrowthIndex_eq_three hc, periodicGlobalGrowthInterpolation_isGreatest hc,
    periodicGlobalGrowthDimension_eq_three hc⟩

/-- Concavity of the finite-time and limiting interpolants on [0,5]. -/
theorem concave_interpolants (c : ℝ) (p : PhaseSpace) :
    (∀ t : ℝ, 0 < t → ConcaveOn ℝ (Icc (0 : ℝ) 5) (fun d => Real.log
      (singularValueFunction (fderiv ℝ (evolution c t) p).toLinearMap d) / t)) ∧
    ConcaveOn ℝ (Icc (0 : ℝ) 5) (spectrumInterpolation (lyapunovExponent c p)) :=
  ⟨fun _ ht => concaveOn_log_singularValueFunction c ht p,
    concaveOn_lyapunovExponent_interpolation c p⟩

/-!
## Definitions and basic properties
-/

/-- The parameter range is c>4. -/
theorem D01_parameter (c : ℝ) (hc : 4 < c) :
    0 < c ∧ 4 < 4 + 4 / c ∧ 4 + 4 / c < 5 :=
  ⟨by linarith, targetDimension_bounds hc⟩

/-- The five-dimensional ambient norm is Euclidean. -/
theorem D02_euclidean_geometry :
    Module.finrank ℝ PhaseSpace = 5 ∧
    ∀ p : PhaseSpace,
      ‖p‖ ^ 2 = p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2 + p 3 ^ 2 + p 4 ^ 2 := by
  refine ⟨finrank_euclideanSpace_fin, ?_⟩
  intro p
  simpa only [radiusSq₁, radiusSq₂, add_assoc] using norm_sq_phaseSpace p

/-- Real coordinates, complex moduli and ordinary radii agree. -/
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
  have h₁ : Complex.normSq (⟨p 0, p 1⟩ : ℂ) = radiusSq₁ p := by
    simp [Complex.normSq_apply, radiusSq₁, pow_two]
  have h₂ : Complex.normSq (⟨p 2, p 3⟩ : ℂ) = radiusSq₂ p := by
    simp [Complex.normSq_apply, radiusSq₂, pow_two]
  refine ⟨rfl, rfl, radiusSq₁_nonneg p, radiusSq₂_nonneg p, ?_, ?_, ?_, ?_,
    Real.sqrt_nonneg _, Real.sqrt_nonneg _, ?_, by positivity⟩
  · exact (Complex.normSq_eq_norm_sq _).symm.trans h₁
  · exact (Complex.normSq_eq_norm_sq _).symm.trans h₂
  · rw [Complex.norm_def, h₁]
  · rw [Complex.norm_def, h₂]
  · intro s
    exact ⟨rfl, by unfold q; ring⟩

/-- The explicitly displayed field is smooth and has degree exactly five. -/
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
    (∀ n : WithTop ℕ∞, ContDiff ℝ n (vectorField c)) :=
  ⟨fun _ => rfl, eval_vectorFieldPolynomial c, totalDegree_vectorFieldPolynomial_le c,
    totalDegree_vectorFieldPolynomial_first c, vectorFieldPolynomial_degree c,
    contDiff_vectorField c⟩

/-- Global forward solutions, uniqueness and the evolution law. -/
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
  exact ⟨fun p => ⟨evolution_zero_time c p, fun _ ht => hasDerivAt_evolution c ht p⟩,
    fun p f hf hf' h0 => evolution_unique c p hf hf' h0,
    fun s t hs ht p => evolution_add c hs ht p,
    fun t ht n => contDiff_evolution c ht n⟩

/-- The squared-radius and ordinary-radius descriptions define the same sets. -/
theorem D06_attractor_and_torus :
    attractor = {p : PhaseSpace | radiusSq₁ p ≤ 2 ∧ radiusSq₂ p ≤ 2 ∧ p 4 = 0} ∧
    torus = {p : PhaseSpace | radiusSq₁ p = 1 ∧ radiusSq₂ p = 1 ∧ p 4 = 0} ∧
    attractor = {p : PhaseSpace | Real.sqrt (radiusSq₁ p) ≤ Real.sqrt 2 ∧
      Real.sqrt (radiusSq₂ p) ≤ Real.sqrt 2 ∧ p 4 = 0} ∧
    torus = {p : PhaseSpace | Real.sqrt (radiusSq₁ p) = 1 ∧
      Real.sqrt (radiusSq₂ p) = 1 ∧ p 4 = 0} ∧
    attractor.Nonempty ∧ IsCompact attractor ∧
    torus.Nonempty ∧ IsCompact torus ∧ torus ⊆ attractor := by
  refine ⟨rfl, rfl, ?_, ?_, attractor_nonempty, isCompact_attractor,
    torus_nonempty, isCompact_torus, torus_subset_attractor⟩
  · ext p
    simp only [attractor, mem_ofPred_eq, Real.sqrt_le_sqrt_iff (by norm_num : (0 : ℝ) ≤ 2)]
  · ext p
    simp only [torus, mem_ofPred_eq, Real.sqrt_eq_one]

/-- Standard singular values of the full ambient derivative. -/
theorem D07_ordered_positive_singular_values (c : ℝ) (t : ℝ) (ht : 0 ≤ t)
    (p : PhaseSpace) :
    Function.Bijective (fderiv ℝ (evolution c t) p) ∧
    Antitone (fun i : Fin 5 =>
      (fderiv ℝ (evolution c t) p).toLinearMap.singularValues i) ∧
    (∀ i : Fin 5, 0 < (fderiv ℝ (evolution c t) p).toLinearMap.singularValues i) ∧
    (Finset.univ.val.map (fun i : Fin 5 =>
      (fderiv ℝ (evolution c t) p).toLinearMap.singularValues i) =
      Finset.univ.val.map (derivativeFactors c t p)) := by
  refine ⟨fderiv_evolution_bijective c ht p, ?_, singularValues_evolution_pos c ht p,
    singularValues_fderiv_evolution c ht p⟩
  exact fun i j hij => (fderiv ℝ (evolution c t) p).toLinearMap.singularValues_antitone hij

/-- The fractional formula and determinant endpoint agree continuously. -/
theorem D08_singular_value_function (M : PhaseSpace →ₗ[ℝ] PhaseSpace)
    (hM : Function.Injective M) :
    singularValueFunction M 0 = 1 ∧
    (∀ k : ℕ, k < 5 → ∀ α : ℝ, 0 ≤ α → α ≤ 1 →
      singularValueFunction M ((k : ℝ) + α) =
        (∏ i ∈ Finset.range k, M.singularValues i) * M.singularValues k ^ α) ∧
    singularValueFunction M 5 = |M.det| ∧
    ContinuousOn (singularValueFunction M) (Icc 0 5) :=
  ⟨singularValueFunction_zero M,
    fun _k hk _α hα₀ hα₁ => singularValueFunction_interpolate M hk hα₀ hα₁,
    singularValueFunction_five M, (continuous_singularValueFunction hM).continuousOn⟩

/-- The finite-time maximum is attained, and the global definition keeps the infimum
over positive real times outside the spatial supremum. -/
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
      sInf {v : ℝ | ∃ τ : ℝ, 0 < τ ∧ v = sSup (finiteTimeDimension c τ '' K)} :=
  ⟨admissibleDimensions_nonempty _,
    isCompact_admissibleDimensions (fderiv_evolution_bijective c ht p).injective,
    finiteTimeDimension_isGreatest c ht p, rfl⟩

/-- The largest nonnegative partial-sum index, including its endpoint branches. -/
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
        spectrumPartialSum a (kaplanYorkeIndex a) / |spectrumEntry a (kaplanYorkeIndex a)|) :=
  ⟨spectrumPartialSum_zero a, kaplanYorkeDimension_mem_interval a,
    fun _ => rfl, kaplanYorkeIndex_mem a,
    fun _k hk hs => le_kaplanYorkeIndex hk hs, kaplanYorkeDimension_of_index_zero,
    kaplanYorkeDimension_of_index_five, fun h₀ h₅ =>
      ⟨spectrumEntry_at_kaplanYorkeIndex_neg h₅,
        kaplanYorkeDimension_of_index_between rfl h₀ h₅⟩⟩

/-- The spectrum in the convention consists of real-time limits. -/
theorem D10_actual_exponents (c : ℝ) (p : PhaseSpace) :
    Antitone (lyapunovExponent c p) ∧
    (∀ i : Fin 5, Tendsto (fun t : ℝ => Real.log
      ((fderiv ℝ (evolution c t) p).toLinearMap.singularValues i) / t)
      atTop (𝓝 (lyapunovExponent c p i))) ∧
    asymptoticDimension c p = kaplanYorkeDimension (lyapunovExponent c p) :=
  ⟨lyapunovExponent_antitone c p, tendsto_lyapunovExponent c p, rfl⟩

/-- The finite-time admissible set agrees with the Kaplan--Yorke convention applied
to the normalized logarithmic spectrum. -/
theorem D10_finite_time_convention (c : ℝ) (t : ℝ) (ht : 0 < t)
    (p : PhaseSpace) :
    {d : ℝ | d ∈ Icc 0 5 ∧
      1 ≤ singularValueFunction (fderiv ℝ (evolution c t) p).toLinearMap d} =
      Icc 0 (kaplanYorkeDimension (normalizedLogSingularValues c t p)) ∧
    finiteTimeDimension c t p =
      kaplanYorkeDimension (normalizedLogSingularValues c t p) :=
  ⟨admissibleDimensions_evolution_eq c ht p, finiteTimeDimension_eq_kaplanYorke c ht p⟩

/-- The two unit-circle angle coordinates cover the torus and have period 2*pi in
each coordinate. -/
theorem D06_torus_angle_coordinates :
    (∀ θ₁ θ₂ : ℝ, torusPoint θ₁ θ₂ ∈ torus) ∧
    (∀ p ∈ torus, ∃ θ₁ θ₂ : ℝ, torusPoint θ₁ θ₂ = p) ∧
    (∀ θ₁ θ₂ : ℝ, torusPoint (θ₁ + 2 * Real.pi) θ₂ = torusPoint θ₁ θ₂) ∧
    (∀ θ₁ θ₂ : ℝ, torusPoint θ₁ (θ₂ + 2 * Real.pi) = torusPoint θ₁ θ₂) :=
  ⟨torusPoint_mem, fun _ hp => exists_torusPoint_of_mem hp,
    torusPoint_add_two_pi_first, torusPoint_add_two_pi_second⟩

/-- Equilibrium points belong to the positive-return union, and the four nonconstant
periodic orbits are four distinct geometric orbit sets. -/
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
  refine ⟨rfl, ?_, rfl, geometricPeriodicOrbits_eq hc, geometricPeriodicOrbits_encard hc⟩
  rw [periodicEquilibriumSet_eq_positiveReturnSet hc]
  ext p
  exact ⟨fun hp => ⟨positiveReturnSet_subset_attractor hc hp, hp⟩, fun hp => hp.2⟩

/-!
## Dynamics
-/



theorem p01_hasDerivAt_radiusEvolution :
    ∀ {t r : ℝ} (ht : 0 ≤ t) (hr : 0 ≤ r),
    HasDerivAt (fun τ => radiusEvolution τ r) (radialField (radiusEvolution t r)) t :=
  @Eden.hasDerivAt_radiusEvolution

theorem p01_exists_planar_angular_lift :
    ∀ (Ω x y : ℝ) (hxy : x ^ 2 + y ^ 2 ≠ 0),
    ∃ θ : ℝ,
      (∀ t : ℝ, HasDerivAt (fun τ => θ + Ω * τ) Ω t) ∧
      ∀ t : ℝ, 0 ≤ t →
        0 < radiusEvolution t (Real.sqrt (x ^ 2 + y ^ 2)) ∧
        planarX Ω t x y = radiusEvolution t (Real.sqrt (x ^ 2 + y ^ 2)) *
          Real.cos (θ + Ω * t) ∧
        planarY Ω t x y = radiusEvolution t (Real.sqrt (x ^ 2 + y ^ 2)) *
          Real.sin (θ + Ω * t) :=
  @Eden.exists_planar_angular_lift

theorem p01_planarX_origin :
    ∀ (Ω t : ℝ),
    planarX Ω t 0 0 = 0 :=
  @Eden.planarX_origin

theorem p01_planarY_origin :
    ∀ (Ω t : ℝ),
    planarY Ω t 0 0 = 0 :=
  @Eden.planarY_origin

theorem p01_radius₁_evolution :
    ∀ (c : ℝ) {t : ℝ} (ht : 0 ≤ t) (p : PhaseSpace),
    Real.sqrt (radiusSq₁ (evolution c t p)) = radiusEvolution t (Real.sqrt (radiusSq₁ p)) :=
  @Eden.radius₁_evolution

theorem p01_radius₂_evolution :
    ∀ (c : ℝ) {t : ℝ} (ht : 0 ≤ t) (p : PhaseSpace),
    Real.sqrt (radiusSq₂ (evolution c t p)) = radiusEvolution t (Real.sqrt (radiusSq₂ p)) :=
  @Eden.radius₂_evolution



theorem p02_radialField_eq_zero_iff :
    ∀ {r : ℝ} (hr : 0 ≤ r),
    radialField r = 0 ↔ r = 0 ∨ r = 1 ∨ r = Real.sqrt 2 :=
  @Eden.radialField_eq_zero_iff

theorem p02_radialField_neg_below_one :
    ∀ {r : ℝ} (hr : 0 < r) (hr₁ : r < 1),
    radialField r < 0 :=
  @Eden.radialField_neg_below_one

theorem p02_radialField_pos_between :
    ∀ {r : ℝ} (hr₁ : 1 < r) (hr₂ : r < Real.sqrt 2),
    radialField r > 0 :=
  @Eden.radialField_pos_between

theorem p02_radialField_neg_above :
    ∀ {r : ℝ} (hr : Real.sqrt 2 < r),
    radialField r < 0 :=
  @Eden.radialField_neg_above

theorem p02_strictMono_squaredRadiusEvolution :
    ∀ {t : ℝ} (ht : 0 ≤ t),
    StrictMono (squaredRadiusEvolution t) :=
  @Eden.strictMono_squaredRadiusEvolution

theorem p02_radiusEvolution_mono :
    ∀ {t r R : ℝ} (ht : 0 ≤ t) (hr : 0 ≤ r) (hrR : r ≤ R),
    radiusEvolution t r ≤ radiusEvolution t R :=
  @Eden.radiusEvolution_mono

theorem p02_squaredRadiusEvolution_pos_iff :
    ∀ {t s : ℝ} (ht : 0 ≤ t),
    0 < squaredRadiusEvolution t s ↔ 0 < s :=
  @Eden.squaredRadiusEvolution_pos_iff

theorem p02_squaredRadiusEvolution_lt_one_iff :
    ∀ {t s : ℝ} (ht : 0 ≤ t),
    squaredRadiusEvolution t s < 1 ↔ s < 1 :=
  @Eden.squaredRadiusEvolution_lt_one_iff

theorem p02_one_lt_squaredRadiusEvolution_iff :
    ∀ {t s : ℝ} (ht : 0 ≤ t),
    1 < squaredRadiusEvolution t s ↔ 1 < s :=
  @Eden.one_lt_squaredRadiusEvolution_iff

theorem p02_squaredRadiusEvolution_lt_two_iff :
    ∀ {t s : ℝ} (ht : 0 ≤ t),
    squaredRadiusEvolution t s < 2 ↔ s < 2 :=
  @Eden.squaredRadiusEvolution_lt_two_iff

theorem p02_two_lt_squaredRadiusEvolution_iff :
    ∀ {t s : ℝ} (ht : 0 ≤ t),
    2 < squaredRadiusEvolution t s ↔ 2 < s :=
  @Eden.two_lt_squaredRadiusEvolution_iff

theorem p02_squaredRadiusEvolution_eq_self_iff :
    ∀ {t s : ℝ} (ht : 0 < t),
    squaredRadiusEvolution t s = s ↔ s = 0 ∨ s = 1 ∨ s = 2 :=
  @Eden.squaredRadiusEvolution_eq_self_iff



theorem p03_radiusEvolution_zero_time :
    ∀ {r : ℝ} (hr : 0 ≤ r),
    radiusEvolution 0 r = r :=
  @Eden.radiusEvolution_zero_time

theorem p03_radiusEvolution_nonneg :
    ∀ (t r : ℝ),
    0 ≤ radiusEvolution t r :=
  @Eden.radiusEvolution_nonneg

theorem p03_radiusEvolution_le_max :
    ∀ {t r : ℝ} (ht : 0 ≤ t) (hr : 0 ≤ r),
    radiusEvolution t r ≤ max r (Real.sqrt 2) :=
  @Eden.radiusEvolution_le_max

theorem p03_radiusEvolution_at_zero :
    ∀ (t : ℝ),
    radiusEvolution t 0 = 0 :=
  @Eden.radiusEvolution_at_zero

theorem p03_radiusEvolution_at_one :
    ∀ (t : ℝ),
    radiusEvolution t 1 = 1 :=
  @Eden.radiusEvolution_at_one

theorem p03_radiusEvolution_at_sqrt_two :
    ∀ (t : ℝ),
    radiusEvolution t (Real.sqrt 2) = Real.sqrt 2 :=
  @Eden.radiusEvolution_at_sqrt_two

theorem p03_tendsto_radiusEvolution_of_lt_one :
    ∀ {r : ℝ} (hr : 0 ≤ r) (hr₁ : r < 1),
    Tendsto (fun t => radiusEvolution t r) atTop (𝓝 0) :=
  @Eden.tendsto_radiusEvolution_of_lt_one

theorem p03_tendsto_radiusEvolution_of_one_lt :
    ∀ {r : ℝ} (hr : 1 < r),
    Tendsto (fun t => radiusEvolution t r) atTop (𝓝 (Real.sqrt 2)) :=
  @Eden.tendsto_radiusEvolution_of_one_lt

theorem p03_tendsto_radiusEvolution_one_iff :
    ∀ {r : ℝ} (hr : 0 ≤ r),
    Tendsto (fun t => radiusEvolution t r) atTop (𝓝 1) ↔ r = 1 :=
  @Eden.tendsto_radiusEvolution_one_iff



theorem p04_abs_fifth_evolution :
    ∀ (c t : ℝ) (p : PhaseSpace),
    |evolution c t p 4| = Real.exp (-c * t) * |p 4| :=
  @Eden.abs_fifth_evolution

theorem p04_isBounded_evolution_image_interval :
    ∀ (c T : ℝ) (p : PhaseSpace),
    Bornology.IsBounded ((fun t => evolution c t p) '' Icc 0 T) :=
  @Eden.isBounded_evolution_image_interval

theorem p04_exists_global_forward_solution :
    ∀ (c : ℝ) (p : PhaseSpace),
    ∃ f : ℝ → PhaseSpace, f 0 = p ∧
      ∀ t, 0 ≤ t → HasDerivAt f (vectorField c (f t)) t :=
  @Eden.exists_global_forward_solution



theorem p05_exists_complete_solution_in_attractor :
    ∀ (c : ℝ) {p : PhaseSpace} (hp : p ∈ attractor),
    ∃ f : ℝ → PhaseSpace, f 0 = p ∧ ∀ t : ℝ,
      f t ∈ attractor ∧ HasDerivAt f (vectorField c (f t)) t :=
  @Eden.exists_complete_solution_in_attractor

theorem p05_hasDerivAt_evolution_of_mem_attractor :
    ∀ (c t : ℝ) {p : PhaseSpace}
    (hp : p ∈ attractor),
    HasDerivAt (fun τ => evolution c τ p) (vectorField c (evolution c t p)) t :=
  @Eden.hasDerivAt_evolution_of_mem_attractor

theorem p05_evolution_mem_attractor_all_time :
    ∀ (c t : ℝ) {p : PhaseSpace} (hp : p ∈ attractor),
    evolution c t p ∈ attractor :=
  @Eden.evolution_mem_attractor_all_time

theorem p05_radiusEvolution_mem_lower_interval :
    ∀ (t : ℝ) {r : ℝ} (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1),
    radiusEvolution t r ∈ Set.Icc 0 1 :=
  @Eden.radiusEvolution_mem_lower_interval

theorem p05_radiusEvolution_mem_upper_interval :
    ∀ (t : ℝ) {r : ℝ}
    (hr₁ : 1 ≤ r) (hr₂ : r ≤ Real.sqrt 2),
    radiusEvolution t r ∈ Set.Icc 1 (Real.sqrt 2) :=
  @Eden.radiusEvolution_mem_upper_interval

theorem p05_evolution_image_attractor :
    ∀ (c : ℝ) {t : ℝ} (ht : 0 ≤ t),
    evolution c t '' attractor = attractor :=
  @Eden.evolution_image_attractor



theorem p06_bounded_set_radius_bounds :
    ∀ {B : Set PhaseSpace} (hB : Bornology.IsBounded B),
    ∃ M W : ℝ, Real.sqrt 2 < M ∧ 0 ≤ W ∧ ∀ p ∈ B,
      Real.sqrt (radiusSq₁ p) ≤ M ∧ Real.sqrt (radiusSq₂ p) ≤ M ∧ |p 4| ≤ W :=
  @Eden.bounded_set_radius_bounds

theorem p06_radial_excess_le :
    ∀ {t r M : ℝ} (ht : 0 ≤ t) (hr : 0 ≤ r)
    (hrM : r ≤ M) (hM : Real.sqrt 2 ≤ M),
    max (radiusEvolution t r - Real.sqrt 2) 0 ≤ radiusEvolution t M - Real.sqrt 2 :=
  @Eden.radial_excess_le

theorem p06_radiusEvolution_antitoneOn :
    ∀ {R : ℝ} (hR : Real.sqrt 2 ≤ R),
    AntitoneOn (fun t => radiusEvolution t R) (Ici 0) :=
  @Eden.radiusEvolution_antitoneOn

theorem p06_infDist_evolution_attractor_sq_le :
    ∀ (c : ℝ) {M W t : ℝ} (ht : 0 ≤ t)
    (hM : Real.sqrt 2 ≤ M) {p : PhaseSpace}
    (h₁ : Real.sqrt (radiusSq₁ p) ≤ M) (h₂ : Real.sqrt (radiusSq₂ p) ≤ M)
    (hw : |p 4| ≤ W),
    Metric.infDist (evolution c t p) attractor ^ 2 ≤ attractionBound c M W t :=
  @Eden.infDist_evolution_attractor_sq_le

theorem p06_tendsto_attractionBound :
    ∀ {c M : ℝ} (hc : 0 < c) (hM : Real.sqrt 2 < M) (W : ℝ),
    Tendsto (fun t => attractionBound c M W t) atTop (𝓝 0) :=
  @Eden.tendsto_attractionBound



theorem p07_attractor_minimal :
    ∀ {c : ℝ} {C : Set PhaseSpace} (hcompact : IsCompact C)
    (hC : UniformlyAttractsBounded c C),
    attractor ⊆ C :=
  @Eden.attractor_minimal

theorem p07_empty_not_uniformlyAttractsBounded :
    ∀ (c : ℝ),
    ¬UniformlyAttractsBounded c (∅ : Set PhaseSpace) :=
  @Eden.empty_not_uniformlyAttractsBounded



theorem p08_deriv_q :
    ∀ (s : ℝ),
    deriv q s = -2 * s + 3 :=
  @Eden.deriv_q

theorem p08_radialRate_eq_q_add_deriv :
    ∀ (s : ℝ),
    radialRate s = q s + 2 * s * deriv q s :=
  @Eden.radialRate_eq_q_add_deriv

theorem p08_tangentialRate_eq_q :
    ∀ (s : ℝ),
    tangentialRate s = q s :=
  @Eden.tangentialRate_eq_q

theorem p08_q_expansion :
    ∀ (s : ℝ),
    q s = -s ^ 2 + 3 * s - 2 :=
  @Eden.q_expansion



theorem p09_toMatrix_fderiv_planarVectorField :
    ∀ (Ω : ℝ) (p : PlanarSpace),
    (fderiv ℝ (planarVectorField Ω) p).toLinearMap.toMatrix
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis =
      q (p 0 ^ 2 + p 1 ^ 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        (2 * deriv q (p 0 ^ 2 + p 1 ^ 2)) •
          Matrix.vecMulVec (fun i => p i) (fun i => p i) +
        Ω • !![0, -1; 1, 0] :=
  @Eden.toMatrix_fderiv_planarVectorField



theorem p10_fderiv_planarEvolution_orthogonal_decomposition :
    ∀ (Ω : ℝ) {t : ℝ}
    (ht : 0 ≤ t) (p : PlanarSpace),
    (fderiv ℝ (planarEvolution Ω t) p).toLinearMap =
      ((planarRadialFrame p).trans (planarAngularRotation Ω t)).toLinearMap ∘ₗ
        planarDiagonal (planarFactors t p) ∘ₗ (planarRadialFrame p).symm.toLinearMap :=
  @Eden.fderiv_planarEvolution_orthogonal_decomposition

theorem p10_planarMovingPerturbation_zero_time :
    ∀ (Ω : ℝ) (p v : PlanarSpace),
    planarMovingPerturbation Ω 0 p v = v :=
  @Eden.planarMovingPerturbation_zero_time

theorem p10_hasDerivAt_planarMovingPerturbation :
    ∀ (Ω : ℝ) {t : ℝ} (ht : 0 < t)
    (p v : PlanarSpace),
    HasDerivAt (fun τ => planarMovingPerturbation Ω τ p v)
      (!₂[radialRate (planarEvolution Ω t p 0 ^ 2 + planarEvolution Ω t p 1 ^ 2) *
          planarMovingPerturbation Ω t p v 0,
        tangentialRate (planarEvolution Ω t p 0 ^ 2 + planarEvolution Ω t p 1 ^ 2) *
          planarMovingPerturbation Ω t p v 1]) t :=
  @Eden.hasDerivAt_planarMovingPerturbation

theorem p10_hasDerivWithinAt_planarMovingPerturbation :
    ∀ (Ω : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (p v : PlanarSpace),
    HasDerivWithinAt (fun τ => planarMovingPerturbation Ω τ p v)
      (!₂[radialRate (planarEvolution Ω t p 0 ^ 2 + planarEvolution Ω t p 1 ^ 2) *
          planarMovingPerturbation Ω t p v 0,
        tangentialRate (planarEvolution Ω t p 0 ^ 2 + planarEvolution Ω t p 1 ^ 2) *
          planarMovingPerturbation Ω t p v 1]) (Set.Ici 0) t :=
  @Eden.hasDerivWithinAt_planarMovingPerturbation

theorem p10_radialAmplitude_eq_exp_integral :
    ∀ {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s),
    radialAmplitude t s =
      Real.exp (∫ τ in (0 : ℝ)..t, radialRate (squaredRadiusEvolution τ s)) :=
  @Eden.radialAmplitude_eq_exp_integral

theorem p10_planarAmplitude_eq_exp_integral :
    ∀ {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s),
    planarAmplitude t s =
      Real.exp (∫ τ in (0 : ℝ)..t, tangentialRate (squaredRadiusEvolution τ s)) :=
  @Eden.planarAmplitude_eq_exp_integral



theorem p11_fderiv_planarEvolution_origin :
    ∀ (Ω : ℝ) {t : ℝ} (ht : 0 ≤ t) (v : PlanarSpace),
    fderiv ℝ (planarEvolution Ω t) 0 v =
      Real.exp (-2 * t) • planarAngularRotation Ω t v :=
  @Eden.fderiv_planarEvolution_origin

theorem p11_rates_at_stationary_radii :
    radialRate 0 = -2 ∧ tangentialRate 0 = -2 ∧
    radialRate 1 = 2 ∧ tangentialRate 1 = 0 ∧
    radialRate 2 = -4 ∧ tangentialRate 2 = 0 :=
  @Eden.rates_at_stationary_radii



theorem p24_equilibriumSet_eq_singleton :
    ∀ {c : ℝ} (hc : c ≠ 0),
    equilibriumSet c = {0} :=
  @Eden.equilibriumSet_eq_singleton

theorem p24_singularValues_at_origin :
    ∀ {c t : ℝ} (hc : 2 ≤ c) (ht : 0 ≤ t),
    (fun i : Fin 5 => (fderiv ℝ (evolution c t) 0).toLinearMap.singularValues i) =
      ![Real.exp (-2 * t), Real.exp (-2 * t), Real.exp (-2 * t),
        Real.exp (-2 * t), Real.exp (-c * t)] :=
  @Eden.singularValues_at_origin

theorem p24_finiteTimeDimension_at_origin :
    ∀ {c t : ℝ} (hc : 4 < c) (ht : 0 < t),
    finiteTimeDimension c t 0 = 0 :=
  @Eden.finiteTimeDimension_at_origin

theorem p24_asymptoticDimension_at_origin :
    ∀ {c : ℝ} (hc : 4 < c),
    asymptoticDimension c 0 = 0 :=
  @Eden.asymptoticDimension_at_origin



theorem p25_stationary_radii_of_evolution_return :
    ∀ (c : ℝ) {t : ℝ} (ht : 0 < t)
    {p : PhaseSpace} (h : evolution c t p = p),
    (radiusSq₁ p = 0 ∨ radiusSq₁ p = 1 ∨ radiusSq₁ p = 2) ∧
    (radiusSq₂ p = 0 ∨ radiusSq₂ p = 1 ∨ radiusSq₂ p = 2) :=
  @Eden.stationary_radii_of_evolution_return

theorem p25_fifth_eq_zero_of_evolution_return :
    ∀ {c t : ℝ} (hc : 0 < c) (ht : 0 < t)
    {p : PhaseSpace} (h : evolution c t p = p),
    p 4 = 0 :=
  @Eden.fifth_eq_zero_of_evolution_return

theorem p25_not_simultaneous_rotation_returns :
    ∀ {t : ℝ} (ht : 0 < t),
    ¬(Real.cos t = 1 ∧ Real.cos (Real.sqrt 2 * t) = 1) :=
  @Eden.not_simultaneous_rotation_returns

theorem p25_one_radius_zero_of_evolution_return :
    ∀ (c : ℝ) {t : ℝ} (ht : 0 < t)
    {p : PhaseSpace} (h : evolution c t p = p),
    radiusSq₁ p = 0 ∨ radiusSq₂ p = 0 :=
  @Eden.one_radius_zero_of_evolution_return

theorem p25_mem_positiveReturnSet_iff :
    ∀ {c : ℝ} (hc : 0 < c) (p : PhaseSpace),
    p ∈ positiveReturnSet c ↔ p = 0 ∨ p ∈ firstCircle 1 ∨ p ∈ firstCircle 2 ∨
      p ∈ secondCircle 1 ∨ p ∈ secondCircle 2 :=
  @Eden.mem_positiveReturnSet_iff



theorem p26_geometricPeriodicOrbits_eq :
    ∀ {c : ℝ} (hc : 0 < c),
    geometricPeriodicOrbits c = {firstCircle 1, firstCircle 2, secondCircle 1, secondCircle 2} :=
  @Eden.geometricPeriodicOrbits_eq

theorem p26_geometricPeriodicOrbits_encard :
    ∀ {c : ℝ} (hc : 0 < c),
    (geometricPeriodicOrbits c).encard = 4 :=
  @Eden.geometricPeriodicOrbits_encard

theorem p26_forwardOrbit_eq_firstCircle :
    ∀ (c : ℝ) {s : ℝ} (hs : s = 1 ∨ s = 2)
    {p : PhaseSpace} (hp : p ∈ firstCircle s),
    forwardOrbit c p = firstCircle s :=
  @Eden.forwardOrbit_eq_firstCircle

theorem p26_forwardOrbit_eq_secondCircle :
    ∀ (c : ℝ) {s : ℝ} (hs : s = 1 ∨ s = 2)
    {p : PhaseSpace} (hp : p ∈ secondCircle s),
    forwardOrbit c p = secondCircle s :=
  @Eden.forwardOrbit_eq_secondCircle

theorem p26_first_plane_return :
    ∀ (c : ℝ) {p : PhaseSpace}
    (h₁ : radiusSq₁ p = 1 ∨ radiusSq₁ p = 2)
    (h₂ : radiusSq₂ p = 0) (hw : p 4 = 0),
    evolution c (2 * Real.pi) p = p :=
  @Eden.first_plane_return

theorem p26_second_plane_return :
    ∀ (c : ℝ) {p : PhaseSpace}
    (h₁ : radiusSq₁ p = 0) (h₂ : radiusSq₂ p = 1 ∨ radiusSq₂ p = 2)
    (hw : p 4 = 0),
    evolution c (2 * Real.pi / Real.sqrt 2) p = p :=
  @Eden.second_plane_return

theorem p26_normalizedLogSingularValues_unit_circle :
    ∀ {c t : ℝ} (hc : 4 < c)
    (ht : 0 < t) {p : PhaseSpace} (hp : p ∈ firstCircle 1 ∨ p ∈ secondCircle 1),
    normalizedLogSingularValues c t p = ![2, 0, -2, -2, -c] :=
  @Eden.normalizedLogSingularValues_unit_circle

theorem p26_normalizedLogSingularValues_outer_circle :
    ∀ {c t : ℝ} (hc : 4 < c)
    (ht : 0 < t) {p : PhaseSpace} (hp : p ∈ firstCircle 2 ∨ p ∈ secondCircle 2),
    normalizedLogSingularValues c t p = ![0, -2, -2, -4, -c] :=
  @Eden.normalizedLogSingularValues_outer_circle

theorem p26_finiteTimeDimension_eq_asymptotic_on_periodic :
    ∀ {c t : ℝ} (hc : 0 < c)
    (ht : 0 < t) {p : PhaseSpace} (hp : p ∈ periodicEquilibriumSet c),
    finiteTimeDimension c t p = asymptoticDimension c p :=
  @Eden.finiteTimeDimension_eq_asymptotic_on_periodic

theorem p26_asymptoticDimension_first_unit_circle :
    ∀ {c : ℝ} (hc : 4 < c)
    {p : PhaseSpace} (hp : p ∈ firstCircle 1),
    asymptoticDimension c p = 3 :=
  @Eden.asymptoticDimension_first_unit_circle

theorem p26_asymptoticDimension_second_unit_circle :
    ∀ {c : ℝ} (hc : 4 < c)
    {p : PhaseSpace} (hp : p ∈ secondCircle 1),
    asymptoticDimension c p = 3 :=
  @Eden.asymptoticDimension_second_unit_circle

theorem p26_asymptoticDimension_first_outer_circle :
    ∀ {c : ℝ} (hc : 4 < c)
    {p : PhaseSpace} (hp : p ∈ firstCircle 2),
    asymptoticDimension c p = 1 :=
  @Eden.asymptoticDimension_first_outer_circle

theorem p26_asymptoticDimension_second_outer_circle :
    ∀ {c : ℝ} (hc : 4 < c)
    {p : PhaseSpace} (hp : p ∈ secondCircle 2),
    asymptoticDimension c p = 1 :=
  @Eden.asymptoticDimension_second_outer_circle



theorem p27_log_singularValueFunction_div_time :
    ∀ (c : ℝ) {t : ℝ} (ht : 0 < t)
    (p : PhaseSpace) (d : ℝ),
    Real.log (singularValueFunction (fderiv ℝ (evolution c t) p).toLinearMap d) / t =
      spectrumInterpolation (normalizedLogSingularValues c t p) d :=
  @Eden.log_singularValueFunction_div_time

theorem p27_tendstoUniformlyOn_log_singularValueFunction :
    ∀ (c : ℝ) (p : PhaseSpace),
    TendstoUniformlyOn (fun t d => Real.log
      (singularValueFunction (fderiv ℝ (evolution c t) p).toLinearMap d) / t)
      (spectrumInterpolation (lyapunovExponent c p)) atTop (Icc 0 5) :=
  @Eden.tendstoUniformlyOn_log_singularValueFunction



theorem p28_eventually_dimension_zero_of_limiting_radii :
    ∀ {c : ℝ} (hc : 4 < c)
    (p : PhaseSpace) (h₁ : limitingSquaredRadius (radiusSq₁ p) = 0)
    (h₂ : limitingSquaredRadius (radiusSq₂ p) = 0),
    ∀ᶠ t in atTop, (∀ i, normalizedLogSingularValues c t p i < 0) ∧
      finiteTimeDimension c t p = 0 :=
  @Eden.eventually_dimension_zero_of_limiting_radii

theorem p28_finiteTimeDimension_of_limiting_unit_radii :
    ∀ {c t : ℝ} (hc : 4 < c)
    (ht : 0 < t) {p : PhaseSpace} (hp : p ∈ attractor)
    (h₁ : limitingSquaredRadius (radiusSq₁ p) = 1)
    (h₂ : limitingSquaredRadius (radiusSq₂ p) = 1),
    finiteTimeDimension c t p = targetDimension c :=
  @Eden.finiteTimeDimension_of_limiting_unit_radii



theorem p29_tangentialRate_along_nonneg :
    ∀ {s t : ℝ} (hs₁ : 1 ≤ s) (hs₂ : s ≤ 2)
    (ht : 0 ≤ t),
    0 ≤ tangentialRate (squaredRadiusEvolution t s) :=
  @Eden.tangentialRate_along_nonneg

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
          -normalizedLogSingularValues c t p 1 :=
  @Eden.eventually_dimension_formula_zero_two

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
          -normalizedLogSingularValues c t p 2 :=
  @Eden.eventually_dimension_formula_two_two

/-- The exact fifth-coordinate trajectory, with every real time permitted. -/
theorem p01_fifth_coordinate (c t : ℝ) (p : PhaseSpace) :
    evolution c t p 4 = Real.exp (-c*t)*p 4 := rfl

/-- Both dimensions equal three on either unit periodic circle at every positive
time. -/
theorem p26_unit_circle_dimensions (c : ℝ) (hc : 4 < c) (t : ℝ) (ht : 0 < t)
    (p : PhaseSpace) (hp : p ∈ firstCircle 1 ∨ p ∈ secondCircle 1) :
    finiteTimeDimension c t p = 3 ∧ asymptoticDimension c p = 3 := by
  constructor
  · rw [finiteTimeDimension_eq_kaplanYorke c ht p,
      normalizedLogSingularValues_unit_circle hc ht hp, kaplanYorkeDimension_zero_one hc]
  · rcases hp with hp | hp
    · exact asymptoticDimension_first_unit_circle hc hp
    · exact asymptoticDimension_second_unit_circle hc hp

/-- Both dimensions equal one on either outer periodic circle at every positive
time. -/
theorem p26_outer_circle_dimensions (c : ℝ) (hc : 4 < c) (t : ℝ) (ht : 0 < t)
    (p : PhaseSpace) (hp : p ∈ firstCircle 2 ∨ p ∈ secondCircle 2) :
    finiteTimeDimension c t p = 1 ∧ asymptoticDimension c p = 1 := by
  constructor
  · rw [finiteTimeDimension_eq_kaplanYorke c ht p,
      normalizedLogSingularValues_outer_circle hc ht hp, kaplanYorkeDimension_zero_two hc]
  · rcases hp with hp | hp
    · exact asymptoticDimension_first_outer_circle hc hp
    · exact asymptoticDimension_second_outer_circle hc hp

/-- Strict positivity and negativity around the limiting root three, in either plane
order. -/
theorem p28_zero_one_root_and_convergence (c : ℝ) (hc : 4 < c)
    (p : PhaseSpace) (hp : p ∈ attractor)
    (hpair : (limitingSquaredRadius (radiusSq₁ p) = 0 ∧ limitingSquaredRadius (radiusSq₂ p) = 1) ∨
      (limitingSquaredRadius (radiusSq₁ p) = 1 ∧ limitingSquaredRadius (radiusSq₂ p) = 0)) :
    (∀ d : ℝ, d ∈ Ioo 0 3 → 0 < spectrumInterpolation (lyapunovExponent c p) d) ∧
    spectrumInterpolation (lyapunovExponent c p) 3 = 0 ∧
    (∀ d : ℝ, d ∈ Ioc 3 5 → spectrumInterpolation (lyapunovExponent c p) d < 0) ∧
    Tendsto (fun t : ℝ => finiteTimeDimension c t p) atTop (𝓝 3) := by
  have hs := (lyapunovExponent_eq_of_limiting_radii c p hpair).trans
    (descending_radiusPairSpectrum_zero_one hc)
  have hdim : asymptoticDimension c p = 3 := by
    rw [asymptoticDimension, hs, kaplanYorkeDimension_zero_one hc]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro d hd
    rw [hs]
    exact spectrumInterpolation_pos_zero_one hd
  · rw [hs]
    norm_num [spectrumInterpolation, singularWeight, Fin.sum_univ_succ]
  · intro d hd
    apply (spectrumInterpolation_neg_iff (lyapunovExponent_antitone c p)
      (show d ∈ Icc 0 5 from ⟨by linarith [hd.1], hd.2⟩)).mpr
    change asymptoticDimension c p < d
    rw [hdim]
    exact hd.1
  · simpa only [hdim] using tendsto_finiteTimeDimension hc hp

/-- Strict positivity and negativity around the limiting root seven halves. -/
theorem p28_one_two_root_and_convergence (c : ℝ) (hc : 4 < c)
    (p : PhaseSpace) (hp : p ∈ attractor)
    (hpair : (limitingSquaredRadius (radiusSq₁ p) = 1 ∧ limitingSquaredRadius (radiusSq₂ p) = 2) ∨
      (limitingSquaredRadius (radiusSq₁ p) = 2 ∧ limitingSquaredRadius (radiusSq₂ p) = 1)) :
    (∀ d : ℝ, d ∈ Ioo 0 (7/2) → 0 < spectrumInterpolation (lyapunovExponent c p) d) ∧
    spectrumInterpolation (lyapunovExponent c p) (7/2) = 0 ∧
    (∀ d : ℝ, d ∈ Ioc (7/2) 5 → spectrumInterpolation (lyapunovExponent c p) d < 0) ∧
    Tendsto (fun t : ℝ => finiteTimeDimension c t p) atTop (𝓝 (7/2)) := by
  have hs := (lyapunovExponent_eq_of_limiting_radii c p hpair).trans
    (descending_radiusPairSpectrum_one_two hc)
  have hdim : asymptoticDimension c p = 7/2 := by
    rw [asymptoticDimension, hs, kaplanYorkeDimension_one_two hc]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro d hd
    rw [hs]
    exact spectrumInterpolation_pos_one_two hd
  · rw [hs]
    norm_num [spectrumInterpolation, singularWeight, Fin.sum_univ_succ]
  · intro d hd
    apply (spectrumInterpolation_neg_iff (lyapunovExponent_antitone c p)
      (show d ∈ Icc 0 5 from ⟨by linarith [hd.1], hd.2⟩)).mpr
    change asymptoticDimension c p < d
    rw [hdim]
    exact hd.1
  · simpa only [hdim] using tendsto_finiteTimeDimension hc hp

/-- The first neutral rate tends to zero, the next to minus two, and the dimension
to one. -/
theorem p29_zero_two_limits (c : ℝ) (hc : 4 < c) (p : PhaseSpace) (hp : p ∈ attractor)
    (hpair : (limitingSquaredRadius (radiusSq₁ p) = 0 ∧ limitingSquaredRadius (radiusSq₂ p) = 2) ∨
      (limitingSquaredRadius (radiusSq₁ p) = 2 ∧ limitingSquaredRadius (radiusSq₂ p) = 0)) :
    Tendsto (fun t : ℝ => normalizedLogSingularValues c t p 0) atTop (𝓝 0) ∧
    Tendsto (fun t : ℝ => normalizedLogSingularValues c t p 1) atTop (𝓝 (-2)) ∧
    Tendsto (fun t : ℝ => finiteTimeDimension c t p) atTop (𝓝 1) := by
  have hs := (lyapunovExponent_eq_of_limiting_radii c p hpair).trans
    (descending_radiusPairSpectrum_zero_two hc)
  have hdim : asymptoticDimension c p = 1 := by
    rw [asymptoticDimension, hs, kaplanYorkeDimension_zero_two hc]
  refine ⟨?_, ?_, ?_⟩
  · simpa [normalizedLogSingularValues, hs] using tendsto_lyapunovExponent c p 0
  · simpa [normalizedLogSingularValues, hs] using tendsto_lyapunovExponent c p 1
  · simpa only [hdim] using tendsto_finiteTimeDimension hc hp

/-- Both neutral rates tend to zero, the next to minus four, and the dimension to
two. -/
theorem p29_two_two_limits (c : ℝ) (hc : 4 < c) (p : PhaseSpace) (hp : p ∈ attractor)
    (h₁ : limitingSquaredRadius (radiusSq₁ p) = 2)
    (h₂ : limitingSquaredRadius (radiusSq₂ p) = 2) :
    (∀ i : Fin 5, i.val < 2 →
      Tendsto (fun t : ℝ => normalizedLogSingularValues c t p i) atTop (𝓝 0)) ∧
    Tendsto (fun t : ℝ => normalizedLogSingularValues c t p 2) atTop (𝓝 (-4)) ∧
    Tendsto (fun t : ℝ => finiteTimeDimension c t p) atTop (𝓝 2) := by
  have hs := (lyapunovExponent_eq_of_limiting_radii c p (Or.inl ⟨h₁, h₂⟩)).trans
    (descending_radiusPairSpectrum_two_two hc)
  have hdim : asymptoticDimension c p = 2 := by
    rw [asymptoticDimension, hs, kaplanYorkeDimension_two_two hc]
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    have he : lyapunovExponent c p i = 0 := by
      rw [hs]
      fin_cases i <;> norm_num at *
    simpa only [normalizedLogSingularValues, he] using tendsto_lyapunovExponent c p i
  · simpa [normalizedLogSingularValues, hs] using tendsto_lyapunovExponent c p 2
  · simpa only [hdim] using tendsto_finiteTimeDimension hc hp

/-- The zero-zero limiting row has dimension limit zero. -/
theorem p28_zero_zero_limit (c : ℝ) (hc : 4 < c) (p : PhaseSpace) (hp : p ∈ attractor)
    (h₁ : limitingSquaredRadius (radiusSq₁ p) = 0)
    (h₂ : limitingSquaredRadius (radiusSq₂ p) = 0) :
    Tendsto (fun t : ℝ => finiteTimeDimension c t p) atTop (𝓝 0) := by
  have hs := (lyapunovExponent_eq_of_limiting_radii c p (Or.inl ⟨h₁, h₂⟩)).trans
    (descending_radiusPairSpectrum_zero_zero hc)
  have hdim : asymptoticDimension c p = 0 := by
    rw [asymptoticDimension, hs, kaplanYorkeDimension_zero_zero hc]
  simpa only [hdim] using tendsto_finiteTimeDimension hc hp

/-- The unit-unit limiting row has dimension limit four plus four over c. -/
theorem p28_unit_unit_limit (c : ℝ) (hc : 4 < c) (p : PhaseSpace) (hp : p ∈ attractor)
    (h₁ : limitingSquaredRadius (radiusSq₁ p) = 1)
    (h₂ : limitingSquaredRadius (radiusSq₂ p) = 1) :
    Tendsto (fun t : ℝ => finiteTimeDimension c t p) atTop (𝓝 (4+4/c)) := by
  have hs := (lyapunovExponent_eq_of_limiting_radii c p (Or.inl ⟨h₁, h₂⟩)).trans
    (descending_radiusPairSpectrum_one_one hc)
  have hdim : asymptoticDimension c p = 4+4/c := by
    rw [asymptoticDimension, hs, kaplanYorkeDimension_one_one hc]
    rfl
  simpa only [hdim] using tendsto_finiteTimeDimension hc hp

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
         Real.exp (-c * t) * v 4] :=
  @Eden.fderiv_evolution_apply

theorem p13_fderiv_evolution_radialFrame :
    ∀ (c : ℝ) {t : ℝ} (ht : 0 ≤ t) (p v : PhaseSpace),
    fderiv ℝ (evolution c t) p (radialFrame p v) =
      angularRotation t (radialFrame p (diagonalLinear (derivativeFactors c t p) v)) :=
  @Eden.fderiv_evolution_radialFrame

theorem p13_fderiv_evolution_orthogonal_decomposition :
    ∀ (c : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (p : PhaseSpace),
    (fderiv ℝ (evolution c t) p).toLinearMap =
      (angularRotation t).toLinearEquiv.toLinearMap ∘ₗ
        (radialFrame p).toLinearEquiv.toLinearMap ∘ₗ
          diagonalLinear (derivativeFactors c t p) ∘ₗ
            (radialFrame p).symm.toLinearEquiv.toLinearMap :=
  @Eden.fderiv_evolution_orthogonal_decomposition

theorem p13_derivativeFactors_pos :
    ∀ (c : ℝ) {t : ℝ} (ht : 0 ≤ t) (p : PhaseSpace) (i : Fin 5),
    0 < derivativeFactors c t p i :=
  @Eden.derivativeFactors_pos

theorem p13_singularValues_fderiv_evolution :
    ∀ (c : ℝ) {t : ℝ} (ht : 0 ≤ t) (p : PhaseSpace),
    Finset.univ.val.map (fun i : Fin 5 => (fderiv ℝ (evolution c t) p).toLinearMap.singularValues i) =
      Finset.univ.val.map (fun i : Fin 5 => derivativeFactors c t p i) :=
  @Eden.singularValues_fderiv_evolution

theorem p13_log_planarAmplitude_eq_integral :
    ∀ {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s),
    Real.log (planarAmplitude t s) =
      ∫ τ in (0 : ℝ)..t, tangentialRate (squaredRadiusEvolution τ s) :=
  @Eden.log_planarAmplitude_eq_integral

theorem p13_log_radialAmplitude_eq_integral :
    ∀ {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s),
    Real.log (radialAmplitude t s) =
      ∫ τ in (0 : ℝ)..t, radialRate (squaredRadiusEvolution τ s) :=
  @Eden.log_radialAmplitude_eq_integral

theorem p13_planarAmplitude_eq_exp_integral :
    ∀ {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s),
    planarAmplitude t s =
      Real.exp (∫ τ in (0 : ℝ)..t, tangentialRate (squaredRadiusEvolution τ s)) :=
  @Eden.planarAmplitude_eq_exp_integral

theorem p13_radialAmplitude_eq_exp_integral :
    ∀ {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s),
    radialAmplitude t s =
      Real.exp (∫ τ in (0 : ℝ)..t, radialRate (squaredRadiusEvolution τ s)) :=
  @Eden.radialAmplitude_eq_exp_integral

theorem p14_radialRate_add_four :
    ∀ (s : ℝ),
    radialRate s + 4 = (2 - s) * (5 * s + 1) :=
  @Eden.radialRate_add_four

theorem p14_tangentialRate_add_two :
    ∀ (s : ℝ),
    tangentialRate s + 2 = s * (3 - s) :=
  @Eden.tangentialRate_add_two

theorem p14_rates_sum :
    ∀ (s : ℝ),
    radialRate s + tangentialRate s = 2 - 6 * (s - 1) ^ 2 :=
  @Eden.rates_sum

theorem p15_radialRate_lower_bound :
    ∀ {s : ℝ} (hs₀ : 0 ≤ s) (hs₂ : s ≤ 2),
    -4 ≤ radialRate s :=
  @Eden.radialRate_lower_bound

theorem p15_tangentialRate_lower_bound :
    ∀ {s : ℝ} (hs₀ : 0 ≤ s) (hs₂ : s ≤ 2),
    -2 ≤ tangentialRate s :=
  @Eden.tangentialRate_lower_bound

theorem p16_radiusSq₁_evolution :
    ∀ (c : ℝ) {t : ℝ} (ht : 0 ≤ t) (p : PhaseSpace),
    radiusSq₁ (evolution c t p) = squaredRadiusEvolution t (radiusSq₁ p) :=
  @Eden.radiusSq₁_evolution

theorem p16_radiusSq₂_evolution :
    ∀ (c : ℝ) {t : ℝ} (ht : 0 ≤ t) (p : PhaseSpace),
    radiusSq₂ (evolution c t p) = squaredRadiusEvolution t (radiusSq₂ p) :=
  @Eden.radiusSq₂_evolution

theorem p16_evolution_mem_attractor :
    ∀ (c : ℝ) {t : ℝ} (ht : 0 ≤ t)
    {p : PhaseSpace} (hp : p ∈ attractor),
    evolution c t p ∈ attractor :=
  @Eden.evolution_mem_attractor

theorem p16_derivativeFactors_planar_lower_bound :
    ∀ (c : ℝ) {t : ℝ} (ht : 0 ≤ t)
    {p : PhaseSpace} (hp : p ∈ attractor) (i : Fin 4),
    Real.exp (-4 * t) ≤ derivativeFactors c t p i.castSucc :=
  @Eden.derivativeFactors_planar_lower_bound

theorem p16_exp_fifth_lt_planar_bound :
    ∀ {c t : ℝ} (hc : 4 < c) (ht : 0 < t),
    Real.exp (-c * t) < Real.exp (-4 * t) :=
  @Eden.exp_fifth_lt_planar_bound

theorem p16_derivativeFactors_fifth_lt_planar :
    ∀ {c t : ℝ} (hc : 4 < c) (ht : 0 < t)
    {p : PhaseSpace} (hp : p ∈ attractor) (i : Fin 4),
    derivativeFactors c t p 4 < derivativeFactors c t p i.castSucc :=
  @Eden.derivativeFactors_fifth_lt_planar

theorem p16_singularValues_fderiv_evolution_fifth :
    ∀ {c t : ℝ} (hc : 4 ≤ c) (ht : 0 ≤ t)
    {p : PhaseSpace} (hp : p ∈ attractor),
    (fderiv ℝ (evolution c t) p).toLinearMap.singularValues 4 = Real.exp (-c * t) :=
  @Eden.singularValues_fderiv_evolution_fifth

theorem p17_volumeDefect_eq_integral_evolution :
    ∀ (c : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (p : PhaseSpace),
    volumeDefect t p = ∫ τ in (0 : ℝ)..t,
      ((radiusSq₁ (evolution c τ p) - 1) ^ 2 +
        (radiusSq₂ (evolution c τ p) - 1) ^ 2) :=
  @Eden.volumeDefect_eq_integral_evolution

theorem p17_continuousOn_volumeDefect_integrand :
    ∀ (c : ℝ) (p : PhaseSpace),
    ContinuousOn (fun τ => (radiusSq₁ (evolution c τ p) - 1) ^ 2 +
      (radiusSq₂ (evolution c τ p) - 1) ^ 2) (Set.Ici 0) :=
  @Eden.continuousOn_volumeDefect_integrand

theorem p17_volumeDefect_integrand_nonneg :
    ∀ (c τ : ℝ) (p : PhaseSpace),
    0 ≤ (radiusSq₁ (evolution c τ p) - 1) ^ 2 +
      (radiusSq₂ (evolution c τ p) - 1) ^ 2 :=
  @Eden.volumeDefect_integrand_nonneg

theorem p17_volumeDefect_nonneg :
    ∀ {t : ℝ} (ht : 0 ≤ t) (p : PhaseSpace),
    0 ≤ volumeDefect t p :=
  @Eden.volumeDefect_nonneg

theorem p17_log_singularValues_fderiv_evolution_prod_four :
    ∀ {c t : ℝ}
    (hc : 4 ≤ c) (ht : 0 ≤ t) {p : PhaseSpace} (hp : p ∈ attractor),
    Real.log (∏ i : Fin 4, (fderiv ℝ (evolution c t) p).toLinearMap.singularValues i) =
      4 * t - 6 * volumeDefect t p :=
  @Eden.log_singularValues_fderiv_evolution_prod_four

theorem p17_singularValues_fderiv_evolution_prod_four :
    ∀ {c t : ℝ} (hc : 4 ≤ c) (ht : 0 ≤ t)
    {p : PhaseSpace} (hp : p ∈ attractor),
    (∏ i : Fin 4, (fderiv ℝ (evolution c t) p).toLinearMap.singularValues i) =
      Real.exp (4 * t - 6 * volumeDefect t p) :=
  @Eden.singularValues_fderiv_evolution_prod_four

theorem p18_volumeDefect_eq_zero_iff :
    ∀ {t : ℝ} (ht : 0 < t)
    {p : PhaseSpace} (hp : p ∈ attractor),
    volumeDefect t p = 0 ↔ p ∈ torus :=
  @Eden.volumeDefect_eq_zero_iff

theorem p18_singularValues_fderiv_evolution_prod_four_le :
    ∀ {c t : ℝ}
    (hc : 4 ≤ c) (ht : 0 ≤ t) {p : PhaseSpace} (hp : p ∈ attractor),
    (∏ i : Fin 4, (fderiv ℝ (evolution c t) p).toLinearMap.singularValues i) ≤
      Real.exp (4 * t) :=
  @Eden.singularValues_fderiv_evolution_prod_four_le

theorem p18_singularValues_fderiv_evolution_prod_four_eq_iff :
    ∀ {c t : ℝ}
    (hc : 4 ≤ c) (ht : 0 < t) {p : PhaseSpace} (hp : p ∈ attractor),
    (∏ i : Fin 4, (fderiv ℝ (evolution c t) p).toLinearMap.singularValues i) =
      Real.exp (4 * t) ↔ p ∈ torus :=
  @Eden.singularValues_fderiv_evolution_prod_four_eq_iff

theorem p19_singularValueFunction_evolution_on_four_five :
    ∀ {c t d : ℝ}
    (hc : 4 ≤ c) (ht : 0 ≤ t) {p : PhaseSpace} (hp : p ∈ attractor)
    (hd₄ : 4 ≤ d) (hd₅ : d ≤ 5),
    singularValueFunction (fderiv ℝ (evolution c t) p).toLinearMap d =
      Real.exp (4 * t - 6 * volumeDefect t p - c * t * (d - 4)) :=
  @Eden.singularValueFunction_evolution_on_four_five

theorem p19_singularValueFunction_evolution_at_target :
    ∀ {c t : ℝ}
    (hc : 4 < c) (ht : 0 ≤ t) {p : PhaseSpace} (hp : p ∈ attractor),
    singularValueFunction (fderiv ℝ (evolution c t) p).toLinearMap (targetDimension c) =
      Real.exp (-6 * volumeDefect t p) :=
  @Eden.singularValueFunction_evolution_at_target

theorem p19_singularValueFunction_evolution_above_target :
    ∀ {c t d : ℝ}
    (hc : 4 < c) (ht : 0 < t) {p : PhaseSpace} (hp : p ∈ attractor)
    (hd : targetDimension c < d) (hd₅ : d ≤ 5),
    singularValueFunction (fderiv ℝ (evolution c t) p).toLinearMap d =
      Real.exp (-6 * volumeDefect t p - c * t * (d - targetDimension c)) :=
  @Eden.singularValueFunction_evolution_above_target

theorem p19_singularValueFunction_evolution_above_target_lt_one :
    ∀ {c t d : ℝ}
    (hc : 4 < c) (ht : 0 < t) {p : PhaseSpace} (hp : p ∈ attractor)
    (hd : targetDimension c < d) (hd₅ : d ≤ 5),
    singularValueFunction (fderiv ℝ (evolution c t) p).toLinearMap d < 1 :=
  @Eden.singularValueFunction_evolution_above_target_lt_one

theorem p19_finiteTimeDimension_le_target :
    ∀ {c t : ℝ} (hc : 4 < c) (ht : 0 < t)
    {p : PhaseSpace} (hp : p ∈ attractor),
    finiteTimeDimension c t p ≤ targetDimension c :=
  @Eden.finiteTimeDimension_le_target

theorem p20_singularValues_on_torus :
    ∀ {c t : ℝ} (hc : 0 ≤ c) (ht : 0 ≤ t)
    {p : PhaseSpace} (hp : p ∈ torus),
    (fun i : Fin 5 => (fderiv ℝ (evolution c t) p).toLinearMap.singularValues i) =
      ![Real.exp (2 * t), Real.exp (2 * t), 1, 1, Real.exp (-c * t)] :=
  @Eden.singularValues_on_torus

theorem p20_finiteTimeDimension_eq_target_iff :
    ∀ {c t : ℝ} (hc : 4 < c) (ht : 0 < t)
    {p : PhaseSpace} (hp : p ∈ attractor),
    finiteTimeDimension c t p = targetDimension c ↔ p ∈ torus :=
  @Eden.finiteTimeDimension_eq_target_iff

theorem p20_finiteTimeDimension_attractor_isGreatest :
    ∀ {c t : ℝ} (hc : 4 < c) (ht : 0 < t),
    IsGreatest (finiteTimeDimension c t '' attractor) (targetDimension c) :=
  @Eden.finiteTimeDimension_attractor_isGreatest

theorem p21_tendsto_radialRate_average :
    ∀ {s : ℝ} (hs : 0 ≤ s),
    Tendsto (fun t => (∫ τ in (0 : ℝ)..t,
      radialRate (squaredRadiusEvolution τ s)) / t) atTop
      (𝓝 (radialRate (limitingSquaredRadius s))) :=
  @Eden.tendsto_radialRate_average

theorem p21_tendsto_tangentialRate_average :
    ∀ {s : ℝ} (hs : 0 ≤ s),
    Tendsto (fun t => (∫ τ in (0 : ℝ)..t,
      tangentialRate (squaredRadiusEvolution τ s)) / t) atTop
      (𝓝 (tangentialRate (limitingSquaredRadius s))) :=
  @Eden.tendsto_tangentialRate_average

theorem p21_limiting_rates_of_lt_one :
    ∀ {s : ℝ} (hs : s < 1),
    radialRate (limitingSquaredRadius s) = -2 ∧
      tangentialRate (limitingSquaredRadius s) = -2 :=
  @Eden.limiting_rates_of_lt_one

theorem p21_limiting_rates_at_one :
    radialRate (limitingSquaredRadius 1) = 2 ∧
      tangentialRate (limitingSquaredRadius 1) = 0 :=
  @Eden.limiting_rates_at_one

theorem p21_limiting_rates_of_one_lt :
    ∀ {s : ℝ} (hs : 1 < s),
    radialRate (limitingSquaredRadius s) = -4 ∧
      tangentialRate (limitingSquaredRadius s) = 0 :=
  @Eden.limiting_rates_of_one_lt

theorem p21_tendsto_log_derivativeFactors_div :
    ∀ (c : ℝ) (p : PhaseSpace) (i : Fin 5),
    Tendsto (fun t => Real.log (derivativeFactors c t p i) / t) atTop
      (𝓝 (factorExponents c p i)) :=
  @Eden.tendsto_log_derivativeFactors_div

theorem p22_lipschitzWith_descending :
    ∀ (n : ℕ),
    LipschitzWith 1 (descending : (Fin n → ℝ) → (Fin n → ℝ)) :=
  @Eden.lipschitzWith_descending

theorem p22_normalizedLogSingularValues_eq_descending :
    ∀ (c : ℝ) {t : ℝ} (ht : 0 < t)
    (p : PhaseSpace),
    normalizedLogSingularValues c t p =
      descending (fun i => Real.log (derivativeFactors c t p i) / t) :=
  @Eden.normalizedLogSingularValues_eq_descending

theorem p22_tendsto_normalizedLogSingularValues :
    ∀ (c : ℝ) (p : PhaseSpace),
    Tendsto (fun t => normalizedLogSingularValues c t p) atTop
      (𝓝 (descending (factorExponents c p))) :=
  @Eden.tendsto_normalizedLogSingularValues

theorem p22_lyapunovExponent_eq_descending :
    ∀ (c : ℝ) (p : PhaseSpace) (i : Fin 5),
    lyapunovExponent c p i = descending (factorExponents c p) i :=
  @Eden.lyapunovExponent_eq_descending

theorem p22_tendsto_lyapunovExponent :
    ∀ (c : ℝ) (p : PhaseSpace) (i : Fin 5),
    Tendsto (fun t => Real.log
      ((fderiv ℝ (evolution c t) p).toLinearMap.singularValues i) / t) atTop
      (𝓝 (lyapunovExponent c p i)) :=
  @Eden.tendsto_lyapunovExponent

theorem p22_lyapunovExponent_eq_radiusPairSpectrum :
    ∀ (c : ℝ) (p : PhaseSpace),
    lyapunovExponent c p = descending (radiusPairSpectrum c
      (limitingSquaredRadius (radiusSq₁ p)) (limitingSquaredRadius (radiusSq₂ p))) :=
  @Eden.lyapunovExponent_eq_radiusPairSpectrum

theorem p22_limitingSquaredRadius_cases :
    ∀ (s : ℝ),
    limitingSquaredRadius s = 0 ∨ limitingSquaredRadius s = 1 ∨ limitingSquaredRadius s = 2 :=
  @Eden.limitingSquaredRadius_cases

theorem p22_limitingSquaredRadius_eq_one_iff :
    ∀ (s : ℝ),
    limitingSquaredRadius s = 1 ↔ s = 1 :=
  @Eden.limitingSquaredRadius_eq_one_iff

theorem p22_descending_radiusPairSpectrum_swap :
    ∀ (c s₁ s₂ : ℝ),
    descending (radiusPairSpectrum c s₁ s₂) = descending (radiusPairSpectrum c s₂ s₁) :=
  @Eden.descending_radiusPairSpectrum_swap

theorem p22_lyapunovExponent_eq_of_limiting_radii :
    ∀ (c : ℝ) (p : PhaseSpace) {s₁ s₂ : ℝ}
    (h : (limitingSquaredRadius (radiusSq₁ p) = s₁ ∧
        limitingSquaredRadius (radiusSq₂ p) = s₂) ∨
      (limitingSquaredRadius (radiusSq₁ p) = s₂ ∧
        limitingSquaredRadius (radiusSq₂ p) = s₁)),
    lyapunovExponent c p = descending (radiusPairSpectrum c s₁ s₂) :=
  @Eden.lyapunovExponent_eq_of_limiting_radii

theorem p22_descending_radiusPairSpectrum_zero_zero :
    ∀ {c : ℝ} (hc : 4 < c),
    descending (radiusPairSpectrum c 0 0) = ![-2, -2, -2, -2, -c] :=
  @Eden.descending_radiusPairSpectrum_zero_zero

theorem p22_descending_radiusPairSpectrum_zero_one :
    ∀ {c : ℝ} (hc : 4 < c),
    descending (radiusPairSpectrum c 0 1) = ![2, 0, -2, -2, -c] :=
  @Eden.descending_radiusPairSpectrum_zero_one

theorem p22_descending_radiusPairSpectrum_zero_two :
    ∀ {c : ℝ} (hc : 4 < c),
    descending (radiusPairSpectrum c 0 2) = ![0, -2, -2, -4, -c] :=
  @Eden.descending_radiusPairSpectrum_zero_two

theorem p22_descending_radiusPairSpectrum_one_one :
    ∀ {c : ℝ} (hc : 4 < c),
    descending (radiusPairSpectrum c 1 1) = ![2, 2, 0, 0, -c] :=
  @Eden.descending_radiusPairSpectrum_one_one

theorem p22_descending_radiusPairSpectrum_one_two :
    ∀ {c : ℝ} (hc : 4 < c),
    descending (radiusPairSpectrum c 1 2) = ![2, 0, 0, -4, -c] :=
  @Eden.descending_radiusPairSpectrum_one_two

theorem p22_descending_radiusPairSpectrum_two_two :
    ∀ {c : ℝ} (hc : 4 < c),
    descending (radiusPairSpectrum c 2 2) = ![0, 0, -4, -4, -c] :=
  @Eden.descending_radiusPairSpectrum_two_two

theorem p22_kaplanYorkeDimension_zero_zero :
    ∀ {c : ℝ} (hc : 4 < c),
    kaplanYorkeDimension ![-2, -2, -2, -2, -c] = 0 :=
  @Eden.kaplanYorkeDimension_zero_zero

theorem p22_kaplanYorkeDimension_zero_one :
    ∀ {c : ℝ} (hc : 4 < c),
    kaplanYorkeDimension ![2, 0, -2, -2, -c] = 3 :=
  @Eden.kaplanYorkeDimension_zero_one

theorem p22_kaplanYorkeDimension_zero_two :
    ∀ {c : ℝ} (hc : 4 < c),
    kaplanYorkeDimension ![0, -2, -2, -4, -c] = 1 :=
  @Eden.kaplanYorkeDimension_zero_two

theorem p22_kaplanYorkeDimension_one_one :
    ∀ {c : ℝ} (hc : 4 < c),
    kaplanYorkeDimension ![2, 2, 0, 0, -c] = targetDimension c :=
  @Eden.kaplanYorkeDimension_one_one

theorem p22_kaplanYorkeDimension_one_two :
    ∀ {c : ℝ} (hc : 4 < c),
    kaplanYorkeDimension ![2, 0, 0, -4, -c] = 7 / 2 :=
  @Eden.kaplanYorkeDimension_one_two

theorem p22_kaplanYorkeDimension_two_two :
    ∀ {c : ℝ} (hc : 4 < c),
    kaplanYorkeDimension ![0, 0, -4, -4, -c] = 2 :=
  @Eden.kaplanYorkeDimension_two_two

theorem p23_kaplanYorkeDimension_radiusPair_bound_and_eq :
    ∀ {c s₁ s₂ : ℝ} (hc : 4 < c)
    (hs₁ : s₁ = 0 ∨ s₁ = 1 ∨ s₁ = 2) (hs₂ : s₂ = 0 ∨ s₂ = 1 ∨ s₂ = 2),
    kaplanYorkeDimension (descending (radiusPairSpectrum c s₁ s₂)) ≤ targetDimension c ∧
      (kaplanYorkeDimension (descending (radiusPairSpectrum c s₁ s₂)) = targetDimension c ↔
        s₁ = 1 ∧ s₂ = 1) :=
  @Eden.kaplanYorkeDimension_radiusPair_bound_and_eq

theorem p23_asymptoticDimension_le_target :
    ∀ {c : ℝ} (hc : 4 < c) (p : PhaseSpace),
    asymptoticDimension c p ≤ targetDimension c :=
  @Eden.asymptoticDimension_le_target

theorem p23_asymptoticDimension_eq_target_iff_radii :
    ∀ {c : ℝ} (hc : 4 < c) (p : PhaseSpace),
    asymptoticDimension c p = targetDimension c ↔ radiusSq₁ p = 1 ∧ radiusSq₂ p = 1 :=
  @Eden.asymptoticDimension_eq_target_iff_radii

theorem p23_asymptoticDimension_eq_target_iff :
    ∀ {c : ℝ} (hc : 4 < c) {p : PhaseSpace}
    (hp : p ∈ attractor),
    asymptoticDimension c p = targetDimension c ↔ p ∈ torus :=
  @Eden.asymptoticDimension_eq_target_iff

theorem p23_asymptoticDimension_lt_target_of_not_mem_torus :
    ∀ {c : ℝ} (hc : 4 < c)
    {p : PhaseSpace} (hp : p ∈ attractor) (hT : p ∉ torus),
    asymptoticDimension c p < targetDimension c :=
  @Eden.asymptoticDimension_lt_target_of_not_mem_torus

theorem s04_fderiv_evolution_add :
    ∀ (c : ℝ) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    (p : PhaseSpace),
    fderiv ℝ (evolution c (s + t)) p =
      (fderiv ℝ (evolution c t) (evolution c s p)).comp (fderiv ℝ (evolution c s) p) :=
  @Eden.fderiv_evolution_add

theorem s04_exteriorOperator_comp :
    ∀ (k : ℕ) (A B : PhaseSpace →ₗ[ℝ] PhaseSpace),
    exteriorOperator k (A ∘ₗ B) = (exteriorOperator k A).comp (exteriorOperator k B) :=
  @Eden.exteriorOperator_comp

theorem s04_singularValueFunction_integer_comp_le :
    ∀ {k : ℕ} (hk : k ≤ 5)
    (A B : PhaseSpace →ₗ[ℝ] PhaseSpace),
    singularValueFunction (A ∘ₗ B) k ≤ singularValueFunction A k * singularValueFunction B k :=
  @Eden.singularValueFunction_integer_comp_le

/-- The defect vanishes exactly when both radii remain unit throughout the interval. -/
theorem p18_zero_defect_entire_interval (c : ℝ) {t : ℝ} (ht : 0 < t)
    {p : PhaseSpace} (hp : p ∈ attractor) :
    volumeDefect t p = 0 ↔ ∀ τ ∈ Icc (0 : ℝ) t,
      radiusSq₁ (evolution c τ p) = 1 ∧ radiusSq₂ (evolution c τ p) = 1 := by
  constructor
  · intro h τ hτ
    have hT := evolution_mem_torus c hτ.1 ((volumeDefect_eq_zero_iff ht hp).1 h)
    exact ⟨hT.1, hT.2.1⟩
  · intro h
    have h0 := h 0 ⟨le_rfl, ht.le⟩
    rw [evolution_zero_time] at h0
    exact (volumeDefect_eq_zero_iff ht hp).2 ⟨h0.1, h0.2, hp.2.2⟩

theorem p16_radius_domain (c : ℝ) {p : PhaseSpace} (hp : p ∈ attractor)
    {t : ℝ} (ht : 0 ≤ t) : ∀ τ ∈ Icc (0 : ℝ) t,
      radiusSq₁ (evolution c τ p) ∈ Icc (0 : ℝ) 2 ∧
      radiusSq₂ (evolution c τ p) ∈ Icc (0 : ℝ) 2 := by
  intro τ hτ
  have hA := evolution_mem_attractor c hτ.1 hp
  exact ⟨⟨radiusSq₁_nonneg _, hA.1⟩, ⟨radiusSq₂_nonneg _, hA.2.1⟩⟩

end EdenVerified
