import Eden.ExteriorGram

/-!
# The integer exterior-norm identity for every ambient linear map

An attaining basis wedge and the exact Gram norm formula prove the full
identity, without an invertibility hypothesis. The degrees 1 through 5
are included along with degree 0. Products are compared directly, so rank
deficiency and zero singular values require no logarithmic convention.
-/

noncomputable section
namespace Eden

theorem isGreatest_selectedSingularProduct {k : ℕ} (hk : k ≤ 5)
    (A : PhaseSpace →ₗ[ℝ] PhaseSpace) :
    IsGreatest (Set.range (selectedSingularProduct k A)) (singularValueFunction A k) := by
  have h := isGreatest_selected_prod hk
    (fun i j hij => A.singularValues_antitone hij)
    (fun i : Fin 5 => A.singularValues_nonneg i)
    (rfl : Finset.univ.val.map (fun i : Fin 5 => A.singularValues i) = _)
  rw [singularValueFunction_integer_eq_fin_prod A hk]
  convert h using 1
  ext r
  simp only [Set.mem_range, Set.mem_ofPred_eq, selectedSingularProduct_eq_prod]
  constructor
  · rintro ⟨s, hs⟩
    exact ⟨s, hs.symm⟩
  · rintro ⟨s, hs⟩
    exact ⟨s, hs.symm⟩

theorem norm_exterior_map_singular_basis (k : ℕ) (A : PhaseSpace →ₗ[ℝ] PhaseSpace)
    (s : ExteriorIndex k) :
    ‖exteriorPower.map k A (singularExteriorBasis k A s)‖ = selectedSingularProduct k A s := by
  classical
  have h := norm_sq_exterior_map_singular_basis k A (singularExteriorBasis k A s)
  simp at h
  nlinarith [norm_nonneg (exteriorPower.map k A (singularExteriorBasis k A s)),
    selectedSingularProduct_nonneg k A s]

theorem norm_exterior_map_le_singularValueFunction {k : ℕ} (hk : k ≤ 5)
    (A : PhaseSpace →ₗ[ℝ] PhaseSpace) (v : ExteriorSpace k) :
    ‖exteriorPower.map k A v‖ ≤ singularValueFunction A k * ‖v‖ := by
  classical
  obtain ⟨⟨s, hs⟩, hmax⟩ := isGreatest_selectedSingularProduct hk A
  have hM : 0 ≤ singularValueFunction A k := hs ▸ selectedSingularProduct_nonneg k A s
  have hsum : ‖exteriorPower.map k A v‖ ^ 2 ≤ (singularValueFunction A k) ^ 2 * ‖v‖ ^ 2 := by
    rw [norm_sq_exterior_map_singular_basis,
      ← (singularExteriorBasis k A).repr.norm_map v, EuclideanSpace.real_norm_sq_eq,
      Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hj₀ := selectedSingularProduct_nonneg k A j
    have hjM := hmax ⟨j, rfl⟩
    have hsquare : selectedSingularProduct k A j ^ 2 ≤ singularValueFunction A k ^ 2 := by
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hsquare
      (sq_nonneg ((singularExteriorBasis k A).repr v j))]
  nlinarith [norm_nonneg (exteriorPower.map k A v), norm_nonneg v,
    mul_nonneg hM (norm_nonneg v)]

/-- For every real ambient linear map, omega_k is the exterior
operator norm. Singular maps, ties and the endpoint degrees are included. -/
theorem norm_exteriorOperator_eq_singularValueFunction {k : ℕ} (hk : k ≤ 5)
    (A : PhaseSpace →ₗ[ℝ] PhaseSpace) :
    ‖exteriorOperator k A‖ = singularValueFunction A k := by
  obtain ⟨⟨s, hs⟩, hmax⟩ := isGreatest_selectedSingularProduct hk A
  have hM : 0 ≤ singularValueFunction A k := hs ▸ selectedSingularProduct_nonneg k A s
  apply le_antisymm
  · exact ContinuousLinearMap.opNorm_le_bound _ hM
      (norm_exterior_map_le_singularValueFunction hk A)
  · have h := (exteriorOperator k A).le_opNorm (singularExteriorBasis k A s)
    rw [exteriorOperator_apply, norm_exterior_map_singular_basis,
      OrthonormalBasis.norm_eq_one, mul_one, hs] at h
    exact h

end Eden
