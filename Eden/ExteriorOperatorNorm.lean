import Eden.ExteriorMaximalGrowth
import Eden.SelectedProducts
import Eden.SingularValueFunction

/-!
# The exterior operator norm

The canonical exterior map becomes a continuous linear map through Mathlib's
finite-dimensional continuity theorem. Its norm is the usual operator norm.
The exact squared-coordinate formula gives its upper bound, while a unit
wedge in the fixed initial frame attains the largest selected product.
Ordering and the singular-value multiset identify that product with
the integer singular-value function.
-/

noncomputable section
open Set
namespace Eden

/-- The induced map, with its finite-dimensional continuity proof. -/
def exteriorOperator (k : ℕ) (A : PhaseSpace →ₗ[ℝ] PhaseSpace) :
    ExteriorSpace k →L[ℝ] ExteriorSpace k :=
  (exteriorPower.map k A).toContinuousLinearMap

theorem exteriorOperator_apply (k : ℕ) (A : PhaseSpace →ₗ[ℝ] PhaseSpace)
    (v : ExteriorSpace k) : exteriorOperator k A v = exteriorPower.map k A v := rfl

theorem singularValueFunction_integer (A : PhaseSpace →ₗ[ℝ] PhaseSpace)
    {k : ℕ} (hk : k ≤ 5) :
    singularValueFunction A k = ∏ i ∈ Finset.range k, A.singularValues i := by
  rcases lt_or_eq_of_le hk with hk | rfl
  · simpa using singularValueFunction_interpolate A hk (le_refl (0 : ℝ)) (by norm_num)
  · exact spectralProduct_top 5 A.singularValues

theorem singularValueFunction_integer_eq_fin_prod (A : PhaseSpace →ₗ[ℝ] PhaseSpace)
    {k : ℕ} (hk : k ≤ 5) :
    singularValueFunction A k = ∏ i : Fin k, A.singularValues (Fin.castLE hk i) := by
  rw [singularValueFunction_integer A hk, ← Fin.prod_univ_eq_prod_range]
  rfl

theorem exteriorFactor_eq_prod (k : ℕ) (d : PhaseSpace) (s : ExteriorIndex k) :
    exteriorFactor k d s = ∏ j ∈ s.val, d j := by
  unfold exteriorFactor
  change (∏ i : Fin k, d (s.val.orderEmbOfFin s.property i)) = _
  conv_rhs => rw [← Finset.image_orderEmbOfFin_univ s.val s.property]
  rw [Finset.prod_image (fun _ _ _ _ h => (s.val.orderEmbOfFin s.property).injective h)]

theorem isGreatest_exteriorFactor {k : ℕ} (hk : k ≤ 5) (c : ℝ) {t : ℝ}
    (ht : 0 ≤ t) (p : PhaseSpace) :
    IsGreatest (Set.range (exteriorFactor k (derivativeFactors c t p)))
      (singularValueFunction (fderiv ℝ (evolution c t) p).toLinearMap k) := by
  have h := isGreatest_selected_prod hk
    (fun i j hij => (fderiv ℝ (evolution c t) p).toLinearMap.singularValues_antitone hij)
    (fun i : Fin 5 => (singularValues_evolution_pos c ht p i).le)
    (singularValues_fderiv_evolution c ht p)
  rw [singularValueFunction_integer_eq_fin_prod _ hk]
  convert h using 1
  ext r
  simp only [Set.mem_range, Set.mem_ofPred_eq, exteriorFactor_eq_prod]
  constructor
  · rintro ⟨s, hs⟩
    exact ⟨s, hs.symm⟩
  · rintro ⟨s, hs⟩
    exact ⟨s, hs.symm⟩

theorem norm_exteriorInitialCoordinates (k : ℕ) (p : PhaseSpace) (v : ExteriorSpace k) :
    ‖exteriorInitialCoordinates k p v‖ = ‖v‖ := by
  rw [exteriorInitialCoordinates, (exteriorBasis k).repr.norm_map,
    norm_exterior_map_isometry]

theorem norm_exteriorEvolution_initialBasis (k : ℕ) (c : ℝ) {t : ℝ}
    (ht : 0 ≤ t) (p : PhaseSpace) (s : ExteriorIndex k) :
    ‖exteriorEvolution k c t p (initialExteriorBasisVector k p s)‖ =
      exteriorFactor k (derivativeFactors c t p) s := by
  classical
  have h := norm_sq_exteriorEvolution k c ht p (initialExteriorBasisVector k p s)
  simp [exteriorInitialCoordinates_basis] at h
  have hp := exteriorFactor_pos k c ht p s
  nlinarith [norm_nonneg (exteriorEvolution k c t p (initialExteriorBasisVector k p s))]

theorem norm_exteriorEvolution_le {k : ℕ} (hk : k ≤ 5) (c : ℝ) {t : ℝ}
    (ht : 0 ≤ t) (p : PhaseSpace) (v : ExteriorSpace k) :
    ‖exteriorEvolution k c t p v‖ ≤
      singularValueFunction (fderiv ℝ (evolution c t) p).toLinearMap k * ‖v‖ := by
  classical
  let M := singularValueFunction (fderiv ℝ (evolution c t) p).toLinearMap k
  obtain ⟨⟨s, hs⟩, hmax⟩ := isGreatest_exteriorFactor hk c ht p
  have hM : 0 ≤ M := by
    dsimp [M]
    rw [← hs]
    exact (exteriorFactor_pos k c ht p s).le
  have hsum : ‖exteriorEvolution k c t p v‖ ^ 2 ≤ M ^ 2 * ‖v‖ ^ 2 := by
    rw [norm_sq_exteriorEvolution k c ht p v,
      ← norm_exteriorInitialCoordinates k p v, EuclideanSpace.real_norm_sq_eq,
      Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hj₀ := (exteriorFactor_pos k c ht p j).le
    have hjM : exteriorFactor k (derivativeFactors c t p) j ≤ M := hmax ⟨j, rfl⟩
    have hsquare : (exteriorFactor k (derivativeFactors c t p) j) ^ 2 ≤ M ^ 2 := by
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hsquare
      (sq_nonneg (exteriorInitialCoordinates k p v j))]
  nlinarith [norm_nonneg (exteriorEvolution k c t p v), norm_nonneg v,
    mul_nonneg hM (norm_nonneg v)]

/-- The integer singular-value product is the operator norm of the exterior power of the ambient derivative, including time zero. -/
theorem norm_exteriorOperator_evolution {k : ℕ} (hk : k ≤ 5) (c : ℝ) {t : ℝ}
    (ht : 0 ≤ t) (p : PhaseSpace) :
    ‖exteriorOperator k (fderiv ℝ (evolution c t) p).toLinearMap‖ =
      singularValueFunction (fderiv ℝ (evolution c t) p).toLinearMap k := by
  obtain ⟨⟨s, hs⟩, hmax⟩ := isGreatest_exteriorFactor hk c ht p
  have hM : 0 ≤ singularValueFunction (fderiv ℝ (evolution c t) p).toLinearMap k := by
    rw [← hs]
    exact (exteriorFactor_pos k c ht p s).le
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ hM
    exact norm_exteriorEvolution_le hk c ht p
  · have h := (exteriorOperator k (fderiv ℝ (evolution c t) p).toLinearMap).le_opNorm
      (initialExteriorBasisVector k p s)
    change ‖exteriorEvolution k c t p (initialExteriorBasisVector k p s)‖ ≤ _ at h
    rwa [norm_exteriorEvolution_initialBasis k c ht p s, norm_initialExteriorBasisVector,
      mul_one, hs] at h

end Eden
