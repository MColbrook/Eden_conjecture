import Eden.ExteriorOperatorNorm

/-!
# Exterior powers and the Gram operator of an arbitrary ambient map

The determinant formula for the canonical exterior inner product transports
the adjoint identity to exterior powers. Mathlib's spectral theorem for the
positive Gram operator then gives an exact norm formula, even when the
original map is singular. The eigenbasis API is due to Heather Macbeth;
the canonical exterior inner product is due to Justus Springer.
-/

noncomputable section
open scoped RealInnerProductSpace
namespace Eden

/-- The Gram identity for the exterior map, without invertibility. -/
theorem inner_exterior_map_gram (k : ℕ) (A : PhaseSpace →ₗ[ℝ] PhaseSpace)
    (v w : ExteriorSpace k) :
    ⟪exteriorPower.map k A v, exteriorPower.map k A w⟫ =
      ⟪v, exteriorPower.map k (A.adjoint ∘ₗ A) w⟫ := by
  classical
  have hb (s r : ExteriorIndex k) :
      ⟪exteriorPower.map k A (exteriorBasis k s),
        exteriorPower.map k A (exteriorBasis k r)⟫ =
      ⟪exteriorBasis k s, exteriorPower.map k (A.adjoint ∘ₗ A) (exteriorBasis k r)⟫ := by
    simp only [exteriorBasis_apply, exteriorPower.ιMulti_family,
      exteriorPower.map_apply_ιMulti, exteriorPower.inner_ιMulti_ιMulti,
      Function.comp_def, LinearMap.comp_apply, LinearMap.adjoint_inner_right]
  rw [← (exteriorBasis k).sum_repr v, ← (exteriorBasis k).sum_repr w]
  simp only [map_sum, map_smul, sum_inner, inner_sum]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro s hs
  have hleft (r : ℝ) (x y : ExteriorSpace k) : ⟪r • x, y⟫ = r * ⟪x, y⟫ :=
    real_inner_smul_left x y r
  have hright (r : ℝ) (x y : ExteriorSpace k) : ⟪x, r • y⟫ = r * ⟪x, y⟫ :=
    real_inner_smul_right x y r
  simp only [hleft, hright, hb]

/-- The orthonormal eigenbasis of A* A, ordered by its eigenvalues. -/
def singularVectorBasis (A : PhaseSpace →ₗ[ℝ] PhaseSpace) :
    OrthonormalBasis (Fin 5) ℝ PhaseSpace :=
  A.isSymmetric_adjoint_comp_self.eigenvectorBasis (finrank_euclideanSpace_fin)

/-- Exterior orthonormal basis lifted from the Gram eigenbasis. It depends
on A; if A varies in time this is not a fixed initial frame. -/
def singularExteriorBasis (k : ℕ) (A : PhaseSpace →ₗ[ℝ] PhaseSpace) :
    OrthonormalBasis (ExteriorIndex k) ℝ (ExteriorSpace k) :=
  (singularVectorBasis A).exteriorPower k

theorem singularExteriorBasis_apply (k : ℕ) (A : PhaseSpace →ₗ[ℝ] PhaseSpace)
    (s : ExteriorIndex k) : singularExteriorBasis k A s =
      exteriorPower.ιMulti_family ℝ k (singularVectorBasis A) s := by
  change ((singularVectorBasis A).exteriorPower k).toBasis s = _
  rw [OrthonormalBasis.toBasis_exteriorPower, exteriorPower.basis_apply]
  rfl

/-- The selected product of singular values, with all multiplicities. -/
def selectedSingularProduct (k : ℕ) (A : PhaseSpace →ₗ[ℝ] PhaseSpace)
    (s : ExteriorIndex k) : ℝ :=
  ∏ i : Fin k, A.singularValues (Set.powersetCard.ofFinEmbEquiv.symm s i)

theorem selectedSingularProduct_nonneg (k : ℕ) (A : PhaseSpace →ₗ[ℝ] PhaseSpace)
    (s : ExteriorIndex k) : 0 ≤ selectedSingularProduct k A s :=
  Finset.prod_nonneg (fun _i _ => A.singularValues_nonneg _)

theorem selectedSingularProduct_eq_prod (k : ℕ) (A : PhaseSpace →ₗ[ℝ] PhaseSpace)
    (s : ExteriorIndex k) : selectedSingularProduct k A s = ∏ j ∈ s.val, A.singularValues j := by
  change exteriorFactor k (WithLp.toLp 2 (fun i : Fin 5 => A.singularValues i)) s = _
  exact exteriorFactor_eq_prod k _ s

theorem gram_singularVectorBasis (A : PhaseSpace →ₗ[ℝ] PhaseSpace) (i : Fin 5) :
    (A.adjoint ∘ₗ A) (singularVectorBasis A i) =
      A.singularValues i ^ 2 • singularVectorBasis A i := by
  rw [A.sq_singularValues_fin finrank_euclideanSpace_fin i]
  exact A.isSymmetric_adjoint_comp_self.apply_eigenvectorBasis _ i

theorem exterior_gram_basis (k : ℕ) (A : PhaseSpace →ₗ[ℝ] PhaseSpace)
    (s : ExteriorIndex k) :
    exteriorPower.map k (A.adjoint ∘ₗ A) (singularExteriorBasis k A s) =
      selectedSingularProduct k A s ^ 2 • singularExteriorBasis k A s := by
  change exteriorPower.map k (A.adjoint ∘ₗ A)
      (((singularVectorBasis A).exteriorPower k).toBasis s) = _
  simp only [OrthonormalBasis.toBasis_exteriorPower, exteriorPower.basis_apply,
    exteriorPower.ιMulti_family, exteriorPower.map_apply_ιMulti, Function.comp_def,
    OrthonormalBasis.coe_toBasis]
  simp_rw [gram_singularVectorBasis]
  rw [AlternatingMap.map_smul_univ, Finset.prod_pow]
  rw [singularExteriorBasis_apply, exteriorPower.ιMulti_family]
  rfl

/-- Exact squared norm for all exterior vectors and every ambient linear map,
including maps of deficient rank and zero selected products. -/
theorem norm_sq_exterior_map_singular_basis (k : ℕ) (A : PhaseSpace →ₗ[ℝ] PhaseSpace)
    (v : ExteriorSpace k) :
    ‖exteriorPower.map k A v‖ ^ 2 = ∑ s : ExteriorIndex k,
      (selectedSingularProduct k A s * (singularExteriorBasis k A).repr v s) ^ 2 := by
  classical
  rw [← real_inner_self_eq_norm_sq, inner_exterior_map_gram]
  conv_lhs => arg 3; rw [← (singularExteriorBasis k A).sum_repr v]
  simp only [map_sum, map_smul, exterior_gram_basis, inner_sum,
    real_inner_smul_right, smul_smul]
  apply Finset.sum_congr rfl
  intro s hs
  have hi : ⟪v, singularExteriorBasis k A s⟫ = (singularExteriorBasis k A).repr v s := by
    rw [OrthonormalBasis.repr_apply_apply]
    exact real_inner_comm _ _
  rw [hi]
  ring

end Eden
