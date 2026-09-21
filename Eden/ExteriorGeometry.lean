import Eden.DerivativeDecomposition
import Mathlib.Analysis.InnerProductSpace.ExteriorPower

/-!
# Exterior powers of the Euclidean derivative

The exterior spaces carry Mathlib's canonical Gram-determinant inner product
(Justus Springer). The algebraic basis API is due to Sophie Morel and Daniel
Morrison; the induced-map API is due to Sophie Morel and Joël Riou.
-/

noncomputable section
namespace Eden

/-- The canonical real exterior power of the ambient Euclidean space. -/
abbrev ExteriorSpace (k : ℕ) := ⋀[ℝ]^k PhaseSpace

/-- Indices for the standard orthonormal exterior basis. -/
abbrev ExteriorIndex (k : ℕ) := Set.powersetCard (Fin 5) k

/-- The induced map on exterior powers of the ambient derivative. -/
def exteriorEvolution (k : ℕ) (c t : ℝ) (p : PhaseSpace) :
    ExteriorSpace k →ₗ[ℝ] ExteriorSpace k :=
  exteriorPower.map k (fderiv ℝ (evolution c t) p).toLinearMap

/-- The standard Euclidean orthonormal basis lifted to exterior degree k. -/
def exteriorBasis (k : ℕ) : OrthonormalBasis (ExteriorIndex k) ℝ (ExteriorSpace k) :=
  (EuclideanSpace.basisFun (Fin 5) ℝ).exteriorPower k

theorem exteriorBasis_apply (k : ℕ) (s : ExteriorIndex k) :
    exteriorBasis k s = exteriorPower.ιMulti_family ℝ k
      (EuclideanSpace.basisFun (Fin 5) ℝ) s := by
  change ((EuclideanSpace.basisFun (Fin 5) ℝ).exteriorPower k).toBasis s = _
  rw [OrthonormalBasis.toBasis_exteriorPower, exteriorPower.basis_apply]
  rfl

/-- The product of the diagonal entries selected by an exterior basis index. -/
def exteriorFactor (k : ℕ) (d : PhaseSpace) (s : ExteriorIndex k) : ℝ :=
  ∏ i : Fin k, d (Set.powersetCard.ofFinEmbEquiv.symm s i)

theorem diagonalLinear_basis (d : PhaseSpace) (j : Fin 5) :
    diagonalLinear d (EuclideanSpace.basisFun (Fin 5) ℝ j) =
      d j • EuclideanSpace.basisFun (Fin 5) ℝ j := by
  ext i
  simp [EuclideanSpace.basisFun_apply, PiLp.single_apply, smul_eq_mul]
  split_ifs with h
  · subst i
    rfl
  · simp

theorem exterior_map_diagonal_basis (k : ℕ) (d : PhaseSpace) (s : ExteriorIndex k) :
    exteriorPower.map k (diagonalLinear d) (exteriorBasis k s) =
      exteriorFactor k d s • exteriorBasis k s := by
  change exteriorPower.map k (diagonalLinear d)
      (((EuclideanSpace.basisFun (Fin 5) ℝ).exteriorPower k).toBasis s) = _
  simp only [OrthonormalBasis.toBasis_exteriorPower, exteriorPower.basis_apply,
    exteriorPower.ιMulti_family, exteriorPower.map_apply_ιMulti, Function.comp_def,
    OrthonormalBasis.coe_toBasis]
  simp_rw [diagonalLinear_basis]
  rw [AlternatingMap.map_smul_univ]
  rw [exteriorBasis_apply, exteriorPower.ιMulti_family]
  rfl

/-- The exterior map of a Euclidean isometry preserves the canonical
exterior norm, in every exterior degree, including zero and degrees above 5. -/
theorem norm_exterior_map_isometry (k : ℕ) (U : PhaseSpace ≃ₗᵢ[ℝ] PhaseSpace)
    (v : ExteriorSpace k) : ‖exteriorPower.map k U.toLinearMap v‖ = ‖v‖ := by
  let b := EuclideanSpace.basisFun (Fin 5) ℝ
  let B := b.exteriorPower k
  let C := (b.map U).exteriorPower k
  let V := B.equiv C (Equiv.refl _)
  have hm : exteriorPower.map k U.toLinearMap = V.toLinearMap := by
    apply B.toBasis.ext
    intro s
    change exteriorPower.map k U.toLinearMap (B s) = V (B s)
    rw [OrthonormalBasis.equiv_apply_basis]
    change exteriorPower.map k U.toLinearMap (B.toBasis s) = C.toBasis s
    simp only [B, C, OrthonormalBasis.toBasis_exteriorPower, exteriorPower.basis_apply,
      exteriorPower.map_apply_ιMulti_family, OrthonormalBasis.coe_toBasis]
    rfl
  rw [hm]
  exact V.norm_map v

theorem exterior_map_diagonal_repr (k : ℕ) (d : PhaseSpace) (v : ExteriorSpace k)
    (s : ExteriorIndex k) :
    (exteriorBasis k).repr (exteriorPower.map k (diagonalLinear d) v) s =
      exteriorFactor k d s * (exteriorBasis k).repr v s := by
  classical
  conv_lhs => arg 1; rw [← (exteriorBasis k).sum_repr v]
  simp [map_sum, exterior_map_diagonal_basis, Pi.single_apply, mul_comm]

/-- Squared norm of a diagonal exterior map in the canonical norm. -/
theorem norm_sq_exterior_map_diagonal (k : ℕ) (d : PhaseSpace) (v : ExteriorSpace k) :
    ‖exteriorPower.map k (diagonalLinear d) v‖ ^ 2 =
      ∑ s : ExteriorIndex k, (exteriorFactor k d s * (exteriorBasis k).repr v s) ^ 2 := by
  rw [← (exteriorBasis k).repr.norm_map, EuclideanSpace.real_norm_sq_eq]
  simp only [exterior_map_diagonal_repr]

/-- The fixed input-frame coordinates of an exterior vector. This frame
depends on the initial point, but not on time. -/
def exteriorInitialCoordinates (k : ℕ) (p : PhaseSpace) (v : ExteriorSpace k) :
    EuclideanSpace ℝ (ExteriorIndex k) :=
  (exteriorBasis k).repr (exteriorPower.map k (radialFrame p).symm.toLinearMap v)

/-- The full norm formula for every fixed exterior vector under the derivative; its nonnegative terms retain all coefficients and multiplicities. -/
theorem norm_sq_exteriorEvolution (k : ℕ) (c : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (p : PhaseSpace) (v : ExteriorSpace k) :
    ‖exteriorEvolution k c t p v‖ ^ 2 = ∑ s : ExteriorIndex k,
      (exteriorFactor k (derivativeFactors c t p) s * exteriorInitialCoordinates k p v s) ^ 2 := by
  unfold exteriorEvolution
  rw [fderiv_evolution_orthogonal_decomposition c ht p]
  simp only [exteriorPower.map_comp, LinearMap.comp_apply]
  rw [norm_exterior_map_isometry k (angularRotation t),
    norm_exterior_map_isometry k (radialFrame p), norm_sq_exterior_map_diagonal]
  rfl

theorem exteriorInitialCoordinates_ne_zero {k : ℕ} (p : PhaseSpace)
    {v : ExteriorSpace k} (hv : v ≠ 0) : exteriorInitialCoordinates k p v ≠ 0 := by
  intro h
  have hz : exteriorPower.map k (radialFrame p).symm.toLinearMap v = 0 :=
    (exteriorBasis k).repr.injective (h.trans (map_zero _).symm)
  have hn := norm_exterior_map_isometry k (radialFrame p).symm v
  rw [hz, norm_zero] at hn
  exact hv (norm_eq_zero.mp hn.symm)

end Eden
