import Eden.DerivativeDecomposition
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.LinearAlgebra.Charpoly.ToMatrix

/-!
# Singular values from the orthogonal factorisation

The singular values here are Mathlib's `LinearMap.singularValues`, defined
through the ordered spectrum of the Gram operator. Characteristic polynomials
retain all multiplicities. The characteristic polynomial identifies these values
with the diagonal factors.

The central reused developments are the adjoint API (Frédéric Dupuis and Heather
Macbeth), the finite-dimensional spectral theorem (Heather Macbeth), and
singular values (Niels Voss and Arnav Mehta).
-/

noncomputable section
open Polynomial
namespace Eden

theorem adjoint_diagonalLinear (d : PhaseSpace) :
    (diagonalLinear d).adjoint = diagonalLinear d := by
  symm
  apply (LinearMap.eq_adjoint_iff _ _).2
  intro x y
  simp [PiLp.inner_apply, mul_comm, mul_left_comm, mul_assoc]

theorem diagonalLinear_comp_self (d : PhaseSpace) :
    diagonalLinear d ∘ₗ diagonalLinear d =
      diagonalLinear (WithLp.toLp 2 (fun i => d i ^ 2)) := by
  ext v i
  simp [pow_two, mul_assoc]

theorem toMatrix_diagonalLinear (d : PhaseSpace) :
    (diagonalLinear d).toMatrix (EuclideanSpace.basisFun (Fin 5) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin 5) ℝ).toBasis = Matrix.diagonal (fun i => d i) := by
  ext i j
  simp [LinearMap.toMatrix_apply, EuclideanSpace.basisFun_apply,
    OrthonormalBasis.coe_toBasis_repr_apply, Matrix.diagonal_apply, PiLp.single_apply]

theorem charpoly_diagonalLinear (d : PhaseSpace) :
    (diagonalLinear d).charpoly = ∏ i : Fin 5, (X - C (d i)) := by
  rw [← (diagonalLinear d).charpoly_toMatrix (EuclideanSpace.basisFun (Fin 5) ℝ).toBasis,
    toMatrix_diagonalLinear, Matrix.charpoly_diagonal]

theorem roots_charpoly_diagonalLinear (d : PhaseSpace) :
    (diagonalLinear d).charpoly.roots = Finset.univ.val.map (fun i => d i) := by
  rw [charpoly_diagonalLinear,
    Polynomial.roots_prod _ _ (by simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero])]
  simp

/-- An orthogonal-diagonal-orthogonal map, with `V` as input frame and `U` as output
frame. Its singular values will be obtained from the Gram spectrum. -/
def orthogonalDiagonalMap (U V : PhaseSpace ≃ₗᵢ[ℝ] PhaseSpace) (d : PhaseSpace) :
    PhaseSpace →ₗ[ℝ] PhaseSpace :=
  U.toLinearMap ∘ₗ diagonalLinear d ∘ₗ V.symm.toLinearMap

theorem gram_orthogonalDiagonalMap (U V : PhaseSpace ≃ₗᵢ[ℝ] PhaseSpace) (d : PhaseSpace) :
    (orthogonalDiagonalMap U V d).adjoint ∘ₗ orthogonalDiagonalMap U V d =
      V.toLinearEquiv.conj (diagonalLinear (WithLp.toLp 2 (fun i => d i ^ 2))) := by
  simp only [orthogonalDiagonalMap, LinearMap.adjoint_comp,
    LinearIsometryEquiv.adjoint_toLinearMap_eq_symm, adjoint_diagonalLinear]
  ext v i
  simp [LinearEquiv.conj_apply_apply, diagonalLinear, pow_two, mul_assoc]

theorem roots_charpoly_gram_orthogonalDiagonalMap
    (U V : PhaseSpace ≃ₗᵢ[ℝ] PhaseSpace) (d : PhaseSpace) :
    ((orthogonalDiagonalMap U V d).adjoint ∘ₗ orthogonalDiagonalMap U V d).charpoly.roots =
      Finset.univ.val.map (fun i : Fin 5 => d i ^ 2) := by
  rw [gram_orthogonalDiagonalMap, LinearEquiv.charpoly_conj, roots_charpoly_diagonalLinear]

/-- The five singular values, with multiplicities, are the nonnegative diagonal
entries of an orthogonal factorisation. No ordering of those entries is assumed. -/
theorem singularValues_orthogonalDiagonalMap
    (U V : PhaseSpace ≃ₗᵢ[ℝ] PhaseSpace) (d : PhaseSpace) (hd : ∀ i, 0 ≤ d i) :
    Finset.univ.val.map (fun i : Fin 5 => (orthogonalDiagonalMap U V d).singularValues i) =
      Finset.univ.val.map (fun i : Fin 5 => d i) := by
  let T := orthogonalDiagonalMap U V d
  have hn : Module.finrank ℝ PhaseSpace = 5 := finrank_euclideanSpace_fin
  have hroots := T.isSymmetric_adjoint_comp_self.roots_charpoly_eq_eigenvalues hn
  have hgram := roots_charpoly_gram_orthogonalDiagonalMap U V d
  have hev : Finset.univ.val.map (fun i : Fin 5 =>
      T.isSymmetric_adjoint_comp_self.eigenvalues hn i) =
      Finset.univ.val.map (fun i : Fin 5 => d i ^ 2) := by
    simpa using hroots.symm.trans hgram
  have hsqrt := congrArg (Multiset.map Real.sqrt) hev
  simpa only [Multiset.map_map, Function.comp_def, ← T.singularValues_fin hn,
    Real.sqrt_sq (hd _)] using hsqrt

/-- The complete multiset of ambient Euclidean singular values of the evolution
derivative, including their multiplicities and all zero-radius cases. -/
theorem singularValues_fderiv_evolution (c : ℝ) {t : ℝ} (ht : 0 ≤ t) (p : PhaseSpace) :
    Finset.univ.val.map (fun i : Fin 5 => (fderiv ℝ (evolution c t) p).toLinearMap.singularValues i) =
      Finset.univ.val.map (fun i : Fin 5 => derivativeFactors c t p i) := by
  have heq : (fderiv ℝ (evolution c t) p).toLinearMap =
      orthogonalDiagonalMap ((radialFrame p).trans (angularRotation t))
        (radialFrame p) (derivativeFactors c t p) := by
    ext v : 1
    have h := fderiv_evolution_radialFrame c ht p ((radialFrame p).symm v)
    simpa [orthogonalDiagonalMap] using h
  rw [heq]
  exact singularValues_orthogonalDiagonalMap _ _ _
    (fun i => le_of_lt (derivativeFactors_pos c ht p i))

end Eden
