import Eden.PlanarDerivative
import Eden.StationaryFactors
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.LinearAlgebra.Charpoly.ToMatrix

/-!
# The two planar singular values

The Gram operator of the planar derivative is orthogonally conjugate to the
squares of the radial and tangential factors. Its characteristic polynomial
retains both multiplicities, including at zero radius.

As in the ambient calculation, this uses Mathlib's adjoint API (Frédéric Dupuis
and Heather Macbeth), spectral theorem (Heather Macbeth) and singular values
(Niels Voss and Arnav Mehta).
-/

noncomputable section
open Polynomial
namespace Eden

theorem adjoint_planarDiagonal (d : PlanarSpace) :
    (planarDiagonal d).adjoint = planarDiagonal d := by
  symm
  apply (LinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  simp [PiLp.inner_apply, mul_comm, mul_left_comm, mul_assoc]

theorem planarDiagonal_comp_self (d : PlanarSpace) :
    planarDiagonal d ∘ₗ planarDiagonal d =
      planarDiagonal (WithLp.toLp 2 (fun i => d i ^ 2)) := by
  ext v i
  simp [pow_two, mul_assoc]

theorem toMatrix_planarDiagonal (d : PlanarSpace) :
    (planarDiagonal d).toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis = Matrix.diagonal (fun i => d i) := by
  ext i j
  simp [LinearMap.toMatrix_apply, EuclideanSpace.basisFun_apply,
    OrthonormalBasis.coe_toBasis_repr_apply, Matrix.diagonal_apply, PiLp.single_apply]

theorem roots_charpoly_planarDiagonal (d : PlanarSpace) :
    (planarDiagonal d).charpoly.roots = Finset.univ.val.map (fun i => d i) := by
  rw [← (planarDiagonal d).charpoly_toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis,
    toMatrix_planarDiagonal, Matrix.charpoly_diagonal,
    Polynomial.roots_prod _ _ (by simp [Polynomial.X_sub_C_ne_zero])]
  simp

/-- Orthogonal factorisation of the derivative at every planar point, with no
restrictions on the real angular frequency. -/
theorem fderiv_planarEvolution_orthogonal_decomposition (Ω : ℝ) {t : ℝ}
    (ht : 0 ≤ t) (p : PlanarSpace) :
    (fderiv ℝ (planarEvolution Ω t) p).toLinearMap =
      ((planarRadialFrame p).trans (planarAngularRotation Ω t)).toLinearMap ∘ₗ
        planarDiagonal (planarFactors t p) ∘ₗ (planarRadialFrame p).symm.toLinearMap := by
  ext v : 1
  have h := fderiv_planarEvolution_radialFrame Ω ht p ((planarRadialFrame p).symm v)
  simpa using h

theorem gram_fderiv_planarEvolution (Ω : ℝ) {t : ℝ} (ht : 0 ≤ t) (p : PlanarSpace) :
    (fderiv ℝ (planarEvolution Ω t) p).toLinearMap.adjoint ∘ₗ
        (fderiv ℝ (planarEvolution Ω t) p).toLinearMap =
      (planarRadialFrame p).toLinearEquiv.conj
        (planarDiagonal (WithLp.toLp 2 (fun i => planarFactors t p i ^ 2))) := by
  rw [fderiv_planarEvolution_orthogonal_decomposition Ω ht p]
  simp only [LinearMap.adjoint_comp, LinearIsometryEquiv.adjoint_toLinearMap_eq_symm,
    adjoint_planarDiagonal]
  ext v i
  simp [LinearEquiv.conj_apply_apply, planarDiagonal, pow_two, mul_assoc]

/-- Both standard Mathlib singular values of the planar derivative, as a multiset,
for every real frequency and every initial point, including zero radius and time
zero. -/
theorem singularValues_fderiv_planarEvolution (Ω : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (p : PlanarSpace) :
    Finset.univ.val.map (fun i : Fin 2 =>
      (fderiv ℝ (planarEvolution Ω t) p).toLinearMap.singularValues i) =
      Finset.univ.val.map (fun i : Fin 2 => planarFactors t p i) := by
  let T := (fderiv ℝ (planarEvolution Ω t) p).toLinearMap
  have hn : Module.finrank ℝ PlanarSpace = 2 := finrank_euclideanSpace_fin
  have hroots := T.isSymmetric_adjoint_comp_self.roots_charpoly_eq_eigenvalues hn
  have hgram : (T.adjoint ∘ₗ T).charpoly.roots =
      Finset.univ.val.map (fun i : Fin 2 => planarFactors t p i ^ 2) := by
    rw [gram_fderiv_planarEvolution Ω ht p, LinearEquiv.charpoly_conj,
      roots_charpoly_planarDiagonal]
  have hev : Finset.univ.val.map (fun i : Fin 2 =>
      T.isSymmetric_adjoint_comp_self.eigenvalues hn i) =
      Finset.univ.val.map (fun i : Fin 2 => planarFactors t p i ^ 2) := by
    simpa using hroots.symm.trans hgram
  have hnonneg (i : Fin 2) : 0 ≤ planarFactors t p i := by
    fin_cases i
    · exact (radialAmplitude_pos ht (add_nonneg (sq_nonneg _) (sq_nonneg _))).le
    · exact (planarAmplitude_pos ht (add_nonneg (sq_nonneg _) (sq_nonneg _))).le
  have hsqrt := congrArg (Multiset.map Real.sqrt) hev
  simpa only [Multiset.map_map, Function.comp_def, ← T.singularValues_fin hn,
    Real.sqrt_sq (hnonneg _)] using hsqrt

/-- The manuscript's planar singular-value formula as the two exponential integrals
along the planar trajectory, with full multiplicities. -/
theorem singularValues_fderiv_planarEvolution_integrals (Ω : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (p : PlanarSpace) :
    Finset.univ.val.map (fun i : Fin 2 =>
      (fderiv ℝ (planarEvolution Ω t) p).toLinearMap.singularValues i) =
      {Real.exp (∫ τ in (0 : ℝ)..t, radialRate
          (planarEvolution Ω τ p 0 ^ 2 + planarEvolution Ω τ p 1 ^ 2)),
       Real.exp (∫ τ in (0 : ℝ)..t, tangentialRate
          (planarEvolution Ω τ p 0 ^ 2 + planarEvolution Ω τ p 1 ^ 2))} := by
  rw [singularValues_fderiv_planarEvolution Ω ht p]
  have hr (f : ℝ → ℝ) :
      (∫ τ in (0 : ℝ)..t, f (planarEvolution Ω τ p 0 ^ 2 + planarEvolution Ω τ p 1 ^ 2)) =
        ∫ τ in (0 : ℝ)..t, f (squaredRadiusEvolution τ (p 0 ^ 2 + p 1 ^ 2)) := by
    apply intervalIntegral.integral_congr
    intro τ hτ
    have hτ₀ : 0 ≤ τ := (Set.uIcc_of_le ht ▸ hτ).1
    change f (planarX Ω τ (p 0) (p 1) ^ 2 + planarY Ω τ (p 0) (p 1) ^ 2) = _
    rw [planar_radius_sq Ω hτ₀]
  rw [hr radialRate, hr tangentialRate]
  have hpos := add_nonneg (sq_nonneg (p 0)) (sq_nonneg (p 1))
  rw [← radialAmplitude_eq_exp_integral ht hpos, ← planarAmplitude_eq_exp_integral ht hpos]
  simp [Fin.univ_succ, planarFactors]

/-- At the planar origin the derivative is the exponential contraction times the
angular rotation, for every real frequency. -/
theorem fderiv_planarEvolution_origin (Ω : ℝ) {t : ℝ} (ht : 0 ≤ t) (v : PlanarSpace) :
    fderiv ℝ (planarEvolution Ω t) 0 v =
      Real.exp (-2 * t) • planarAngularRotation Ω t v := by
  rw [fderiv_planarEvolution_apply Ω ht]
  ext i
  fin_cases i <;> simp [planarDerivativeX, planarDerivativeY, planarAngularRotation,
    rotatePlane, planarAmplitude_at_zero ht, smul_eq_mul] <;> ring

end Eden
