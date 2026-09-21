import Eden.VectorFieldDerivative

/-!
# The arbitrary-frequency planar Cartesian Jacobian

Both domain and range are two-dimensional real Euclidean spaces. The matrix
identity is obtained from the derivative in the standard orthonormal basis and
retains every initial point and every real frequency.
-/

noncomputable section
namespace Eden

/-- The real Euclidean plane underlying a complex planar coordinate. -/
abbrev PlanarSpace := EuclideanSpace ℝ (Fin 2)

/-- The planar polynomial equation with arbitrary real frequency. -/
def planarVectorField (Ω : ℝ) (p : PlanarSpace) : PlanarSpace :=
  !₂[q (p 0 ^ 2 + p 1 ^ 2) * p 0 - Ω * p 1,
    q (p 0 ^ 2 + p 1 ^ 2) * p 1 + Ω * p 0]

theorem contDiff_planarVectorField (Ω : ℝ) (n : WithTop ℕ∞) :
    ContDiff ℝ n (planarVectorField Ω) := by
  rw [contDiff_piLp]
  intro i
  fin_cases i <;> simp [planarVectorField, q] <;> fun_prop

theorem fderiv_planarVectorField_apply (Ω : ℝ) (p v : PlanarSpace) :
    fderiv ℝ (planarVectorField Ω) p v =
      !₂[q (p 0 ^ 2 + p 1 ^ 2) * v 0 + 2 * deriv q (p 0 ^ 2 + p 1 ^ 2) *
          (p 0 * v 0 + p 1 * v 1) * p 0 - Ω * v 1,
        q (p 0 ^ 2 + p 1 ^ 2) * v 1 + 2 * deriv q (p 0 ^ 2 + p 1 ^ 2) *
          (p 0 * v 0 + p 1 * v 1) * p 1 + Ω * v 0] := by
  have hd := ((contDiff_planarVectorField Ω 1).differentiable one_ne_zero p).hasFDerivAt
  have hcoord (i : Fin 2) : fderiv ℝ (fun u => planarVectorField Ω u i) p v =
      fderiv ℝ (planarVectorField Ω) p v i := by
    have h := (PiLp.hasFDerivAt_apply 2 (planarVectorField Ω p) i).comp p hd
    change HasFDerivAt (fun u => planarVectorField Ω u i) _ p at h
    rw [h.fderiv]
    rfl
  ext i
  rw [← hcoord i]
  fin_cases i
  · simpa [planarVectorField] using fderiv_planarVectorX_apply Ω
      (PiLp.hasFDerivAt_apply 2 p 0) (PiLp.hasFDerivAt_apply 2 p 1) v
  · simpa [planarVectorField] using fderiv_planarVectorY_apply Ω
      (PiLp.hasFDerivAt_apply 2 p 0) (PiLp.hasFDerivAt_apply 2 p 1) v

/-- The standard real two-dimensional Jacobian q(s)I+2q'(s)vv^T+Omega J, as the
matrix of the derivative, including the origin. -/
theorem toMatrix_fderiv_planarVectorField (Ω : ℝ) (p : PlanarSpace) :
    (fderiv ℝ (planarVectorField Ω) p).toLinearMap.toMatrix
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis =
      q (p 0 ^ 2 + p 1 ^ 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        (2 * deriv q (p 0 ^ 2 + p 1 ^ 2)) •
          Matrix.vecMulVec (fun i => p i) (fun i => p i) +
        Ω • !![0, -1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [LinearMap.toMatrix_apply, EuclideanSpace.basisFun_apply,
      OrthonormalBasis.coe_toBasis_repr_apply,
      fderiv_planarVectorField_apply, Matrix.vecMulVec] <;> ring

end Eden
