import Eden.PlanarVectorField
import Eden.DerivativeFrames

/-!
# The two-dimensional evolution and its derivative

The angular frequency is any real number. The input frame is orthonormal for the
Euclidean norm, including the Cartesian convention at the origin. The radial and
tangential entries follow from differentiation in Cartesian coordinates.
-/

noncomputable section
namespace Eden

/-- The planar evolution on the real Euclidean plane. -/
def planarEvolution (Ω t : ℝ) (p : PlanarSpace) : PlanarSpace :=
  !₂[planarX Ω t (p 0) (p 1), planarY Ω t (p 0) (p 1)]

@[simp] theorem planarEvolution_zero_time (Ω : ℝ) (p : PlanarSpace) :
    planarEvolution Ω 0 p = p := by
  ext i
  fin_cases i <;> simp [planarEvolution]

theorem hasDerivAt_planarEvolution (Ω : ℝ) {t : ℝ} (ht : 0 ≤ t) (p : PlanarSpace) :
    HasDerivAt (fun τ => planarEvolution Ω τ p)
      (planarVectorField Ω (planarEvolution Ω t p)) t := by
  apply hasDerivAt_euclidean_of_coord
  intro i
  fin_cases i
  · simpa [planarEvolution, planarVectorField] using hasDerivAt_planarX Ω ht (p 0) (p 1)
  · simpa [planarEvolution, planarVectorField] using hasDerivAt_planarY Ω ht (p 0) (p 1)

theorem contDiff_planarEvolution (Ω : ℝ) {t : ℝ} (ht : 0 ≤ t) (n : WithTop ℕ∞) :
    ContDiff ℝ n (planarEvolution Ω t) := by
  have hg : ContDiff ℝ n (fun p : PlanarSpace => planarAmplitude t (p 0 ^ 2 + p 1 ^ 2)) := by
    apply contDiff_iff_contDiffAt.mpr
    intro p
    have hr : ContDiffAt ℝ n (fun p : PlanarSpace => p 0 ^ 2 + p 1 ^ 2) p := by fun_prop
    have h := (contDiffAt_planarAmplitude ht
      (add_nonneg (sq_nonneg (p 0)) (sq_nonneg (p 1))) n).comp p hr
    exact h
  rw [contDiff_piLp]
  intro i
  fin_cases i <;> simp [planarEvolution, planarX, planarY] <;> fun_prop

theorem fderiv_planarEvolution_apply (Ω : ℝ) {t : ℝ} (ht : 0 ≤ t) (p v : PlanarSpace) :
    fderiv ℝ (planarEvolution Ω t) p v =
      !₂[planarDerivativeX Ω t (p 0) (p 1) (v 0) (v 1),
        planarDerivativeY Ω t (p 0) (p 1) (v 0) (v 1)] := by
  have hd := ((contDiff_planarEvolution Ω ht 1).differentiable one_ne_zero p).hasFDerivAt
  have hcoord (i : Fin 2) : fderiv ℝ (fun u => planarEvolution Ω t u i) p v =
      fderiv ℝ (planarEvolution Ω t) p v i := by
    have h := (PiLp.hasFDerivAt_apply 2 (planarEvolution Ω t p) i).comp p hd
    change HasFDerivAt (fun u => planarEvolution Ω t u i) _ p at h
    rw [h.fderiv]
    rfl
  ext i
  rw [← hcoord i]
  fin_cases i
  · simpa [planarEvolution] using fderiv_planarX_apply Ω ht
      (PiLp.hasFDerivAt_apply 2 p 0) (PiLp.hasFDerivAt_apply 2 p 1) v
  · simpa [planarEvolution] using fderiv_planarY_apply Ω ht
      (PiLp.hasFDerivAt_apply 2 p 0) (PiLp.hasFDerivAt_apply 2 p 1) v

/-- The real linear map with matrix [[a,-b],[b,a]]. It is a rotation when a^2+b^2=1,
as required in planeRotation. -/
def rotatePlane (a b : ℝ) (v : PlanarSpace) : PlanarSpace :=
  !₂[a * v 0 - b * v 1, b * v 0 + a * v 1]

theorem rotatePlane_inverse {a b : ℝ} (hab : a ^ 2 + b ^ 2 = 1) (v : PlanarSpace) :
    rotatePlane a (-b) (rotatePlane a b v) = v := by
  have h₀ := congrArg (fun r : ℝ => r * v 0) hab
  have h₁ := congrArg (fun r : ℝ => r * v 1) hab
  ext i
  fin_cases i <;> simp [rotatePlane] <;> nlinarith only [h₀, h₁]

theorem norm_rotatePlane {a b : ℝ} (hab : a ^ 2 + b ^ 2 = 1) (v : PlanarSpace) :
    ‖rotatePlane a b v‖ = ‖v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]
  simp [rotatePlane]
  nlinarith [congrArg (fun r : ℝ => r * ((v 0) ^ 2 + (v 1) ^ 2)) hab]

/-- A Euclidean rotation from its unit cosine-sine pair. -/
def planeRotation (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    PlanarSpace ≃ₗᵢ[ℝ] PlanarSpace where
  toFun := rotatePlane a b
  invFun := rotatePlane a (-b)
  left_inv := rotatePlane_inverse hab
  right_inv := by
    have h : a ^ 2 + (-b) ^ 2 = 1 := by simpa using hab
    intro v
    simpa using rotatePlane_inverse h v
  map_add' := by intro v w; ext i; fin_cases i <;> simp [rotatePlane] <;> ring
  map_smul' := by intro r v; ext i; fin_cases i <;> simp [rotatePlane, smul_eq_mul] <;> ring
  norm_map' := norm_rotatePlane hab

@[simp] theorem planeRotation_apply (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) (v : PlanarSpace) :
    planeRotation a b hab v = rotatePlane a b v := rfl

/-- The unit radial vector and its positive quarter-turn; at the origin the
Cartesian frame is selected. This is always a Euclidean isometry. -/
def planarRadialFrame (p : PlanarSpace) : PlanarSpace ≃ₗᵢ[ℝ] PlanarSpace :=
  planeRotation (radialCos (p 0) (p 1)) (radialSin (p 0) (p 1))
    (radialCos_sq_add_radialSin_sq _ _)

/-- The Euclidean rotation through angle Omega*t. -/
def planarAngularRotation (Ω t : ℝ) : PlanarSpace ≃ₗᵢ[ℝ] PlanarSpace :=
  planeRotation (Real.cos (Ω * t)) (Real.sin (Ω * t))
    (by nlinarith [Real.sin_sq_add_cos_sq (Ω * t)])

/-- The real diagonal linear map with the two prescribed Cartesian entries. -/
def planarDiagonal (d : PlanarSpace) : PlanarSpace →ₗ[ℝ] PlanarSpace where
  toFun v := WithLp.toLp 2 (fun i => d i * v i)
  map_add' := by intro v w; ext i; simp [mul_add]
  map_smul' := by intro r v; ext i; simp [smul_eq_mul]; ring

@[simp] theorem planarDiagonal_apply (d v : PlanarSpace) (i : Fin 2) :
    planarDiagonal d v i = d i * v i := rfl

/-- Radial and tangential entries of the proved planar factorisation. -/
def planarFactors (t : ℝ) (p : PlanarSpace) : PlanarSpace :=
  !₂[radialAmplitude t (p 0 ^ 2 + p 1 ^ 2), planarAmplitude t (p 0 ^ 2 + p 1 ^ 2)]

theorem fderiv_planarEvolution_radialFrame (Ω : ℝ) {t : ℝ} (ht : 0 ≤ t) (p v : PlanarSpace) :
    fderiv ℝ (planarEvolution Ω t) p (planarRadialFrame p v) =
      planarAngularRotation Ω t (planarRadialFrame p (planarDiagonal (planarFactors t p) v)) := by
  have hsq := Real.sq_sqrt (add_nonneg (sq_nonneg (p 0)) (sq_nonneg (p 1)))
  have hx := planarDerivativeX_on_radialFrame Ω ht
    (radialCos (p 0) (p 1)) (radialSin (p 0) (p 1))
    (Real.sqrt (p 0 ^ 2 + p 1 ^ 2)) (v 0) (v 1) (radialCos_sq_add_radialSin_sq _ _)
  have hy := planarDerivativeY_on_radialFrame Ω ht
    (radialCos (p 0) (p 1)) (radialSin (p 0) (p 1))
    (Real.sqrt (p 0 ^ 2 + p 1 ^ 2)) (v 0) (v 1) (radialCos_sq_add_radialSin_sq _ _)
  simp only [radius_mul_radialCos, radius_mul_radialSin, hsq] at hx hy
  rw [fderiv_planarEvolution_apply Ω ht]
  ext i
  fin_cases i
  · simpa [planarRadialFrame, planarAngularRotation, rotatePlane, planarDiagonal,
      planarFactors, mul_comm] using hx
  · simpa [planarRadialFrame, planarAngularRotation, rotatePlane, planarDiagonal,
      planarFactors, mul_comm] using hy

end Eden
