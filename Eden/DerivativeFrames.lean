import Eden.CartesianDerivative
import Eden.GrowthRates
import Eden.OrthogonalFrames

/-!
# Radial orthonormal frames for the derivative

At a nonzero planar point the first frame vector is the unit radial vector
and the second is its positive quarter-turn. At zero the Cartesian frame is
chosen. This convention covers the entire ambient phase space.
-/

noncomputable section
namespace Eden

/-- First component of the radial unit vector; at the origin it is one. -/
def radialCos (x y : ℝ) : ℝ :=
  if x ^ 2 + y ^ 2 = 0 then 1 else x / Real.sqrt (x ^ 2 + y ^ 2)

/-- Second component of the radial unit vector; at the origin it is zero. -/
def radialSin (x y : ℝ) : ℝ :=
  if x ^ 2 + y ^ 2 = 0 then 0 else y / Real.sqrt (x ^ 2 + y ^ 2)

theorem radialCos_sq_add_radialSin_sq (x y : ℝ) :
    radialCos x y ^ 2 + radialSin x y ^ 2 = 1 := by
  by_cases h : x ^ 2 + y ^ 2 = 0
  · simp [radialCos, radialSin, h]
  have hr : 0 < Real.sqrt (x ^ 2 + y ^ 2) :=
    Real.sqrt_pos.2 (lt_of_le_of_ne (add_nonneg (sq_nonneg _) (sq_nonneg _)) (Ne.symm h))
  have hsq := Real.sq_sqrt (add_nonneg (sq_nonneg x) (sq_nonneg y))
  simp only [radialCos, radialSin, if_neg h]
  field_simp [ne_of_gt hr]
  nlinarith

theorem radius_mul_radialCos (x y : ℝ) :
    Real.sqrt (x ^ 2 + y ^ 2) * radialCos x y = x := by
  by_cases h : x ^ 2 + y ^ 2 = 0
  · have hx : x = 0 := by nlinarith [sq_nonneg y]
    simp only [radialCos, h, Real.sqrt_zero, zero_mul]
    exact hx.symm
  have hr : Real.sqrt (x ^ 2 + y ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2
      (lt_of_le_of_ne (add_nonneg (sq_nonneg _) (sq_nonneg _)) (Ne.symm h)))
  simp only [radialCos, if_neg h]
  field_simp [hr]

theorem radius_mul_radialSin (x y : ℝ) :
    Real.sqrt (x ^ 2 + y ^ 2) * radialSin x y = y := by
  by_cases h : x ^ 2 + y ^ 2 = 0
  · have hy : y = 0 := by nlinarith [sq_nonneg x]
    simp only [radialSin, if_pos h, mul_zero]
    exact hy.symm
  have hr : Real.sqrt (x ^ 2 + y ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2
      (lt_of_le_of_ne (add_nonneg (sq_nonneg _) (sq_nonneg _)) (Ne.symm h)))
  simp only [radialSin, if_neg h]
  field_simp [hr]

/-- Radial and tangential input frames in each plane, with the fifth unit
vector fixed. This is a Euclidean linear isometry, including at zero radii. -/
def radialFrame (p : PhaseSpace) : PhaseSpace ≃ₗᵢ[ℝ] PhaseSpace :=
  blockRotation (radialCos (p 0) (p 1)) (radialSin (p 0) (p 1))
    (radialCos (p 2) (p 3)) (radialSin (p 2) (p 3))
    (radialCos_sq_add_radialSin_sq _ _) (radialCos_sq_add_radialSin_sq _ _)

/-- Angular evolution of the two planar frames. -/
def angularRotation (t : ℝ) : PhaseSpace ≃ₗᵢ[ℝ] PhaseSpace :=
  blockRotation (Real.cos t) (Real.sin t)
    (Real.cos (Real.sqrt 2 * t)) (Real.sin (Real.sqrt 2 * t))
    (by nlinarith [Real.sin_sq_add_cos_sq t])
    (by nlinarith [Real.sin_sq_add_cos_sq (Real.sqrt 2 * t)])

theorem planarDerivativeX_on_radialFrame (Ω : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (a b r u v : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    planarDerivativeX Ω t (r * a) (r * b) (a * u - b * v) (b * u + a * v) =
      (a * (radialAmplitude t (r ^ 2) * u) - b * (planarAmplitude t (r ^ 2) * v)) *
          Real.cos (Ω * t) -
        (b * (radialAmplitude t (r ^ 2) * u) + a * (planarAmplitude t (r ^ 2) * v)) *
          Real.sin (Ω * t) := by
  have hs : (r * a) ^ 2 + (r * b) ^ 2 = r ^ 2 := by
    nlinarith [congrArg (fun k : ℝ => r ^ 2 * k) hab]
  have hi : r * a * (a * u - b * v) + r * b * (b * u + a * v) = r * u := by
    nlinarith [congrArg (fun k : ℝ => r * u * k) hab]
  rw [planarDerivativeX, hs, hi, ← planarAmplitude_parameter_identity ht (sq_nonneg r)]
  ring

theorem planarDerivativeY_on_radialFrame (Ω : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (a b r u v : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    planarDerivativeY Ω t (r * a) (r * b) (a * u - b * v) (b * u + a * v) =
      (a * (radialAmplitude t (r ^ 2) * u) - b * (planarAmplitude t (r ^ 2) * v)) *
          Real.sin (Ω * t) +
        (b * (radialAmplitude t (r ^ 2) * u) + a * (planarAmplitude t (r ^ 2) * v)) *
          Real.cos (Ω * t) := by
  have hs : (r * a) ^ 2 + (r * b) ^ 2 = r ^ 2 := by
    nlinarith [congrArg (fun k : ℝ => r ^ 2 * k) hab]
  have hi : r * a * (a * u - b * v) + r * b * (b * u + a * v) = r * u := by
    nlinarith [congrArg (fun k : ℝ => r * u * k) hab]
  rw [planarDerivativeY, hs, hi, ← planarAmplitude_parameter_identity ht (sq_nonneg r)]
  ring

end Eden
