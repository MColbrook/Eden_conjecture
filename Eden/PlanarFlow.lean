import Eden.ScalarCalculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Cartesian planar solutions

For every real angular frequency, the explicit positive amplitude and ordinary
Euclidean rotation yield a solution of the planar polynomial equation in
Colbrook's construction. The origin is included in the same formula.

Trigonometric differentiation and the rotation identity use Mathlib's real sine
and cosine API. The amplitude identities come from `Eden.ScalarCalculus`.
-/

noncomputable section
namespace Eden

/-- First real coordinate of the planar solution with initial point `(x,y)`. -/
def planarX (Ω t x y : ℝ) : ℝ :=
  planarAmplitude t (x ^ 2 + y ^ 2) *
    (x * Real.cos (Ω * t) - y * Real.sin (Ω * t))

/-- Second real coordinate of the planar solution with initial point `(x,y)`. -/
def planarY (Ω t x y : ℝ) : ℝ :=
  planarAmplitude t (x ^ 2 + y ^ 2) *
    (x * Real.sin (Ω * t) + y * Real.cos (Ω * t))

@[simp] theorem planarX_zero_time (Ω x y : ℝ) : planarX Ω 0 x y = x := by
  simp [planarX]

@[simp] theorem planarY_zero_time (Ω x y : ℝ) : planarY Ω 0 x y = y := by
  simp [planarY]

@[simp] theorem planarX_origin (Ω t : ℝ) : planarX Ω t 0 0 = 0 := by
  simp [planarX]

@[simp] theorem planarY_origin (Ω t : ℝ) : planarY Ω t 0 0 = 0 := by
  simp [planarY]

/-- The Cartesian solution has the squared radius given by the scalar equation. -/
theorem planar_radius_sq_of_pos (Ω : ℝ) {t x y : ℝ}
    (hD : 0 < radialDiscriminant t (x ^ 2 + y ^ 2))
    (hB : 0 < amplitudeSq t (x ^ 2 + y ^ 2)) :
    planarX Ω t x y ^ 2 + planarY Ω t x y ^ 2 =
      squaredRadiusEvolution t (x ^ 2 + y ^ 2) := by
  have hsq : planarAmplitude t (x ^ 2 + y ^ 2) ^ 2 = amplitudeSq t (x ^ 2 + y ^ 2) :=
    Real.sq_sqrt hB.le
  calc
    planarX Ω t x y ^ 2 + planarY Ω t x y ^ 2 =
        (x ^ 2 + y ^ 2) * planarAmplitude t (x ^ 2 + y ^ 2) ^ 2 *
          (Real.sin (Ω * t) ^ 2 + Real.cos (Ω * t) ^ 2) := by
      unfold planarX planarY
      ring
    _ = (x ^ 2 + y ^ 2) * amplitudeSq t (x ^ 2 + y ^ 2) := by
      rw [Real.sin_sq_add_cos_sq, mul_one, hsq]
    _ = squaredRadiusEvolution t (x ^ 2 + y ^ 2) := mul_amplitudeSq_of_discriminant_pos hD

theorem planar_radius_sq (Ω : ℝ) {t : ℝ} (ht : 0 ≤ t) (x y : ℝ) :
    planarX Ω t x y ^ 2 + planarY Ω t x y ^ 2 =
      squaredRadiusEvolution t (x ^ 2 + y ^ 2) :=
  planar_radius_sq_of_pos Ω (radialDiscriminant_pos ht _)
    (amplitudeSq_pos ht (add_nonneg (sq_nonneg x) (sq_nonneg y)))

/-- The first Cartesian coordinate satisfies the planar vector field. -/
theorem hasDerivAt_planarX_of_pos (Ω : ℝ) {t x y : ℝ}
    (hD : 0 < radialDiscriminant t (x ^ 2 + y ^ 2))
    (hB : 0 < amplitudeSq t (x ^ 2 + y ^ 2)) :
    HasDerivAt (fun τ => planarX Ω τ x y)
      (q (planarX Ω t x y ^ 2 + planarY Ω t x y ^ 2) * planarX Ω t x y -
        Ω * planarY Ω t x y) t := by
  have hc := ((hasDerivAt_id t).const_mul Ω).cos
  have hsn := ((hasDerivAt_id t).const_mul Ω).sin
  have hrot := (hc.const_mul x).sub (hsn.const_mul y)
  apply ((hasDerivAt_planarAmplitude_of_pos hD hB).mul hrot).congr_deriv
  rw [planar_radius_sq_of_pos Ω hD hB]
  dsimp [planarX, planarY]
  ring

theorem hasDerivAt_planarX (Ω : ℝ) {t : ℝ} (ht : 0 ≤ t) (x y : ℝ) :
    HasDerivAt (fun τ => planarX Ω τ x y)
      (q (planarX Ω t x y ^ 2 + planarY Ω t x y ^ 2) * planarX Ω t x y -
        Ω * planarY Ω t x y) t :=
  hasDerivAt_planarX_of_pos Ω (radialDiscriminant_pos ht _)
    (amplitudeSq_pos ht (add_nonneg (sq_nonneg x) (sq_nonneg y)))

/-- The second Cartesian coordinate satisfies the planar vector field. -/
theorem hasDerivAt_planarY_of_pos (Ω : ℝ) {t x y : ℝ}
    (hD : 0 < radialDiscriminant t (x ^ 2 + y ^ 2))
    (hB : 0 < amplitudeSq t (x ^ 2 + y ^ 2)) :
    HasDerivAt (fun τ => planarY Ω τ x y)
      (q (planarX Ω t x y ^ 2 + planarY Ω t x y ^ 2) * planarY Ω t x y +
        Ω * planarX Ω t x y) t := by
  have hc := ((hasDerivAt_id t).const_mul Ω).cos
  have hsn := ((hasDerivAt_id t).const_mul Ω).sin
  have hrot := (hsn.const_mul x).add (hc.const_mul y)
  apply ((hasDerivAt_planarAmplitude_of_pos hD hB).mul hrot).congr_deriv
  rw [planar_radius_sq_of_pos Ω hD hB]
  dsimp [planarX, planarY]
  ring
theorem hasDerivAt_planarY (Ω : ℝ) {t : ℝ} (ht : 0 ≤ t) (x y : ℝ) :
    HasDerivAt (fun τ => planarY Ω τ x y)
      (q (planarX Ω t x y ^ 2 + planarY Ω t x y ^ 2) * planarY Ω t x y +
        Ω * planarX Ω t x y) t :=
  hasDerivAt_planarY_of_pos Ω (radialDiscriminant_pos ht _)
    (amplitudeSq_pos ht (add_nonneg (sq_nonneg x) (sq_nonneg y)))


end Eden
