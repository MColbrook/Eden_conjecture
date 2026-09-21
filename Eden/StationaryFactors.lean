import Eden.DerivativeDecomposition

/-!
# Derivative factors at the stationary radii

These formulas follow from the proved integral expressions and the stationary
squared-radius solutions. They cover nonnegative time, including time zero. The
origin formulas also give the Cartesian derivative there.
-/

noncomputable section
namespace Eden

theorem planarAmplitude_at_zero {t : ℝ} (ht : 0 ≤ t) :
    planarAmplitude t 0 = Real.exp (-2 * t) := by
  rw [planarAmplitude_eq_exp_integral ht (by norm_num)]
  simp [tangentialRate, mul_comm]

theorem radialAmplitude_at_zero {t : ℝ} (ht : 0 ≤ t) :
    radialAmplitude t 0 = Real.exp (-2 * t) := by
  rw [radialAmplitude_eq_exp_integral ht (by norm_num)]
  simp [radialRate, mul_comm]

theorem planarAmplitude_at_one {t : ℝ} (ht : 0 ≤ t) : planarAmplitude t 1 = 1 := by
  rw [planarAmplitude_eq_exp_integral ht (by norm_num)]
  simp [tangentialRate]
  ring

theorem radialAmplitude_at_one {t : ℝ} (ht : 0 ≤ t) :
    radialAmplitude t 1 = Real.exp (2 * t) := by
  rw [radialAmplitude_eq_exp_integral ht (by norm_num)]
  norm_num [radialRate, mul_comm]

theorem planarAmplitude_at_two {t : ℝ} (ht : 0 ≤ t) : planarAmplitude t 2 = 1 := by
  rw [planarAmplitude_eq_exp_integral ht (by norm_num)]
  norm_num [tangentialRate]

theorem radialAmplitude_at_two {t : ℝ} (ht : 0 ≤ t) :
    radialAmplitude t 2 = Real.exp (-4 * t) := by
  rw [radialAmplitude_eq_exp_integral ht (by norm_num)]
  norm_num [radialRate, mul_comm]

theorem planarDerivativeX_at_origin (Ω : ℝ) {t : ℝ} (ht : 0 ≤ t) (dx dy : ℝ) :
    planarDerivativeX Ω t 0 0 dx dy =
      Real.exp (-2 * t) * (dx * Real.cos (Ω * t) - dy * Real.sin (Ω * t)) := by
  simp [planarDerivativeX, planarAmplitude_at_zero ht]

theorem planarDerivativeY_at_origin (Ω : ℝ) {t : ℝ} (ht : 0 ≤ t) (dx dy : ℝ) :
    planarDerivativeY Ω t 0 0 dx dy =
      Real.exp (-2 * t) * (dx * Real.sin (Ω * t) + dy * Real.cos (Ω * t)) := by
  simp [planarDerivativeY, planarAmplitude_at_zero ht]

theorem derivativeFactors_at_origin (c : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    derivativeFactors c t 0 =
      !₂[Real.exp (-2 * t), Real.exp (-2 * t), Real.exp (-2 * t),
         Real.exp (-2 * t), Real.exp (-c * t)] := by
  ext i
  fin_cases i <;> simp [derivativeFactors, radiusSq₁, radiusSq₂,
    planarAmplitude_at_zero ht, radialAmplitude_at_zero ht]

theorem derivativeFactors_on_torus (c : ℝ) {t : ℝ} (ht : 0 ≤ t) {p : PhaseSpace}
    (hp : p ∈ torus) : derivativeFactors c t p =
      !₂[Real.exp (2 * t), 1, Real.exp (2 * t), 1, Real.exp (-c * t)] := by
  have h₁ : radiusSq₁ p = 1 := hp.1
  have h₂ : radiusSq₂ p = 1 := hp.2.1
  ext i
  fin_cases i <;> simp [derivativeFactors, h₁, h₂,
    planarAmplitude_at_one ht, radialAmplitude_at_one ht]

end Eden
