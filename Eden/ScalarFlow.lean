import Eden.Algebra
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp

/-!
# An explicit formula for the squared-radius evolution

The substitution `u = r² - 1` transforms the radial equation into `u' =
2u(1-u²)`. This yields explicit formulas for the squared radius and for a planar
amplitude which is nonsingular at zero radius.

Differentiability follows from positivity of the radicands and Mathlib's real
exponential and square-root calculus.
-/

noncomputable section

namespace Eden

/-- Denominator squared in the explicit radial formula, positive for `t ≥ 0`. -/
def radialDiscriminant (t s : ℝ) : ℝ :=
  Real.exp (-4 * t) + (1 - Real.exp (-4 * t)) * (s - 1) ^ 2

/-- Evolution of an initial squared radius `s`. -/
def squaredRadiusEvolution (t s : ℝ) : ℝ :=
  1 + (s - 1) / Real.sqrt (radialDiscriminant t s)

/-- The squared planar amplitude, with its removable singularity at initial squared
radius zero already eliminated algebraically. -/
def amplitudeSq (t s : ℝ) : ℝ :=
  (1 + (s - 2) * (1 - Real.exp (-4 * t)) /
    (Real.sqrt (radialDiscriminant t s) + 1)) /
      Real.sqrt (radialDiscriminant t s)

theorem radialDiscriminant_pos {t : ℝ} (ht : 0 ≤ t) (s : ℝ) :
    0 < radialDiscriminant t s := by
  have he : Real.exp (-4 * t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hm := mul_nonneg (sub_nonneg.mpr he) (sq_nonneg (s - 1))
  have hp := Real.exp_pos (-4 * t)
  dsimp [radialDiscriminant]
  linarith

theorem sqrt_radialDiscriminant_pos {t : ℝ} (ht : 0 ≤ t) (s : ℝ) :
    0 < Real.sqrt (radialDiscriminant t s) :=
  Real.sqrt_pos.2 (radialDiscriminant_pos ht s)

private theorem amplitude_algebra_pos {e s R : ℝ}
    (he₀ : 0 < e) (he₁ : e ≤ 1) (hs₀ : 0 ≤ s) (hR : 0 < R)
    (hR₂ : R ^ 2 = e + (1 - e) * (s - 1) ^ 2) :
    0 < (1 + (s - 2) * (1 - e) / (R + 1)) / R := by
  have hnum : 0 < R + 1 + (s - 2) * (1 - e) := by
    rcases le_total 1 s with hs₁ | hs₁
    · have hm := mul_nonneg (sub_nonneg.mpr he₁) (sub_nonneg.mpr hs₁)
      nlinarith
    · have hsq : (s - 1) ^ 2 ≤ 1 := by nlinarith
      have hm := mul_nonneg (le_of_lt he₀) (sub_nonneg.mpr hsq)
      have hRge : 1 - s ≤ R := by nlinarith
      have hep : 0 < e * (2 - s) := mul_pos he₀ (by linarith)
      nlinarith
  have hden : 0 < R + 1 := by linarith
  have hquot : -1 < (s - 2) * (1 - e) / (R + 1) :=
    (lt_div_iff₀ hden).2 (by linarith)
  exact div_pos (by linarith) hR

theorem amplitudeSq_pos {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    0 < amplitudeSq t s := by
  apply amplitude_algebra_pos (Real.exp_pos (-4 * t))
    (Real.exp_le_one_iff.mpr (by linarith)) hs (sqrt_radialDiscriminant_pos ht s)
  exact Real.sq_sqrt (le_of_lt (radialDiscriminant_pos ht s))

theorem mul_amplitudeSq_of_discriminant_pos {t s : ℝ}
    (hD : 0 < radialDiscriminant t s) :
    s * amplitudeSq t s = squaredRadiusEvolution t s := by
  have hR := Real.sqrt_pos.2 hD
  have hR₀ : Real.sqrt (radialDiscriminant t s) ≠ 0 := ne_of_gt hR
  have hR₁ : Real.sqrt (radialDiscriminant t s) + 1 ≠ 0 := by linarith
  have hsq : Real.sqrt (radialDiscriminant t s) ^ 2 =
      Real.exp (-4 * t) + (1 - Real.exp (-4 * t)) * (s - 1) ^ 2 :=
    Real.sq_sqrt (le_of_lt hD)
  dsimp [amplitudeSq, squaredRadiusEvolution]
  field_simp
  simp only [neg_mul] at hsq
  nlinarith

theorem mul_amplitudeSq {t : ℝ} (ht : 0 ≤ t) (s : ℝ) :
    s * amplitudeSq t s = squaredRadiusEvolution t s :=
  mul_amplitudeSq_of_discriminant_pos (radialDiscriminant_pos ht s)

theorem squaredRadiusEvolution_nonneg {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    0 ≤ squaredRadiusEvolution t s := by
  rw [← mul_amplitudeSq ht s]
  exact mul_nonneg hs (le_of_lt (amplitudeSq_pos ht hs))

@[simp] theorem radialDiscriminant_zero_time (s : ℝ) : radialDiscriminant 0 s = 1 := by
  simp [radialDiscriminant]

@[simp] theorem squaredRadiusEvolution_zero_time (s : ℝ) :
    squaredRadiusEvolution 0 s = s := by
  simp [squaredRadiusEvolution]

@[simp] theorem amplitudeSq_zero_time (s : ℝ) : amplitudeSq 0 s = 1 := by
  simp [amplitudeSq]

@[simp] theorem squaredRadiusEvolution_at_one (t : ℝ) :
    squaredRadiusEvolution t 1 = 1 := by
  simp [squaredRadiusEvolution]

@[simp] theorem radialDiscriminant_at_zero (t : ℝ) : radialDiscriminant t 0 = 1 := by
  dsimp [radialDiscriminant]
  ring

@[simp] theorem radialDiscriminant_at_two (t : ℝ) : radialDiscriminant t 2 = 1 := by
  dsimp [radialDiscriminant]
  ring

@[simp] theorem squaredRadiusEvolution_at_zero (t : ℝ) :
    squaredRadiusEvolution t 0 = 0 := by
  simp [squaredRadiusEvolution]

@[simp] theorem squaredRadiusEvolution_at_two (t : ℝ) :
    squaredRadiusEvolution t 2 = 2 := by
  norm_num [squaredRadiusEvolution]

@[simp] theorem amplitudeSq_at_zero (t : ℝ) :
    amplitudeSq t 0 = Real.exp (-4 * t) := by
  simp [amplitudeSq]
  ring

/-- The scalar equation holds locally wherever its discriminant is positive. -/
theorem hasDerivAt_squaredRadiusEvolution_of_discriminant_pos {t s : ℝ}
    (hD : 0 < radialDiscriminant t s) :
    HasDerivAt (fun τ => squaredRadiusEvolution τ s)
      (-2 * squaredRadiusEvolution t s * (squaredRadiusEvolution t s - 1) *
        (squaredRadiusEvolution t s - 2)) t := by
  have he : HasDerivAt (fun τ : ℝ => Real.exp (-4 * τ))
      (Real.exp (-4 * t) * (-4)) t := by
    simpa using ((hasDerivAt_id t).const_mul (-4 : ℝ)).exp
  have hd := he.add (((hasDerivAt_const t (1 : ℝ)).sub he).mul_const ((s - 1) ^ 2))
  have hr := hd.sqrt (ne_of_gt hD)
  have hR := Real.sqrt_pos.2 hD
  have hq := (hasDerivAt_const t (s - 1)).div hr (ne_of_gt hR)
  have hsq : Real.sqrt (radialDiscriminant t s) ^ 2 =
      Real.exp (-4 * t) + (1 - Real.exp (-4 * t)) * (s - 1) ^ 2 :=
    Real.sq_sqrt (le_of_lt hD)
  apply (hq.const_add 1).congr_deriv
  dsimp [squaredRadiusEvolution, radialDiscriminant] at hR hsq ⊢
  simp only [neg_mul] at hR hsq ⊢
  field_simp [ne_of_gt hR]
  nlinarith [congrArg (fun x : ℝ => (s - 1) * x) hsq]

/-- The scalar equation holds for every nonnegative time and real initial parameter. -/
theorem hasDerivAt_squaredRadiusEvolution {t : ℝ} (ht : 0 ≤ t) (s : ℝ) :
    HasDerivAt (fun τ => squaredRadiusEvolution τ s)
      (-2 * squaredRadiusEvolution t s * (squaredRadiusEvolution t s - 1) *
        (squaredRadiusEvolution t s - 2)) t :=
  hasDerivAt_squaredRadiusEvolution_of_discriminant_pos (radialDiscriminant_pos ht s)

end Eden
