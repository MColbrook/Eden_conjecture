import Eden.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Algebraic identities for the radial and tangential rates

Algebraic identities and bounds for the radial and tangential variational
rates in the planar variational equations of Colbrook's paper.
-/

namespace Eden

theorem q_expansion (s : ℝ) : q s = -s ^ 2 + 3 * s - 2 := by
  unfold q
  ring

theorem tangentialRate_eq_q (s : ℝ) : tangentialRate s = q s := by
  rw [q_expansion]
  rfl

theorem radialRate_eq_q_add (s : ℝ) :
    radialRate s = q s + 2 * s * (-2 * s + 3) := by
  unfold radialRate q
  ring

theorem radialRate_add_four (s : ℝ) :
    radialRate s + 4 = (2 - s) * (5 * s + 1) := by
  unfold radialRate
  ring

theorem tangentialRate_add_two (s : ℝ) :
    tangentialRate s + 2 = s * (3 - s) := by
  unfold tangentialRate
  ring

theorem rates_sum (s : ℝ) :
    radialRate s + tangentialRate s = 2 - 6 * (s - 1) ^ 2 := by
  unfold radialRate tangentialRate
  ring

theorem radialRate_lower_bound {s : ℝ} (hs₀ : 0 ≤ s) (hs₂ : s ≤ 2) :
    -4 ≤ radialRate s := by
  have h := mul_nonneg (sub_nonneg.mpr hs₂) (show 0 ≤ 5 * s + 1 by linarith)
  linarith [radialRate_add_four s]

theorem tangentialRate_lower_bound {s : ℝ} (hs₀ : 0 ≤ s) (hs₂ : s ≤ 2) :
    -2 ≤ tangentialRate s := by
  have h := mul_nonneg hs₀ (show 0 ≤ 3 - s by linarith)
  linarith [tangentialRate_add_two s]

/-- The tangential rate is nonnegative on the outer invariant annulus. -/
theorem tangentialRate_nonneg {s : ℝ} (hs₁ : 1 ≤ s) (hs₂ : s ≤ 2) :
    0 ≤ tangentialRate s := by
  have h := mul_nonneg (sub_nonneg.mpr hs₁) (sub_nonneg.mpr hs₂)
  dsimp [tangentialRate]
  nlinarith

/-- The complete rate values at the three stationary squared radii. -/
theorem rates_at_stationary_radii :
    radialRate 0 = -2 ∧ tangentialRate 0 = -2 ∧
    radialRate 1 = 2 ∧ tangentialRate 1 = 0 ∧
    radialRate 2 = -4 ∧ tangentialRate 2 = 0 := by
  norm_num [radialRate, tangentialRate]

/-- Algebraic sum of the five variational rates. -/
theorem total_rate_identity (s₁ s₂ c : ℝ) :
    radialRate s₁ + tangentialRate s₁ + radialRate s₂ + tangentialRate s₂ - c =
      4 - c - 6 * (s₁ - 1) ^ 2 - 6 * (s₂ - 1) ^ 2 := by
  unfold radialRate tangentialRate
  ring

theorem total_rate_le (s₁ s₂ c : ℝ) :
    radialRate s₁ + tangentialRate s₁ + radialRate s₂ + tangentialRate s₂ - c ≤
      4 - c := by
  rw [total_rate_identity]
  nlinarith [sq_nonneg (s₁ - 1), sq_nonneg (s₂ - 1)]

theorem total_rate_neg (s₁ s₂ : ℝ) {c : ℝ} (hc : 4 < c) :
    radialRate s₁ + tangentialRate s₁ + radialRate s₂ + tangentialRate s₂ - c < 0 := by
  linarith [total_rate_le s₁ s₂ c]

theorem targetDimension_bounds {c : ℝ} (hc : 4 < c) :
    4 < targetDimension c ∧ targetDimension c < 5 := by
  have hc₀ : 0 < c := by linarith
  have hpos : 0 < (4 : ℝ) / c := div_pos (by norm_num) hc₀
  have hlt : (4 : ℝ) / c < 1 := (div_lt_one hc₀).2 hc
  dsimp [targetDimension]
  constructor <;> linarith

theorem targetDimension_eight : targetDimension 8 = 9 / 2 := by
  norm_num [targetDimension]

end Eden
