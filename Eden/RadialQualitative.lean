import Eden.PhysicalRadius
import Eden.Uniqueness

/-!
# Equilibrium radii, signs and the unit-radius limit

All equilibrium and limit classifications below retain the entire nonnegative
half-line. The strict signs are consequences of the factored radial field.
Uniqueness of limits uses Mathlib's Hausdorff-space limit API.
-/

noncomputable section
open Filter Set
open scoped Topology
namespace Eden

theorem radialField_eq_zero_iff {r : ℝ} (hr : 0 ≤ r) :
    radialField r = 0 ↔ r = 0 ∨ r = 1 ∨ r = Real.sqrt 2 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hn := Real.sqrt_nonneg (2 : ℝ)
  constructor
  · intro h
    simp only [radialField, mul_eq_zero, neg_eq_zero, sub_eq_zero] at h
    rcases h with (h | h) | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (by nlinarith))
    · exact Or.inr (Or.inr (by nlinarith))
  · rintro (rfl | rfl | rfl) <;> simp [radialField]

theorem radialField_neg_below_one {r : ℝ} (hr : 0 < r) (hr₁ : r < 1) :
    radialField r < 0 := by
  have h₁ : r ^ 2 - 1 < 0 := by nlinarith
  have h₂ : r ^ 2 - 2 < 0 := by nlinarith
  exact mul_neg_of_pos_of_neg (mul_pos_of_neg_of_neg (neg_neg_of_pos hr) h₁) h₂

theorem radialField_pos_between {r : ℝ} (hr₁ : 1 < r) (hr₂ : r < Real.sqrt 2) :
    radialField r > 0 := by
  have h₁ : 0 < r ^ 2 - 1 := by nlinarith
  have h₂ : r ^ 2 - 2 < 0 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg (2 : ℝ)]
  exact mul_pos_of_neg_of_neg (mul_neg_of_neg_of_pos (by linarith) h₁) h₂

theorem radialField_neg_above {r : ℝ} (hr : Real.sqrt 2 < r) :
    radialField r < 0 := by
  have hn := Real.sqrt_nonneg (2 : ℝ)
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have h₁ : 0 < r ^ 2 - 1 := by nlinarith
  have h₂ : 0 < r ^ 2 - 2 := by nlinarith
  exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by linarith) h₁) h₂

theorem tendsto_radiusEvolution_one_iff {r : ℝ} (hr : 0 ≤ r) :
    Tendsto (fun t => radiusEvolution t r) atTop (𝓝 1) ↔ r = 1 := by
  constructor
  · intro h
    rcases lt_trichotomy r 1 with hlt | heq | hgt
    · have heq := tendsto_nhds_unique h (tendsto_radiusEvolution_of_lt_one hr hlt)
      norm_num at heq
    · exact heq
    · have heq := tendsto_nhds_unique h (tendsto_radiusEvolution_of_one_lt hgt)
      have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
      nlinarith
  · rintro rfl
    simp

/-- The trajectory is bounded on every finite forward interval, including for real
parameters for which the fifth coordinate expands. -/
theorem isBounded_evolution_image_interval (c T : ℝ) (p : PhaseSpace) :
    Bornology.IsBounded ((fun t => evolution c t p) '' Icc 0 T) :=
  (isCompact_Icc.image_of_continuousOn
    ((continuousOn_evolution c p).mono Icc_subset_Ici_self)).isBounded

end Eden
