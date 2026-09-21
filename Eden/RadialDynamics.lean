import Eden.ScalarCalculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Order, invariant regions and limits of the squared radius

These statements concern the explicit scalar evolution already connected to the
Cartesian ODE. Order preservation follows from its positive parameter derivative
using Mathlib's mean value theorem. The limiting squared radii follow from
continuity of square root and the exponential limit at infinity.
-/

noncomputable section
open Filter
open scoped Topology

namespace Eden

theorem strictMono_squaredRadiusEvolution {t : ℝ} (ht : 0 ≤ t) :
    StrictMono (squaredRadiusEvolution t) := by
  apply strictMono_of_hasDerivAt_pos (hasDerivAt_squaredRadiusEvolution_parameter ht)
  intro s
  exact div_pos (Real.exp_pos _) (pow_pos (sqrt_radialDiscriminant_pos ht s) _)

theorem squaredRadiusEvolution_lt_zero_iff {t s : ℝ} (ht : 0 ≤ t) :
    squaredRadiusEvolution t s < 0 ↔ s < 0 := by
  simpa using (strictMono_squaredRadiusEvolution ht).lt_iff_lt (a := s) (b := 0)

theorem squaredRadiusEvolution_pos_iff {t s : ℝ} (ht : 0 ≤ t) :
    0 < squaredRadiusEvolution t s ↔ 0 < s := by
  simpa using (strictMono_squaredRadiusEvolution ht).lt_iff_lt (a := 0) (b := s)

theorem squaredRadiusEvolution_lt_one_iff {t s : ℝ} (ht : 0 ≤ t) :
    squaredRadiusEvolution t s < 1 ↔ s < 1 := by
  simpa using (strictMono_squaredRadiusEvolution ht).lt_iff_lt (a := s) (b := 1)

theorem one_lt_squaredRadiusEvolution_iff {t s : ℝ} (ht : 0 ≤ t) :
    1 < squaredRadiusEvolution t s ↔ 1 < s := by
  simpa using (strictMono_squaredRadiusEvolution ht).lt_iff_lt (a := 1) (b := s)

theorem squaredRadiusEvolution_le_two_iff {t s : ℝ} (ht : 0 ≤ t) :
    squaredRadiusEvolution t s ≤ 2 ↔ s ≤ 2 := by
  simpa using (strictMono_squaredRadiusEvolution ht).le_iff_le (a := s) (b := 2)

theorem squaredRadiusEvolution_lt_two_iff {t s : ℝ} (ht : 0 ≤ t) :
    squaredRadiusEvolution t s < 2 ↔ s < 2 := by
  simpa using (strictMono_squaredRadiusEvolution ht).lt_iff_lt (a := s) (b := 2)

theorem two_lt_squaredRadiusEvolution_iff {t s : ℝ} (ht : 0 ≤ t) :
    2 < squaredRadiusEvolution t s ↔ 2 < s := by
  simpa using (strictMono_squaredRadiusEvolution ht).lt_iff_lt (a := 2) (b := s)

theorem squaredRadiusEvolution_le_initial {t s : ℝ} (ht : 0 ≤ t) (hs : 2 ≤ s) :
    squaredRadiusEvolution t s ≤ s := by
  have he : Real.exp (-4 * t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hD : 1 ≤ radialDiscriminant t s := by
    have hm := mul_nonneg (sub_nonneg.mpr he)
      (show 0 ≤ (s - 1) ^ 2 - 1 by nlinarith)
    dsimp [radialDiscriminant]
    nlinarith
  have hR : 1 ≤ Real.sqrt (radialDiscriminant t s) := by
    simpa using Real.sqrt_le_sqrt hD
  have hRp : 0 < Real.sqrt (radialDiscriminant t s) := by linarith
  have hdiv : (s - 1) / Real.sqrt (radialDiscriminant t s) ≤ s - 1 := by
    apply (div_le_iff₀ hRp).2
    nlinarith
  dsimp [squaredRadiusEvolution]
  linarith

theorem squaredRadiusEvolution_le_max {t s : ℝ} (ht : 0 ≤ t) :
    squaredRadiusEvolution t s ≤ max s 2 := by
  rcases le_total s 2 with hs | hs
  · exact le_trans ((squaredRadiusEvolution_le_two_iff ht).2 hs) (le_max_right _ _)
  · exact le_trans (squaredRadiusEvolution_le_initial ht hs) (le_max_left _ _)

/-- Inside the closed radial interval the formula is defined for all real time. -/
theorem radialDiscriminant_pos_on_interval (t : ℝ) {s : ℝ}
    (hs₀ : 0 ≤ s) (hs₂ : s ≤ 2) : 0 < radialDiscriminant t s := by
  have hu : (s - 1) ^ 2 ≤ 1 := by nlinarith
  have he := Real.exp_pos (-4 * t)
  have hm := mul_nonneg (sub_nonneg.mpr hu) (le_of_lt he)
  by_cases hz : (s - 1) ^ 2 = 0
  · simpa only [radialDiscriminant, hz, mul_zero, add_zero] using he
  · have hp : 0 < (s - 1) ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hz)
    dsimp [radialDiscriminant]
    nlinarith

theorem squaredRadiusEvolution_mem_interval (t : ℝ) {s : ℝ}
    (hs₀ : 0 ≤ s) (hs₂ : s ≤ 2) :
    squaredRadiusEvolution t s ∈ Set.Icc 0 2 := by
  have hD := radialDiscriminant_pos_on_interval t hs₀ hs₂
  have hR := Real.sqrt_pos.2 hD
  have hsq := Real.sq_sqrt hD.le
  have hu : (s - 1) ^ 2 ≤ 1 := by nlinarith
  have hm := mul_nonneg (sub_nonneg.mpr hu) (Real.exp_pos (-4 * t)).le
  have hbound : (s - 1) ^ 2 ≤ radialDiscriminant t s := by
    dsimp [radialDiscriminant]
    nlinarith
  have hl : -Real.sqrt (radialDiscriminant t s) ≤ s - 1 := by nlinarith
  have hr : s - 1 ≤ Real.sqrt (radialDiscriminant t s) := by nlinarith
  have hq₀ : -1 ≤ (s - 1) / Real.sqrt (radialDiscriminant t s) :=
    (le_div_iff₀ hR).2 (by linarith)
  have hq₂ : (s - 1) / Real.sqrt (radialDiscriminant t s) ≤ 1 :=
    (div_le_iff₀ hR).2 (by linarith)
  constructor <;> dsimp [squaredRadiusEvolution] <;> linarith

theorem tendsto_radialExponential :
    Tendsto (fun t : ℝ => Real.exp (-4 * t)) atTop (𝓝 0) := by
  have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (tendsto_id.const_mul_atTop (show (0 : ℝ) < 4 by norm_num))
  simpa only [Function.comp_def, id_eq, neg_mul] using h

theorem tendsto_radialDiscriminant (s : ℝ) :
    Tendsto (fun t => radialDiscriminant t s) atTop (𝓝 ((s - 1) ^ 2)) := by
  have h := tendsto_radialExponential.add
    (((tendsto_const_nhds (x := (1 : ℝ))).sub tendsto_radialExponential).mul_const
      ((s - 1) ^ 2))
  simpa [radialDiscriminant] using h

theorem tendsto_squaredRadiusEvolution {s : ℝ} (hs : s ≠ 1) :
    Tendsto (fun t => squaredRadiusEvolution t s) atTop
      (𝓝 (1 + (s - 1) / |s - 1|)) := by
  have hR := (tendsto_radialDiscriminant s).sqrt
  rw [Real.sqrt_sq_eq_abs] at hR
  have hn : |s - 1| ≠ 0 := abs_ne_zero.mpr (sub_ne_zero.mpr hs)
  exact tendsto_const_nhds.add (tendsto_const_nhds.div hR hn)

theorem tendsto_squaredRadiusEvolution_of_lt_one {s : ℝ} (hs : s < 1) :
    Tendsto (fun t => squaredRadiusEvolution t s) atTop (𝓝 0) := by
  have h := tendsto_squaredRadiusEvolution (ne_of_lt hs)
  have hn : s - 1 ≠ 0 := by linarith
  rw [abs_of_neg (show s - 1 < 0 by linarith), div_neg, div_self hn] at h
  norm_num at h
  exact h

theorem tendsto_squaredRadiusEvolution_of_one_lt {s : ℝ} (hs : 1 < s) :
    Tendsto (fun t => squaredRadiusEvolution t s) atTop (𝓝 2) := by
  have h := tendsto_squaredRadiusEvolution (ne_of_gt hs)
  have hn : s - 1 ≠ 0 := by linarith
  rw [abs_of_pos (show 0 < s - 1 by linarith), div_self hn] at h
  norm_num at h
  exact h

end Eden
