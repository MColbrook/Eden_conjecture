import Eden.ExactGlobalGrowth
import Eden.LogarithmicInterpolation

/-!
# Interpolation of globally maximised sums

Successive differences of the global rates Γ_k define their piecewise
linear interpolant. Telescoping identifies its values at the integers.
-/

noncomputable section
open Set
namespace Eden

/-- Successive differences of global sums, used only to encode interpolation. -/
def globalGrowthIncrements (c : ℝ) (i : Fin 5) : ℝ :=
  globalGrowthRate c (i.val + 1) - globalGrowthRate c i.val

/-- Interpolation encoded by successive differences. For c≥4 the theorems
below identify it with the linear interpolant through (k,Γ_k), k=0,...,5. -/
def globalGrowthInterpolation (c d : ℝ) : ℝ :=
  spectrumInterpolation (globalGrowthIncrements c) d

/-- Supremum of the nonnegative region on [0,5]. For c>4 it is proved below
to be attained and equal to the largest nonnegative point. -/
def globalGrowthDimension (c : ℝ) : ℝ :=
  sSup {d : ℝ | d ∈ Icc 0 5 ∧ 0 ≤ globalGrowthInterpolation c d}

theorem spectrumEntry_globalGrowthIncrements (c : ℝ) {k : ℕ} (hk : k < 5) :
    spectrumEntry (globalGrowthIncrements c) k =
      globalGrowthRate c (k + 1) - globalGrowthRate c k := by
  simp [spectrumEntry, hk, globalGrowthIncrements]

theorem spectrumPartialSum_globalGrowthIncrements {c : ℝ} (hc : 4 ≤ c)
    {k : ℕ} (hk : k ≤ 5) :
    spectrumPartialSum (globalGrowthIncrements c) k = globalGrowthRate c k := by
  induction k with
  | zero => simp [globalGrowthRate_zero hc]
  | succ k ih =>
    rw [spectrumPartialSum_succ, ih (by omega),
      spectrumEntry_globalGrowthIncrements c (by omega)]
    ring

theorem globalGrowthInterpolation_interpolate {c : ℝ} (hc : 4 ≤ c)
    {k : ℕ} (hk : k < 5) {α : ℝ} (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) :
    globalGrowthInterpolation c ((k : ℝ) + α) =
      (1 - α) * globalGrowthRate c k + α * globalGrowthRate c (k + 1) := by
  rw [globalGrowthInterpolation, spectrumInterpolation_interpolate _ hk hα₀ hα₁,
    spectrumPartialSum_globalGrowthIncrements hc (by omega),
    spectrumEntry_globalGrowthIncrements c hk]
  ring

theorem globalGrowthInterpolation_integer {c : ℝ} (hc : 4 ≤ c)
    {k : ℕ} (hk : k ≤ 5) :
    globalGrowthInterpolation c k = globalGrowthRate c k := by
  rcases eq_or_lt_of_le hk with rfl | hk
  · exact (spectrumInterpolation_five _).trans (spectrumPartialSum_globalGrowthIncrements hc le_rfl)
  · simpa using globalGrowthInterpolation_interpolate hc hk (α := 0) le_rfl zero_le_one

theorem globalGrowthInterpolation_four_five {c d : ℝ} (hc : 4 ≤ c)
    (hd₄ : 4 ≤ d) (hd₅ : d ≤ 5) :
    globalGrowthInterpolation c d = 4 - c * (d - 4) := by
  have h := globalGrowthInterpolation_interpolate hc (k := 4) (by norm_num)
    (α := d - 4) (by linarith) (by linarith)
  norm_num only [Nat.cast_ofNat] at h
  rw [show 4 + (d - 4) = d by ring, globalGrowthRate_four hc, globalGrowthRate_five hc] at h
  rw [h]
  ring

/-- The largest nonnegative integer global sum has index four when c>4. -/
theorem globalGrowthIndex_eq_four {c : ℝ} (hc : 4 < c) :
    kaplanYorkeIndex (globalGrowthIncrements c) = 4 := by
  apply kaplanYorkeIndex_eq (by norm_num)
  · rw [spectrumPartialSum_globalGrowthIncrements hc.le (by norm_num), globalGrowthRate_four hc.le]
    norm_num
  · intro k hk hk₅
    have he : k = 5 := by omega
    subst k
    rw [spectrumPartialSum_globalGrowthIncrements hc.le le_rfl]
    exact globalGrowthRate_five_neg hc

/-- The full real interpolant has greatest nonnegative point 4+4/c when c>4. -/
theorem globalGrowthInterpolation_isGreatest {c : ℝ} (hc : 4 < c) :
    IsGreatest {d : ℝ | d ∈ Icc 0 5 ∧ 0 ≤ globalGrowthInterpolation c d}
      (targetDimension c) := by
  have hd := targetDimension_bounds hc
  have hpos : 0 < c := by linarith
  have hroot : globalGrowthInterpolation c (targetDimension c) = 0 := by
    rw [globalGrowthInterpolation_four_five hc.le hd.1.le hd.2.le]
    simp only [targetDimension, add_sub_cancel_left]
    rw [mul_div_cancel₀ _ hpos.ne', sub_self]
  constructor
  · exact ⟨⟨by linarith, hd.2.le⟩, hroot ▸ le_rfl⟩
  · intro d hd'
    change d ∈ Icc 0 5 ∧ 0 ≤ globalGrowthInterpolation c d at hd'
    by_contra hn
    have hdt : targetDimension c < d := lt_of_not_ge hn
    have hd₄ : 4 ≤ d := hd.1.le.trans hdt.le
    rw [globalGrowthInterpolation_four_five hc.le hd₄ hd'.1.2] at hd'
    have hineq : 4 / c < d - 4 := by
      dsimp [targetDimension] at hdt
      linarith
    have hmul : 4 < (d - 4) * c := (div_lt_iff₀ hpos).mp hineq
    nlinarith [hd'.2]

/-- The dimension obtained from maximised sums is exactly 4+4/c. -/
theorem globalGrowthDimension_eq_target {c : ℝ} (hc : 4 < c) :
    globalGrowthDimension c = 4 + 4 / c :=
  (globalGrowthInterpolation_isGreatest hc).csSup_eq

/-- The same dimension in the fourth/fifth global-rate ratio form. -/
theorem globalGrowthDimension_eq_rate_ratio {c : ℝ} (hc : 4 < c) :
    globalGrowthDimension c =
      4 + globalGrowthRate c 4 / (globalGrowthRate c 4 - globalGrowthRate c 5) := by
  rw [globalGrowthDimension_eq_target hc, globalGrowthRate_four hc.le, globalGrowthRate_five hc.le]
  congr 2
  ring

end Eden
