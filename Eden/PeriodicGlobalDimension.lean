import Eden.PeriodicGlobalGrowth

/-!
# Dimension from the periodic-set global growth sums

Successive differences encode the interpolant through the already proved
ordinary limits of spatial suprema. The six nodes are identified explicitly; for
c > 4, the largest nonnegative point on the entire interval [0,5] is three. The
fixed-index quantity 4-2/c is a separate convention in CommonIndexPeriodic.
-/

noncomputable section
open Set
namespace Eden

/-- Successive differences of the periodic-set global sums. -/
def periodicGlobalGrowthIncrements (c : ℝ) (i : Fin 5) : ℝ :=
  periodicGlobalGrowthRate c (i.val + 1) - periodicGlobalGrowthRate c i.val

/-- The interpolant is encoded by successive differences of the global growth sums. -/
def periodicGlobalGrowthInterpolation (c d : ℝ) : ℝ :=
  spectrumInterpolation (periodicGlobalGrowthIncrements c) d

/-- Supremum of the nonnegative interpolation region on the full dimension interval. -/
def periodicGlobalGrowthDimension (c : ℝ) : ℝ :=
  sSup {d : ℝ | d ∈ Icc 0 5 ∧ 0 ≤ periodicGlobalGrowthInterpolation c d}

theorem periodicGlobalGrowthIncrements_eq {c : ℝ} (hc : 4 < c) :
    periodicGlobalGrowthIncrements c = ![2, 0, -2, -2, -c] := by
  funext i
  unfold periodicGlobalGrowthIncrements
  rw [periodicGlobalGrowthRate_eq hc (by omega), periodicGlobalGrowthRate_eq hc (by omega)]
  fin_cases i <;> norm_num [spectrumPartialSum, spectrumEntry, Finset.sum_range_succ]

theorem periodicGlobalGrowthInterpolation_eq {c : ℝ} (hc : 4 < c) (d : ℝ) :
    periodicGlobalGrowthInterpolation c d = spectrumInterpolation ![2, 0, -2, -2, -c] d := by
  rw [periodicGlobalGrowthInterpolation, periodicGlobalGrowthIncrements_eq hc]

/-- Equality with the global sums at all six integer nodes. -/
theorem periodicGlobalGrowthInterpolation_integer {c : ℝ} (hc : 4 < c)
    {k : ℕ} (hk : k ≤ 5) :
    periodicGlobalGrowthInterpolation c k = periodicGlobalGrowthRate c k := by
  rw [periodicGlobalGrowthInterpolation_eq hc, spectrumInterpolation_integer _ hk,
    periodicGlobalGrowthRate_eq hc hk]

/-- Linear interpolation between every pair of consecutive global-sum nodes. -/
theorem periodicGlobalGrowthInterpolation_interpolate {c : ℝ} (hc : 4 < c)
    {k : ℕ} (hk : k < 5) {α : ℝ} (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) :
    periodicGlobalGrowthInterpolation c ((k : ℝ) + α) =
      (1 - α) * periodicGlobalGrowthRate c k + α * periodicGlobalGrowthRate c (k + 1) := by
  rw [periodicGlobalGrowthInterpolation_eq hc,
    spectrumInterpolation_interpolate _ hk hα₀ hα₁,
    periodicGlobalGrowthRate_eq hc (by omega), periodicGlobalGrowthRate_eq hc (by omega),
    spectrumPartialSum_succ]
  ring

/-- The last nonnegative integer global-sum node is three when c > 4. -/
theorem periodicGlobalGrowthIndex_eq_three {c : ℝ} (hc : 4 < c) :
    kaplanYorkeIndex (periodicGlobalGrowthIncrements c) = 3 := by
  rw [periodicGlobalGrowthIncrements_eq hc]
  apply kaplanYorkeIndex_eq (by omega)
    (by norm_num [spectrumPartialSum, spectrumEntry, Finset.sum_range_succ])
  intro k hk hk₅
  interval_cases k <;> norm_num [spectrumPartialSum, spectrumEntry, Finset.sum_range_succ]
  linarith

/-- The maximum is over all real dimensions in [0,5], including the zero at three. -/
theorem periodicGlobalGrowthInterpolation_isGreatest {c : ℝ} (hc : 4 < c) :
    IsGreatest {d : ℝ | d ∈ Icc 0 5 ∧ 0 ≤ periodicGlobalGrowthInterpolation c d} 3 := by
  have ha : Antitone (![2, 0, -2, -2, -c] : Fin 5 → ℝ) := by
    rw [← descending_radiusPairSpectrum_zero_one hc]
    exact descending_antitone _
  have hiff (d : ℝ) (hd : d ∈ Icc 0 5) :
      0 ≤ periodicGlobalGrowthInterpolation c d ↔ d ≤ 3 := by
    rw [periodicGlobalGrowthInterpolation_eq hc, spectrumInterpolation_nonneg_iff ha hd,
      kaplanYorkeDimension_zero_one hc]
  constructor
  · exact ⟨by norm_num, (hiff 3 (by norm_num)).mpr le_rfl⟩
  · intro d hd
    exact (hiff d hd.1).mp hd.2

/-- The dimension formed from periodic-set spatial suprema before time limits equals
three. -/
theorem periodicGlobalGrowthDimension_eq_three {c : ℝ} (hc : 4 < c) :
    periodicGlobalGrowthDimension c = 3 :=
  (periodicGlobalGrowthInterpolation_isGreatest hc).csSup_eq

end Eden
