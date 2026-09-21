import Eden.CommonIndex
import Eden.PeriodicGap

/-!
# Periodic points with the global index fixed

The complete equilibrium/periodic classification gives fourth sum -8 at
the origin and outer circles, and -2 on the unit circles. The common-index
local expression therefore has maximum 4-2/c, whereas the separately
defined pointwise Kaplan--Yorke dimension has maximum 3.
-/

noncomputable section
open Set
namespace Eden

theorem exponentSum_four_unit_circle {c : ℝ} (hc : 4 < c) {p : PhaseSpace}
    (hp : p ∈ firstCircle 1 ∨ p ∈ secondCircle 1) :
    spectrumPartialSum (lyapunovExponent c p) 4 = -2 := by
  have hs : lyapunovExponent c p = ![2, 0, -2, -2, -c] := by
    rcases hp with hp | hp
    · rw [lyapunovExponent_eq_radiusPairSpectrum, hp.1, hp.2.1]
      norm_num [limitingSquaredRadius]
      rw [descending_radiusPairSpectrum_swap c 1 0, descending_radiusPairSpectrum_zero_one hc]
    · rw [lyapunovExponent_eq_radiusPairSpectrum, hp.1, hp.2.1]
      norm_num [limitingSquaredRadius]
      exact descending_radiusPairSpectrum_zero_one hc
  rw [hs]
  norm_num [spectrumPartialSum, spectrumEntry, Finset.sum_range_succ]

theorem exponentSum_four_outer_circle {c : ℝ} (hc : 4 < c) {p : PhaseSpace}
    (hp : p ∈ firstCircle 2 ∨ p ∈ secondCircle 2) :
    spectrumPartialSum (lyapunovExponent c p) 4 = -8 := by
  have hs : lyapunovExponent c p = ![0, -2, -2, -4, -c] := by
    rcases hp with hp | hp
    · rw [lyapunovExponent_eq_radiusPairSpectrum, hp.1, hp.2.1]
      norm_num [limitingSquaredRadius]
      rw [descending_radiusPairSpectrum_swap c 2 0, descending_radiusPairSpectrum_zero_two hc]
    · rw [lyapunovExponent_eq_radiusPairSpectrum, hp.1, hp.2.1]
      norm_num [limitingSquaredRadius]
      exact descending_radiusPairSpectrum_zero_two hc
  rw [hs]
  norm_num [spectrumPartialSum, spectrumEntry, Finset.sum_range_succ]

theorem exponentSum_four_origin {c : ℝ} (hc : 4 < c) :
    spectrumPartialSum (lyapunovExponent c 0) 4 = -8 := by
  rw [lyapunovExponent_eq_radiusPairSpectrum]
  norm_num [radiusSq₁, radiusSq₂, limitingSquaredRadius]
  rw [descending_radiusPairSpectrum_zero_zero hc]
  norm_num [spectrumPartialSum, spectrumEntry, Finset.sum_range_succ]

theorem exponentSum_four_periodic_le {c : ℝ} (hc : 4 < c) {p : PhaseSpace}
    (hp : p ∈ periodicEquilibriumSet c) : spectrumPartialSum (lyapunovExponent c p) 4 ≤ -2 := by
  rw [periodicEquilibriumSet_eq_positiveReturnSet (show 0 < c by linarith)] at hp
  rcases (mem_positiveReturnSet_iff (by linarith) p).mp hp with rfl | h | h | h | h
  · rw [exponentSum_four_origin hc]; norm_num
  · exact (exponentSum_four_unit_circle hc (Or.inl h)).le
  · rw [exponentSum_four_outer_circle hc (Or.inl h)]; norm_num
  · exact (exponentSum_four_unit_circle hc (Or.inr h)).le
  · rw [exponentSum_four_outer_circle hc (Or.inr h)]; norm_num

theorem exponentSum_four_periodic_isGreatest {c : ℝ} (hc : 4 < c) :
    IsGreatest ((fun p => spectrumPartialSum (lyapunovExponent c p) 4) ''
      periodicEquilibriumSet c) (-2) := by
  constructor
  · obtain ⟨p, hp⟩ := firstCircle_nonempty (show (0 : ℝ) ≤ 1 by norm_num)
    refine ⟨p, ?_, exponentSum_four_unit_circle hc (Or.inl hp)⟩
    rw [periodicEquilibriumSet_eq_positiveReturnSet (show 0 < c by linarith)]
    exact (mem_positiveReturnSet_iff (by linarith) p).mpr (Or.inr (Or.inl hp))
  · rintro x ⟨p, hp, rfl⟩
    exact exponentSum_four_periodic_le hc hp

/-- Over the entire equilibrium/periodic set, the fixed global index gives
maximum 4-2/c, attained on a unit circle. -/
theorem commonIndexLocalDimension_periodic_isGreatest {c : ℝ} (hc : 4 < c) :
    IsGreatest (commonIndexLocalDimension c '' periodicEquilibriumSet c) (4 - 2 / c) := by
  constructor
  · obtain ⟨p, hp, he⟩ := (exponentSum_four_periodic_isGreatest hc).1
    dsimp only at he
    refine ⟨p, hp, ?_⟩
    rw [commonIndexLocalDimension_eq hc, he]
    ring
  · rintro x ⟨p, hp, rfl⟩
    rw [commonIndexLocalDimension_eq hc]
    have h := div_le_div_of_nonneg_right (exponentSum_four_periodic_le hc hp)
      (show (0 : ℝ) ≤ c by linarith)
    rw [neg_div] at h
    linarith

theorem supremum_commonIndexLocalDimension_periodic {c : ℝ} (hc : 4 < c) :
    sSup (commonIndexLocalDimension c '' periodicEquilibriumSet c) = 4 - 2 / c :=
  (commonIndexLocalDimension_periodic_isGreatest hc).csSup_eq

theorem commonIndex_periodic_gap {c : ℝ} (hc : 4 < c) :
    sSup (commonIndexLocalDimension c '' periodicEquilibriumSet c) < commonIndexDimension c := by
  rw [supremum_commonIndexLocalDimension_periodic hc, commonIndexDimension_eq_target hc]
  have h₂ : (0 : ℝ) < 2 / c := by positivity
  have h₄ : (0 : ℝ) < 4 / c := by positivity
  linarith

theorem periodic_dimension_conventions_distinct {c : ℝ} (hc : 4 < c) :
    sSup (asymptoticDimension c '' periodicEquilibriumSet c) <
      sSup (commonIndexLocalDimension c '' periodicEquilibriumSet c) := by
  rw [supremum_asymptoticDimension_periodic hc, supremum_commonIndexLocalDimension_periodic hc]
  have : (2 : ℝ) / c < 1 := (div_lt_one (by linarith)).mpr (by linarith)
  linarith

end Eden
