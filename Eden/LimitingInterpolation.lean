import Eden.InterpolationSign
import Eden.DimensionTable

/-!
# Strict positivity in the expanding limiting spectra

The three spectra with a positive first exponent have positive interpolant
strictly between zero and their Kaplan--Yorke dimension. The other rows,
which have zero dimension or leading zero exponents, are treated separately.
-/

noncomputable section
open Set
namespace Eden

theorem spectrumInterpolation_pos_zero_one {c d : ℝ}
    (hd : d ∈ Ioo 0 3) : 0 < spectrumInterpolation ![2, 0, -2, -2, -c] d := by
  obtain ⟨k, hk, α, hα, rfl⟩ := exists_dimension_segment
    (show d ∈ Icc 0 5 from ⟨hd.1.le, by linarith [hd.2]⟩)
  rw [spectrumInterpolation_interpolate _ hk hα.1 hα.2]
  interval_cases k <;>
    norm_num [spectrumPartialSum, spectrumEntry, Finset.sum_range_succ] at *
  all_goals linarith [hα.1, hα.2, hd.1, hd.2]

theorem spectrumInterpolation_pos_one_two {c d : ℝ}
    (hd : d ∈ Ioo 0 (7 / 2)) : 0 < spectrumInterpolation ![2, 0, 0, -4, -c] d := by
  obtain ⟨k, hk, α, hα, rfl⟩ := exists_dimension_segment
    (show d ∈ Icc 0 5 from ⟨hd.1.le, by linarith [hd.2]⟩)
  rw [spectrumInterpolation_interpolate _ hk hα.1 hα.2]
  interval_cases k <;>
    norm_num [spectrumPartialSum, spectrumEntry, Finset.sum_range_succ] at *
  all_goals linarith [hα.1, hα.2, hd.1, hd.2]

theorem spectrumInterpolation_pos_one_one {c d : ℝ} (hc : 4 < c)
    (hd : d ∈ Ioo 0 (targetDimension c)) :
    0 < spectrumInterpolation ![2, 2, 0, 0, -c] d := by
  obtain ⟨k, hk, α, hα, rfl⟩ := exists_dimension_segment
    (show d ∈ Icc 0 5 from ⟨hd.1.le, hd.2.le.trans (targetDimension_bounds hc).2.le⟩)
  rw [spectrumInterpolation_interpolate _ hk hα.1 hα.2]
  interval_cases k <;>
    norm_num [spectrumPartialSum, spectrumEntry, Finset.sum_range_succ] at *
  · linarith [hd.1]
  · linarith [hα.1]
  · have hαc : α * c < 4 := (lt_div_iff₀ (show 0 < c by linarith)).mp
      (show α < 4 / c by dsimp [targetDimension] at hd; linarith [hd.2])
    nlinarith

theorem one_lt_of_limitingSquaredRadius_eq_two {s : ℝ}
    (hs : limitingSquaredRadius s = 2) : 1 < s := by
  by_contra h
  rcases lt_or_eq_of_le (le_of_not_gt h) with hlt | heq
  · simp [limitingSquaredRadius, hlt] at hs
  · simp [limitingSquaredRadius, heq] at hs

end Eden
