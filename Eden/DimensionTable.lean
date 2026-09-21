import Eden.SpectrumTable
import Eden.FiniteTimeDimension

/-!
# Kaplan--Yorke values and their maximisers

The six values follow from the ordered spectra and the largest nonnegative
partial-sum index. Spectra with leading zero entries have dimensions one and two.
-/

noncomputable section
namespace Eden

theorem kaplanYorkeDimension_zero_zero {c : ℝ} (hc : 4 < c) :
    kaplanYorkeDimension ![-2, -2, -2, -2, -c] = 0 := by
  apply kaplanYorkeDimension_of_index_zero
  apply kaplanYorkeIndex_eq (by omega) (by simp)
  intro k hk hk₅
  interval_cases k <;>
    norm_num [spectrumPartialSum, spectrumEntry, Finset.sum_range_succ] at *
  all_goals linarith

theorem kaplanYorkeDimension_zero_one {c : ℝ} (hc : 4 < c) :
    kaplanYorkeDimension ![2, 0, -2, -2, -c] = 3 := by
  have hi : kaplanYorkeIndex ![2, 0, -2, -2, -c] = 3 := by
    apply kaplanYorkeIndex_eq (by omega)
      (by norm_num [spectrumPartialSum, spectrumEntry, Finset.sum_range_succ])
    intro k hk hk₅
    interval_cases k <;>
      norm_num [spectrumPartialSum, spectrumEntry, Finset.sum_range_succ] at *
    all_goals linarith
  rw [kaplanYorkeDimension_of_index_between hi (by omega) (by omega)]
  norm_num [spectrumPartialSum, spectrumEntry, Finset.sum_range_succ]

theorem kaplanYorkeDimension_zero_two {c : ℝ} (hc : 4 < c) :
    kaplanYorkeDimension ![0, -2, -2, -4, -c] = 1 := by
  have hi : kaplanYorkeIndex ![0, -2, -2, -4, -c] = 1 := by
    apply kaplanYorkeIndex_eq (by omega) (by norm_num [spectrumPartialSum, spectrumEntry])
    intro k hk hk₅
    interval_cases k <;>
      norm_num [spectrumPartialSum, spectrumEntry, Finset.sum_range_succ] at *
    all_goals linarith
  rw [kaplanYorkeDimension_of_index_between hi (by omega) (by omega)]
  norm_num [spectrumPartialSum, spectrumEntry, Finset.sum_range_succ]

theorem kaplanYorkeDimension_one_one {c : ℝ} (hc : 4 < c) :
    kaplanYorkeDimension ![2, 2, 0, 0, -c] = targetDimension c := by
  have hi : kaplanYorkeIndex ![2, 2, 0, 0, -c] = 4 := by
    apply kaplanYorkeIndex_eq (by omega)
      (by norm_num [spectrumPartialSum, spectrumEntry, Finset.sum_range_succ])
    intro k hk hk₅
    have : k = 5 := by omega
    subst k
    norm_num [spectrumPartialSum, spectrumEntry, Finset.sum_range_succ]
    linarith
  rw [kaplanYorkeDimension_of_index_between hi (by omega) (by omega)]
  norm_num [spectrumPartialSum, spectrumEntry, Finset.sum_range_succ,
    abs_of_neg (show -c < 0 by linarith), targetDimension]

theorem kaplanYorkeDimension_one_two {c : ℝ} (hc : 4 < c) :
    kaplanYorkeDimension ![2, 0, 0, -4, -c] = 7 / 2 := by
  have hi : kaplanYorkeIndex ![2, 0, 0, -4, -c] = 3 := by
    apply kaplanYorkeIndex_eq (by omega)
      (by norm_num [spectrumPartialSum, spectrumEntry, Finset.sum_range_succ])
    intro k hk hk₅
    interval_cases k <;>
      norm_num [spectrumPartialSum, spectrumEntry, Finset.sum_range_succ] at *
    all_goals linarith
  rw [kaplanYorkeDimension_of_index_between hi (by omega) (by omega)]
  norm_num [spectrumPartialSum, spectrumEntry, Finset.sum_range_succ]

theorem kaplanYorkeDimension_two_two {c : ℝ} (hc : 4 < c) :
    kaplanYorkeDimension ![0, 0, -4, -4, -c] = 2 := by
  have hi : kaplanYorkeIndex ![0, 0, -4, -4, -c] = 2 := by
    apply kaplanYorkeIndex_eq (by omega)
      (by norm_num [spectrumPartialSum, spectrumEntry, Finset.sum_range_succ])
    intro k hk hk₅
    interval_cases k <;>
      norm_num [spectrumPartialSum, spectrumEntry, Finset.sum_range_succ] at *
    all_goals linarith
  rw [kaplanYorkeDimension_of_index_between hi (by omega) (by omega)]
  norm_num [spectrumPartialSum, spectrumEntry, Finset.sum_range_succ]

/-- Exhausting the three possible limiting squared radii gives the sharp
bound and its unique radius pair, allowing either order of the planes. -/
theorem kaplanYorkeDimension_radiusPair_bound_and_eq {c s₁ s₂ : ℝ} (hc : 4 < c)
    (hs₁ : s₁ = 0 ∨ s₁ = 1 ∨ s₁ = 2) (hs₂ : s₂ = 0 ∨ s₂ = 1 ∨ s₂ = 2) :
    kaplanYorkeDimension (descending (radiusPairSpectrum c s₁ s₂)) ≤ targetDimension c ∧
      (kaplanYorkeDimension (descending (radiusPairSpectrum c s₁ s₂)) = targetDimension c ↔
        s₁ = 1 ∧ s₂ = 1) := by
  rcases hs₁ with rfl | rfl | rfl <;> rcases hs₂ with rfl | rfl | rfl
  all_goals try rw [descending_radiusPairSpectrum_swap c 1 0]
  all_goals try rw [descending_radiusPairSpectrum_swap c 2 0]
  all_goals try rw [descending_radiusPairSpectrum_swap c 2 1]
  all_goals simp only [descending_radiusPairSpectrum_zero_zero hc,
    descending_radiusPairSpectrum_zero_one hc, descending_radiusPairSpectrum_zero_two hc,
    descending_radiusPairSpectrum_one_one hc, descending_radiusPairSpectrum_one_two hc,
    descending_radiusPairSpectrum_two_two hc, kaplanYorkeDimension_zero_zero hc,
    kaplanYorkeDimension_zero_one hc, kaplanYorkeDimension_zero_two hc,
    kaplanYorkeDimension_one_one hc, kaplanYorkeDimension_one_two hc,
    kaplanYorkeDimension_two_two hc]
  all_goals norm_num
  all_goals constructor <;> linarith [(targetDimension_bounds hc).1]

theorem asymptoticDimension_le_target {c : ℝ} (hc : 4 < c) (p : PhaseSpace) :
    asymptoticDimension c p ≤ targetDimension c := by
  rw [asymptoticDimension, lyapunovExponent_eq_radiusPairSpectrum]
  exact (kaplanYorkeDimension_radiusPair_bound_and_eq hc
    (limitingSquaredRadius_cases _) (limitingSquaredRadius_cases _)).1

/-- In the ambient space the maximising radii are exactly one; the fifth
coordinate is fixed to zero when the point is restricted to A. -/
theorem asymptoticDimension_eq_target_iff_radii {c : ℝ} (hc : 4 < c) (p : PhaseSpace) :
    asymptoticDimension c p = targetDimension c ↔ radiusSq₁ p = 1 ∧ radiusSq₂ p = 1 := by
  rw [asymptoticDimension, lyapunovExponent_eq_radiusPairSpectrum,
    (kaplanYorkeDimension_radiusPair_bound_and_eq hc
      (limitingSquaredRadius_cases _) (limitingSquaredRadius_cases _)).2,
    limitingSquaredRadius_eq_one_iff, limitingSquaredRadius_eq_one_iff]

theorem asymptoticDimension_eq_target_iff {c : ℝ} (hc : 4 < c) {p : PhaseSpace}
    (hp : p ∈ attractor) : asymptoticDimension c p = targetDimension c ↔ p ∈ torus := by
  rw [asymptoticDimension_eq_target_iff_radii hc]
  change (radiusSq₁ p = 1 ∧ radiusSq₂ p = 1) ↔
    radiusSq₁ p = 1 ∧ radiusSq₂ p = 1 ∧ p 4 = 0
  simp [hp.2.2]

theorem asymptoticDimension_lt_target_of_not_mem_torus {c : ℝ} (hc : 4 < c)
    {p : PhaseSpace} (hp : p ∈ attractor) (hT : p ∉ torus) :
    asymptoticDimension c p < targetDimension c :=
  lt_of_le_of_ne (asymptoticDimension_le_target hc p)
    (fun h => hT ((asymptoticDimension_eq_target_iff hc hp).mp h))

theorem asymptoticDimension_on_torus {c : ℝ} (hc : 4 < c) {p : PhaseSpace}
    (hp : p ∈ torus) : asymptoticDimension c p = 4 + 4 / c :=
  (asymptoticDimension_eq_target_iff hc (torus_subset_attractor hp)).mpr hp

theorem asymptoticDimension_attractor_isGreatest {c : ℝ} (hc : 4 < c) :
    IsGreatest (asymptoticDimension c '' attractor) (targetDimension c) := by
  constructor
  · obtain ⟨p, hp⟩ := torus_nonempty
    exact ⟨p, torus_subset_attractor hp, asymptoticDimension_on_torus hc hp⟩
  · rintro d ⟨p, hp, rfl⟩
    exact asymptoticDimension_le_target hc p

theorem supremum_asymptoticDimension_attractor {c : ℝ} (hc : 4 < c) :
    sSup (asymptoticDimension c '' attractor) = targetDimension c :=
  (asymptoticDimension_attractor_isGreatest hc).csSup_eq

theorem globalLyapunovDimension_eq_supremum_asymptoticDimension {c : ℝ} (hc : 4 < c) :
    globalLyapunovDimension c attractor = sSup (asymptoticDimension c '' attractor) := by
  rw [globalLyapunovDimension_attractor hc, supremum_asymptoticDimension_attractor hc]
  rfl

end Eden
