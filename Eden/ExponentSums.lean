import Eden.DimensionTable

/-!
# Maxima of sums of the Lyapunov exponents

The exponents here are the real-time limits already obtained from the ambient singular values. The finite spectrum classification determines their
last entry and their fourth and fifth partial sums. Suprema retain the same
initial point in every term of the sum.
-/

noncomputable section
open Set
namespace Eden

theorem lyapunovExponent_bounds {c : ℝ} (hc : 4 < c) (p : PhaseSpace)
    (i : Fin 5) : -c ≤ lyapunovExponent c p i ∧ lyapunovExponent c p i ≤ 2 := by
  rw [lyapunovExponent_eq_radiusPairSpectrum]
  rcases limitingSquaredRadius_cases (radiusSq₁ p) with h₁ | h₁ | h₁ <;>
    rcases limitingSquaredRadius_cases (radiusSq₂ p) with h₂ | h₂ | h₂
  all_goals rw [h₁, h₂]
  all_goals try rw [descending_radiusPairSpectrum_swap c 1 0]
  all_goals try rw [descending_radiusPairSpectrum_swap c 2 0]
  all_goals try rw [descending_radiusPairSpectrum_swap c 2 1]
  all_goals simp only [descending_radiusPairSpectrum_zero_zero hc,
    descending_radiusPairSpectrum_zero_one hc, descending_radiusPairSpectrum_zero_two hc,
    descending_radiusPairSpectrum_one_one hc, descending_radiusPairSpectrum_one_two hc,
    descending_radiusPairSpectrum_two_two hc]
  all_goals fin_cases i <;> norm_num <;> linarith

theorem lyapunovExponent_fifth {c : ℝ} (hc : 4 < c) (p : PhaseSpace) :
    lyapunovExponent c p 4 = -c := by
  rw [lyapunovExponent_eq_radiusPairSpectrum]
  rcases limitingSquaredRadius_cases (radiusSq₁ p) with h₁ | h₁ | h₁ <;>
    rcases limitingSquaredRadius_cases (radiusSq₂ p) with h₂ | h₂ | h₂
  all_goals rw [h₁, h₂]
  all_goals try rw [descending_radiusPairSpectrum_swap c 1 0]
  all_goals try rw [descending_radiusPairSpectrum_swap c 2 0]
  all_goals try rw [descending_radiusPairSpectrum_swap c 2 1]
  all_goals simp [descending_radiusPairSpectrum_zero_zero hc,
    descending_radiusPairSpectrum_zero_one hc, descending_radiusPairSpectrum_zero_two hc,
    descending_radiusPairSpectrum_one_one hc, descending_radiusPairSpectrum_one_two hc,
    descending_radiusPairSpectrum_two_two hc]

theorem exponentSum_four_bound_and_eq {c : ℝ} (hc : 4 < c) (p : PhaseSpace) :
    spectrumPartialSum (lyapunovExponent c p) 4 ≤ 4 ∧
      (spectrumPartialSum (lyapunovExponent c p) 4 = 4 ↔
        radiusSq₁ p = 1 ∧ radiusSq₂ p = 1) := by
  rw [← limitingSquaredRadius_eq_one_iff (radiusSq₁ p),
    ← limitingSquaredRadius_eq_one_iff (radiusSq₂ p),
    lyapunovExponent_eq_radiusPairSpectrum]
  rcases limitingSquaredRadius_cases (radiusSq₁ p) with h₁ | h₁ | h₁ <;>
    rcases limitingSquaredRadius_cases (radiusSq₂ p) with h₂ | h₂ | h₂
  all_goals rw [h₁, h₂]
  all_goals try rw [descending_radiusPairSpectrum_swap c 1 0]
  all_goals try rw [descending_radiusPairSpectrum_swap c 2 0]
  all_goals try rw [descending_radiusPairSpectrum_swap c 2 1]
  all_goals norm_num [descending_radiusPairSpectrum_zero_zero hc,
    descending_radiusPairSpectrum_zero_one hc, descending_radiusPairSpectrum_zero_two hc,
    descending_radiusPairSpectrum_one_one hc, descending_radiusPairSpectrum_one_two hc,
    descending_radiusPairSpectrum_two_two hc, spectrumPartialSum, spectrumEntry,
    Finset.sum_range_succ]

theorem exponentSum_four_eq_iff {c : ℝ} (hc : 4 < c) {p : PhaseSpace}
    (hp : p ∈ attractor) : spectrumPartialSum (lyapunovExponent c p) 4 = 4 ↔ p ∈ torus := by
  rw [(exponentSum_four_bound_and_eq hc p).2]
  change (radiusSq₁ p = 1 ∧ radiusSq₂ p = 1) ↔
    radiusSq₁ p = 1 ∧ radiusSq₂ p = 1 ∧ p 4 = 0
  simp [hp.2.2]

theorem exponentSum_five {c : ℝ} (hc : 4 < c) (p : PhaseSpace) :
    spectrumPartialSum (lyapunovExponent c p) 5 =
      spectrumPartialSum (lyapunovExponent c p) 4 - c := by
  rw [show (5 : ℕ) = 4 + 1 from rfl, spectrumPartialSum_succ]
  simp [spectrumEntry, lyapunovExponent_fifth hc, sub_eq_add_neg]

theorem exponentSum_on_torus {c : ℝ} (hc : 4 < c) {p : PhaseSpace}
    (hp : p ∈ torus) : lyapunovExponent c p = ![2, 2, 0, 0, -c] := by
  rw [lyapunovExponent_eq_radiusPairSpectrum, hp.1, hp.2.1]
  norm_num [limitingSquaredRadius]
  exact descending_radiusPairSpectrum_one_one hc

theorem exponentSum_le_twice_index {c : ℝ} (hc : 4 < c) (p : PhaseSpace)
    (k : ℕ) : spectrumPartialSum (lyapunovExponent c p) k ≤ (k : ℝ) * 2 := by
  calc
    _ ≤ ∑ _i ∈ Finset.range k, (2 : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      simp only [spectrumEntry]
      split_ifs with h
      · exact (lyapunovExponent_bounds hc p ⟨i, h⟩).2
      · norm_num
    _ = _ := by simp

/-- Supremum of the sum at each point, not a sum of separate suprema. -/
def supremumExponentSum (c : ℝ) (k : ℕ) : ℝ :=
  sSup ((fun p => spectrumPartialSum (lyapunovExponent c p) k) '' attractor)

theorem exponentSum_image_bddAbove {c : ℝ} (hc : 4 < c) (k : ℕ) :
    BddAbove ((fun p => spectrumPartialSum (lyapunovExponent c p) k) '' attractor) := by
  refine ⟨(k : ℝ) * 2, ?_⟩
  rintro x ⟨p, hp, rfl⟩
  exact exponentSum_le_twice_index hc p k

theorem exponentSum_four_isGreatest {c : ℝ} (hc : 4 < c) :
    IsGreatest ((fun p => spectrumPartialSum (lyapunovExponent c p) 4) '' attractor) 4 := by
  constructor
  · obtain ⟨p, hp⟩ := torus_nonempty
    exact ⟨p, torus_subset_attractor hp,
      (exponentSum_four_eq_iff hc (torus_subset_attractor hp)).mpr hp⟩
  · rintro x ⟨p, hp, rfl⟩
    exact (exponentSum_four_bound_and_eq hc p).1

theorem exponentSum_five_isGreatest {c : ℝ} (hc : 4 < c) :
    IsGreatest ((fun p => spectrumPartialSum (lyapunovExponent c p) 5) '' attractor)
      (4 - c) := by
  constructor
  · obtain ⟨p, hp, he⟩ := (exponentSum_four_isGreatest hc).1
    exact ⟨p, hp, by dsimp only at he ⊢; rw [exponentSum_five hc, he]⟩
  · rintro x ⟨p, hp, rfl⟩
    dsimp only
    rw [exponentSum_five hc]
    linarith [(exponentSum_four_bound_and_eq hc p).1]

theorem supremumExponentSum_four {c : ℝ} (hc : 4 < c) :
    supremumExponentSum c 4 = 4 := (exponentSum_four_isGreatest hc).csSup_eq

theorem supremumExponentSum_five {c : ℝ} (hc : 4 < c) :
    supremumExponentSum c 5 = 4 - c := (exponentSum_five_isGreatest hc).csSup_eq

theorem supremumExponentSum_nonneg {c : ℝ} (hc : 4 < c) {k : ℕ} (hk : k ≤ 4) :
    0 ≤ supremumExponentSum c k := by
  obtain ⟨p, hp⟩ := torus_nonempty
  have hle := le_csSup (exponentSum_image_bddAbove hc k)
    (Set.mem_image_of_mem (fun p => spectrumPartialSum (lyapunovExponent c p) k)
      (torus_subset_attractor hp))
  apply le_trans (b := spectrumPartialSum (lyapunovExponent c p) k) _ hle
  rw [exponentSum_on_torus hc hp]
  interval_cases k <;> norm_num [spectrumPartialSum, spectrumEntry, Finset.sum_range_succ]

end Eden
