import Eden.LogarithmicInterpolation

/-!
# The nonnegative region of the logarithmic interpolant

For a descending spectrum, the interpolant is nonnegative exactly up to the
Kaplan--Yorke dimension. The proof includes zero partial sums and uses the
Kaplan--Yorke index and Mathlib's finite-sum comparison.
-/

noncomputable section
open Set
namespace Eden

theorem spectrumEntry_antitone {a : Fin 5 → ℝ} (ha : Antitone a)
    {i j : ℕ} (hij : i ≤ j) (hj : j < 5) : spectrumEntry a j ≤ spectrumEntry a i := by
  have hi : i < 5 := lt_of_le_of_lt hij hj
  simp only [spectrumEntry, dif_pos hi, dif_pos hj]
  exact ha hij

theorem spectrumPartialSum_nonneg_of_le {a : Fin 5 → ℝ} (ha : Antitone a)
    {k j : ℕ} (hkj : k ≤ j) (hj : j ≤ 5) (hs : 0 ≤ spectrumPartialSum a j) :
    0 ≤ spectrumPartialSum a k := by
  rcases eq_or_lt_of_le hkj with rfl | hkj
  · exact hs
  have hk : k < 5 := lt_of_lt_of_le hkj hj
  by_contra h
  have hneg : spectrumPartialSum a k < 0 := lt_of_not_ge h
  have hkneg : spectrumEntry a k < 0 := by
    by_contra hn
    have hnonneg : 0 ≤ spectrumPartialSum a k := by
      apply Finset.sum_nonneg
      intro i hi
      exact (le_of_not_gt hn).trans
        (spectrumEntry_antitone ha (Finset.mem_range.mp hi).le hk)
    linarith
  have hsum : spectrumPartialSum a j ≤ spectrumPartialSum a k := by
    have hn : (∑ i ∈ Finset.range k, -spectrumEntry a i) ≤
        ∑ i ∈ Finset.range j, -spectrumEntry a i := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hkj.le)
      intro i hi hnot
      have hki : k ≤ i := by simp only [Finset.mem_range] at hnot; omega
      have hi₅ : i < 5 := lt_of_lt_of_le (Finset.mem_range.mp hi) hj
      exact neg_nonneg.mpr ((spectrumEntry_antitone ha hki hi₅).trans hkneg.le)
    simpa only [Finset.sum_neg_distrib, neg_le_neg_iff, spectrumPartialSum] using hn
  linarith

theorem kaplanYorkeIndex_le_dimension (a : Fin 5 → ℝ) :
    (kaplanYorkeIndex a : ℝ) ≤ kaplanYorkeDimension a := by
  by_cases h₀ : kaplanYorkeIndex a = 0
  · simp [h₀, kaplanYorkeDimension_of_index_zero h₀]
  by_cases h₅ : kaplanYorkeIndex a = 5
  · simp [h₅, kaplanYorkeDimension_of_index_five h₅]
  exact (kaplanYorkeDimension_between_index (by omega)
    (lt_of_le_of_ne (kaplanYorkeIndex_mem a).1 h₅)).1

theorem kaplanYorkeDimension_lt_succ_index {a : Fin 5 → ℝ}
    (hj : kaplanYorkeIndex a < 5) :
    kaplanYorkeDimension a < (kaplanYorkeIndex a : ℝ) + 1 := by
  by_cases h₀ : kaplanYorkeIndex a = 0
  · simp [h₀, kaplanYorkeDimension_of_index_zero h₀]
  exact (kaplanYorkeDimension_between_index (by omega) hj).2

theorem kaplanYorkeDimension_formula_of_index_lt_five {a : Fin 5 → ℝ}
    (hj : kaplanYorkeIndex a < 5) :
    kaplanYorkeDimension a = (kaplanYorkeIndex a : ℝ) +
      spectrumPartialSum a (kaplanYorkeIndex a) / -spectrumEntry a (kaplanYorkeIndex a) := by
  by_cases h₀ : kaplanYorkeIndex a = 0
  · simp [h₀, kaplanYorkeDimension_of_index_zero h₀]
  rw [kaplanYorkeDimension_of_index_between rfl (by omega) hj,
    abs_of_neg (spectrumEntry_at_kaplanYorkeIndex_neg hj)]

theorem spectrumInterpolation_index_criterion {a : Fin 5 → ℝ}
    (hj : kaplanYorkeIndex a < 5) (α : ℝ) :
    0 ≤ spectrumPartialSum a (kaplanYorkeIndex a) + α * spectrumEntry a (kaplanYorkeIndex a) ↔
      (kaplanYorkeIndex a : ℝ) + α ≤ kaplanYorkeDimension a := by
  rw [kaplanYorkeDimension_formula_of_index_lt_five hj, add_le_add_iff_left,
    le_div_iff₀ (show 0 < -spectrumEntry a (kaplanYorkeIndex a) from
      neg_pos.mpr (spectrumEntry_at_kaplanYorkeIndex_neg hj))]
  constructor <;> intro h <;> nlinarith

/-- Closed unit intervals cover all of [0,5], including dimension five. -/
theorem exists_dimension_segment {d : ℝ} (hd : d ∈ Icc 0 5) :
    ∃ k : ℕ, k < 5 ∧ ∃ α : ℝ, α ∈ Icc 0 1 ∧ d = (k : ℝ) + α := by
  by_cases h₁ : d ≤ 1
  · exact ⟨0, by omega, d, ⟨hd.1, h₁⟩, by simp⟩
  by_cases h₂ : d ≤ 2
  · exact ⟨1, by omega, d - 1, ⟨by linarith, by linarith⟩, by norm_num⟩
  by_cases h₃ : d ≤ 3
  · exact ⟨2, by omega, d - 2, ⟨by linarith, by linarith⟩, by norm_num⟩
  by_cases h₄ : d ≤ 4
  · exact ⟨3, by omega, d - 3, ⟨by linarith, by linarith⟩, by norm_num⟩
  exact ⟨4, by omega, d - 4, ⟨by linarith, by linarith [hd.2]⟩, by norm_num⟩

/-- For a descending spectrum and every dimension in `[0,5]`, the interpolant
is nonnegative exactly at or below the Kaplan--Yorke dimension. Zero partial
sums and both ambient endpoints are included. -/
theorem spectrumInterpolation_nonneg_iff {a : Fin 5 → ℝ} (ha : Antitone a)
    {d : ℝ} (hd : d ∈ Icc 0 5) :
    0 ≤ spectrumInterpolation a d ↔ d ≤ kaplanYorkeDimension a := by
  obtain ⟨k, hk, α, hα, rfl⟩ := exists_dimension_segment hd
  rw [spectrumInterpolation_interpolate a hk hα.1 hα.2]
  rcases lt_trichotomy k (kaplanYorkeIndex a) with hkj | hkj | hjk
  · have hs := kaplanYorkeIndex_mem a
    have hsk := spectrumPartialSum_nonneg_of_le ha hkj.le hs.1 hs.2
    have hsk₁ := spectrumPartialSum_nonneg_of_le ha
      (show k + 1 ≤ kaplanYorkeIndex a by omega) hs.1 hs.2
    have h₀ := mul_nonneg (sub_nonneg.mpr hα.2) hsk
    have h₁ := mul_nonneg hα.1 hsk₁
    rw [spectrumPartialSum_succ] at h₁
    have hn : 0 ≤ spectrumPartialSum a k + α * spectrumEntry a k := by nlinarith
    have hkreal : (k : ℝ) + 1 ≤ kaplanYorkeIndex a := by exact_mod_cast hkj
    have hle := kaplanYorkeIndex_le_dimension a
    exact iff_of_true hn (by linarith [hα.2])
  · subst k
    exact spectrumInterpolation_index_criterion hk α
  · have hsneg := spectrumPartialSum_after_index_neg hjk hk.le
    have hj₅ : kaplanYorkeIndex a < 5 := lt_trans hjk hk
    have haneg := (spectrumEntry_antitone ha hjk.le hk).trans_lt
      (spectrumEntry_at_kaplanYorkeIndex_neg hj₅)
    have hmul := mul_nonpos_of_nonneg_of_nonpos hα.1 haneg.le
    have hn : spectrumPartialSum a k + α * spectrumEntry a k < 0 := by linarith
    have hkreal : (kaplanYorkeIndex a : ℝ) + 1 ≤ k := by exact_mod_cast hjk
    have hdim := kaplanYorkeDimension_lt_succ_index hj₅
    exact iff_of_false (not_le_of_gt hn) (not_le_of_gt (by linarith [hα.1]))

theorem spectrumInterpolation_neg_iff {a : Fin 5 → ℝ} (ha : Antitone a)
    {d : ℝ} (hd : d ∈ Icc 0 5) :
    spectrumInterpolation a d < 0 ↔ kaplanYorkeDimension a < d := by
  simpa only [not_le] using not_congr (spectrumInterpolation_nonneg_iff ha hd)

end Eden
