import Eden.InterpolationSign

/-!
# The finite-time dimension and the ordered logarithmic spectrum

The definition by the singular-value function agrees with the Kaplan--Yorke
formula for the ambient derivative at each positive real time.
The comparison includes dimensions zero and five and all zero partial sums.
-/

noncomputable section
open Set
namespace Eden

theorem singularValueFunction_evolution_pos (c : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (p : PhaseSpace) (d : ℝ) :
    0 < singularValueFunction (fderiv ℝ (evolution c t) p).toLinearMap d := by
  unfold singularValueFunction spectralProduct
  rw [← Fin.prod_univ_eq_prod_range]
  exact Finset.prod_pos (fun i _ => Real.rpow_pos_of_pos
    (singularValues_evolution_pos c ht p i) _)

theorem one_le_singularValueFunction_iff_interpolation (c : ℝ) {t : ℝ} (ht : 0 < t)
    (p : PhaseSpace) (d : ℝ) :
    1 ≤ singularValueFunction (fderiv ℝ (evolution c t) p).toLinearMap d ↔
      0 ≤ spectrumInterpolation (normalizedLogSingularValues c t p) d := by
  rw [← log_singularValueFunction_div_time c ht p d, le_div_iff₀ ht, zero_mul]
  exact (Real.log_nonneg_iff (singularValueFunction_evolution_pos c ht.le p d)).symm

theorem admissibleDimensions_evolution_eq (c : ℝ) {t : ℝ} (ht : 0 < t)
    (p : PhaseSpace) :
    admissibleDimensions (fderiv ℝ (evolution c t) p).toLinearMap =
      Icc 0 (kaplanYorkeDimension (normalizedLogSingularValues c t p)) := by
  ext d
  constructor
  · rintro ⟨hd, hω⟩
    exact ⟨hd.1, (spectrumInterpolation_nonneg_iff
      (normalizedLogSingularValues_antitone c ht p) hd).mp
      ((one_le_singularValueFunction_iff_interpolation c ht p d).mp hω)⟩
  · intro hd
    have hd₅ : d ∈ Icc 0 5 := ⟨hd.1, hd.2.trans
      (kaplanYorkeDimension_mem_interval (normalizedLogSingularValues c t p)).2⟩
    exact ⟨hd₅, (one_le_singularValueFunction_iff_interpolation c ht p d).mpr
      ((spectrumInterpolation_nonneg_iff
        (normalizedLogSingularValues_antitone c ht p) hd₅).mpr hd.2)⟩

/-- At every positive real time, the dimension defined from the ambient derivative equals the Kaplan--Yorke formula applied to its ordered
singular-value logarithms divided by time. -/
theorem finiteTimeDimension_eq_kaplanYorke (c : ℝ) {t : ℝ} (ht : 0 < t)
    (p : PhaseSpace) :
    finiteTimeDimension c t p =
      kaplanYorkeDimension (normalizedLogSingularValues c t p) := by
  have hmax := finiteTimeDimension_isGreatest c ht.le p
  rw [admissibleDimensions_evolution_eq c ht p] at hmax
  exact le_antisymm hmax.1.2 (hmax.2
    ⟨(kaplanYorkeDimension_mem_interval (normalizedLogSingularValues c t p)).1, le_rfl⟩)

end Eden
