import Eden.DimensionConvergenceCriteria
import Eden.NeutralDimensionBounds
import Eden.LimitingInterpolation

/-!
# Convergence to the Kaplan--Yorke dimension on the attractor

The nine ordered pairs of limiting squared radii reduce to the six limiting
spectra. Strict positivity handles the expanding spectra; nonnegative
tangential factors supply the lower bounds for the neutral spectra.
All limits are along real time tending to positive infinity.
-/

noncomputable section
open Set Filter
open scoped Topology
namespace Eden

theorem tendsto_finiteTimeDimension_of_asymptotic_zero (c : ℝ) (p : PhaseSpace)
    (h : asymptoticDimension c p = 0) :
    Tendsto (fun t => finiteTimeDimension c t p) atTop (𝓝 (asymptoticDimension c p)) := by
  apply tendsto_finiteTimeDimension_of_eventual_lower_bound c p
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [h]
  exact (finiteTimeDimension_mem_interval c ht.le p).1

theorem tendsto_finiteTimeDimension_of_spectrum_pos (c : ℝ) (p : PhaseSpace)
    (a : Fin 5 → ℝ) (ha : lyapunovExponent c p = a)
    (hpos : ∀ d ∈ Ioo 0 (kaplanYorkeDimension a), 0 < spectrumInterpolation a d) :
    Tendsto (fun t => finiteTimeDimension c t p) atTop (𝓝 (asymptoticDimension c p)) := by
  apply tendsto_finiteTimeDimension_of_interpolation_pos c p
  intro d hd
  rw [ha]
  exact hpos d (by simpa only [asymptoticDimension, ha] using hd)

private theorem convergence_zero_one {c : ℝ} (hc : 4 < c) (p : PhaseSpace)
    (ha : lyapunovExponent c p = ![2, 0, -2, -2, -c]) :
    Tendsto (fun t => finiteTimeDimension c t p) atTop (𝓝 (asymptoticDimension c p)) := by
  apply tendsto_finiteTimeDimension_of_spectrum_pos c p _ ha
  intro d hd
  rw [kaplanYorkeDimension_zero_one hc] at hd
  exact spectrumInterpolation_pos_zero_one hd

private theorem convergence_one_one {c : ℝ} (hc : 4 < c) (p : PhaseSpace)
    (ha : lyapunovExponent c p = ![2, 2, 0, 0, -c]) :
    Tendsto (fun t => finiteTimeDimension c t p) atTop (𝓝 (asymptoticDimension c p)) := by
  apply tendsto_finiteTimeDimension_of_spectrum_pos c p _ ha
  intro d hd
  rw [kaplanYorkeDimension_one_one hc] at hd
  exact spectrumInterpolation_pos_one_one hc hd

private theorem convergence_one_two {c : ℝ} (hc : 4 < c) (p : PhaseSpace)
    (ha : lyapunovExponent c p = ![2, 0, 0, -4, -c]) :
    Tendsto (fun t => finiteTimeDimension c t p) atTop (𝓝 (asymptoticDimension c p)) := by
  apply tendsto_finiteTimeDimension_of_spectrum_pos c p _ ha
  intro d hd
  rw [kaplanYorkeDimension_one_two hc] at hd
  exact spectrumInterpolation_pos_one_two hd

/-- The pointwise dimension limit, including every boundary radius
and both neutral rows of the limiting spectrum table. -/
theorem tendsto_finiteTimeDimension {c : ℝ} (hc : 4 < c)
    {p : PhaseSpace} (hp : p ∈ attractor) :
    Tendsto (fun t => finiteTimeDimension c t p) atTop (𝓝 (asymptoticDimension c p)) := by
  have ha := lyapunovExponent_eq_radiusPairSpectrum c p
  rcases limitingSquaredRadius_cases (radiusSq₁ p) with h₁ | h₁ | h₁ <;>
    rcases limitingSquaredRadius_cases (radiusSq₂ p) with h₂ | h₂ | h₂
  all_goals rw [h₁, h₂] at ha
  · apply tendsto_finiteTimeDimension_of_asymptotic_zero c p
    rw [asymptoticDimension, ha, descending_radiusPairSpectrum_zero_zero hc,
      kaplanYorkeDimension_zero_zero hc]
  · exact convergence_zero_one hc p
      (ha.trans (descending_radiusPairSpectrum_zero_one hc))
  · have hdim : asymptoticDimension c p = 1 := by
      rw [asymptoticDimension, ha, descending_radiusPairSpectrum_zero_two hc,
        kaplanYorkeDimension_zero_two hc]
    apply tendsto_finiteTimeDimension_of_eventual_lower_bound c p
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [hdim]
    exact finiteTimeDimension_ge_one_of_second_radius c ht hp
      (one_lt_of_limitingSquaredRadius_eq_two h₂).le
  · rw [descending_radiusPairSpectrum_swap c 1 0] at ha
    exact convergence_zero_one hc p
      (ha.trans (descending_radiusPairSpectrum_zero_one hc))
  · exact convergence_one_one hc p
      (ha.trans (descending_radiusPairSpectrum_one_one hc))
  · exact convergence_one_two hc p
      (ha.trans (descending_radiusPairSpectrum_one_two hc))
  · rw [descending_radiusPairSpectrum_swap c 2 0] at ha
    have hdim : asymptoticDimension c p = 1 := by
      rw [asymptoticDimension, ha, descending_radiusPairSpectrum_zero_two hc,
        kaplanYorkeDimension_zero_two hc]
    apply tendsto_finiteTimeDimension_of_eventual_lower_bound c p
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [hdim]
    exact finiteTimeDimension_ge_one_of_first_radius c ht hp
      (one_lt_of_limitingSquaredRadius_eq_two h₁).le
  · rw [descending_radiusPairSpectrum_swap c 2 1] at ha
    exact convergence_one_two hc p
      (ha.trans (descending_radiusPairSpectrum_one_two hc))
  · have hdim : asymptoticDimension c p = 2 := by
      rw [asymptoticDimension, ha, descending_radiusPairSpectrum_two_two hc,
        kaplanYorkeDimension_two_two hc]
    apply tendsto_finiteTimeDimension_of_eventual_lower_bound c p
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [hdim]
    exact finiteTimeDimension_ge_two_of_radii c ht hp
      (one_lt_of_limitingSquaredRadius_eq_two h₁).le
      (one_lt_of_limitingSquaredRadius_eq_two h₂).le

end Eden
