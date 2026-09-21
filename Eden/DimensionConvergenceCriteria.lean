import Eden.FiniteTimeKaplanYorke

/-!
# Criteria for convergence of the finite-time dimension

The upper bound follows from strict negativity past the final zero of the
limiting interpolant. Separate lower bounds cover both the expanding and
neutral spectra.
-/

noncomputable section
open Set Filter
open scoped Topology
namespace Eden

theorem tendsto_spectrumInterpolation_normalized (c : ℝ) (p : PhaseSpace) (d : ℝ) :
    Tendsto (fun t => spectrumInterpolation (normalizedLogSingularValues c t p) d)
      atTop (𝓝 (spectrumInterpolation (lyapunovExponent c p) d)) := by
  exact (tendstoUniformly_spectrumInterpolation
    (tendsto_pi_nhds.mpr (fun i => tendsto_lyapunovExponent c p i))).tendsto_at d

theorem eventually_finiteTimeDimension_lt (c : ℝ) (p : PhaseSpace) {u : ℝ}
    (hu : asymptoticDimension c p < u) :
    ∀ᶠ t in atTop, finiteTimeDimension c t p < u := by
  by_cases h₅ : 5 < u
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    exact (finiteTimeDimension_mem_interval c ht.le p).2.trans_lt h₅
  have hb := kaplanYorkeDimension_mem_interval (lyapunovExponent c p)
  let d := (asymptoticDimension c p + u) / 2
  have hd : d ∈ Icc 0 5 := by
    have hb₀ : 0 ≤ asymptoticDimension c p := hb.1
    constructor <;> dsimp [d] <;> linarith
  have hneg : spectrumInterpolation (lyapunovExponent c p) d < 0 :=
    (spectrumInterpolation_neg_iff (lyapunovExponent_antitone c p) hd).mpr
      (by change asymptoticDimension c p < d; dsimp [d]; linarith)
  have he := (tendsto_spectrumInterpolation_normalized c p d).eventually
    (Iio_mem_nhds hneg)
  filter_upwards [he, eventually_gt_atTop (0 : ℝ)] with t htneg ht
  rw [finiteTimeDimension_eq_kaplanYorke c ht p]
  have hlt := (spectrumInterpolation_neg_iff
    (normalizedLogSingularValues_antitone c ht p) hd).mp htneg
  exact hlt.trans (by dsimp [d]; linarith)

theorem tendsto_finiteTimeDimension_of_lower_tests (c : ℝ) (p : PhaseSpace)
    (hlo : ∀ d ∈ Ioo 0 (asymptoticDimension c p),
      ∀ᶠ t in atTop, d ≤ finiteTimeDimension c t p) :
    Tendsto (fun t => finiteTimeDimension c t p) atTop (𝓝 (asymptoticDimension c p)) := by
  apply tendsto_order.mpr
  constructor
  · intro l hl
    by_cases hl₀ : l < 0
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      exact hl₀.trans_le (finiteTimeDimension_mem_interval c ht.le p).1
    let d := (l + asymptoticDimension c p) / 2
    have hd : d ∈ Ioo 0 (asymptoticDimension c p) := by
      constructor <;> dsimp [d] <;> linarith
    filter_upwards [hlo d hd] with t ht
    exact (show l < d by dsimp [d]; linarith).trans_le ht
  · exact fun _ hu => eventually_finiteTimeDimension_lt c p hu

theorem tendsto_finiteTimeDimension_of_interpolation_pos (c : ℝ) (p : PhaseSpace)
    (hpos : ∀ d ∈ Ioo 0 (asymptoticDimension c p),
      0 < spectrumInterpolation (lyapunovExponent c p) d) :
    Tendsto (fun t => finiteTimeDimension c t p) atTop (𝓝 (asymptoticDimension c p)) := by
  apply tendsto_finiteTimeDimension_of_lower_tests c p
  intro d hd
  have hd₅ : d ∈ Icc 0 5 := ⟨hd.1.le, hd.2.le.trans
    (kaplanYorkeDimension_mem_interval (lyapunovExponent c p)).2⟩
  have he := (tendsto_spectrumInterpolation_normalized c p d).eventually
    (Ioi_mem_nhds (hpos d hd))
  filter_upwards [he, eventually_gt_atTop (0 : ℝ)] with t htpos ht
  rw [finiteTimeDimension_eq_kaplanYorke c ht p]
  exact (spectrumInterpolation_nonneg_iff
    (normalizedLogSingularValues_antitone c ht p) hd₅).mp (le_of_lt htpos)

theorem tendsto_finiteTimeDimension_of_eventual_lower_bound (c : ℝ) (p : PhaseSpace)
    (hlo : ∀ᶠ t in atTop, asymptoticDimension c p ≤ finiteTimeDimension c t p) :
    Tendsto (fun t => finiteTimeDimension c t p) atTop (𝓝 (asymptoticDimension c p)) := by
  apply tendsto_finiteTimeDimension_of_lower_tests c p
  intro d hd
  filter_upwards [hlo] with t ht
  exact hd.2.le.trans ht

end Eden
