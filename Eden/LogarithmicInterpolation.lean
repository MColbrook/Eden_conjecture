import Eden.KaplanYorke
import Eden.SingularValueFunction
import Mathlib.Topology.MetricSpace.UniformConvergence

/-!
# Uniform convergence of logarithmic singular-value interpolation

The same truncated weights as the singular-value function define
the logarithmic interpolant. Their bounds give a uniform constant-five
estimate in the maximum metric on spectra, for every real dimension.
The resulting uniform convergence statement covers the full interval [0,5].

The proof reuses Mathlib's logarithm-of-product and positive real-power
identities, finite-sum bounds and metric characterisation of uniform
convergence. All singular values refer to the Euclidean derivative.
-/

noncomputable section
open Set Filter
open scoped Topology
namespace Eden

/-- Piecewise linear interpolation of the partial sums of a five-entry spectrum. -/
def spectrumInterpolation (a : Fin 5 → ℝ) (d : ℝ) : ℝ :=
  ∑ i : Fin 5, singularWeight i d * a i

theorem singularWeight_bounds (i : ℕ) (d : ℝ) :
    0 ≤ singularWeight i d ∧ singularWeight i d ≤ 1 := by
  exact ⟨le_min (by norm_num) (le_max_left _ _), min_le_left _ _⟩

theorem continuous_spectrumInterpolation (a : Fin 5 → ℝ) :
    Continuous (spectrumInterpolation a) := by
  unfold spectrumInterpolation
  exact continuous_finsetSum _ (fun i _ => (continuous_singularWeight i).mul continuous_const)

theorem spectrumInterpolation_eq_range (a : Fin 5 → ℝ) (d : ℝ) :
    spectrumInterpolation a d =
      ∑ i ∈ Finset.range 5, singularWeight i d * spectrumEntry a i := by
  calc
    _ = ∑ i : Fin 5, singularWeight i d * spectrumEntry a i := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [spectrumEntry]
    _ = _ := Fin.sum_univ_eq_sum_range (fun i => singularWeight i d * spectrumEntry a i) 5

theorem spectrumInterpolation_interpolate (a : Fin 5 → ℝ) {k : ℕ} (hk : k < 5)
    {α : ℝ} (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) :
    spectrumInterpolation a ((k : ℝ) + α) =
      spectrumPartialSum a k + α * spectrumEntry a k := by
  rw [spectrumInterpolation_eq_range]
  have htrunc : (∑ i ∈ Finset.range (k + 1),
      singularWeight i ((k : ℝ) + α) * spectrumEntry a i) =
      ∑ i ∈ Finset.range 5, singularWeight i ((k : ℝ) + α) * spectrumEntry a i := by
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro i hi hnot
    have hki : k < i := by simp only [Finset.mem_range] at hnot; omega
    rw [singularWeight_eq_zero hki hα₁, zero_mul]
  rw [← htrunc, Finset.sum_range_succ, singularWeight_eq_fraction k hα₀ hα₁]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [singularWeight_eq_one (Finset.mem_range.mp hi) hα₀, one_mul]

@[simp] theorem spectrumInterpolation_zero (a : Fin 5 → ℝ) :
    spectrumInterpolation a 0 = 0 := by
  simp [spectrumInterpolation, singularWeight]

theorem spectrumInterpolation_five (a : Fin 5 → ℝ) :
    spectrumInterpolation a 5 = spectrumPartialSum a 5 := by
  rw [spectrumInterpolation_eq_range]
  apply Finset.sum_congr rfl
  intro i hi
  have h := singularWeight_eq_one (Finset.mem_range.mp hi) (le_refl (0 : ℝ))
  norm_num only [Nat.cast_ofNat, add_zero] at h
  rw [h, one_mul]

/-- A bound uniform in dimension, including both endpoints. -/
theorem spectrumInterpolation_dist_le (a b : Fin 5 → ℝ) (d : ℝ) :
    dist (spectrumInterpolation a d) (spectrumInterpolation b d) ≤ 5 * dist a b := by
  rw [Real.dist_eq]
  unfold spectrumInterpolation
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i : Fin 5, |singularWeight i d * a i - singularWeight i d * b i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin 5, dist a b := by
      apply Finset.sum_le_sum
      intro i hi
      rw [← mul_sub, abs_mul, abs_of_nonneg (singularWeight_bounds i d).1]
      calc
        _ ≤ |a i - b i| := mul_le_of_le_one_left (abs_nonneg _) (singularWeight_bounds i d).2
        _ ≤ dist a b := by simpa only [Real.dist_eq] using dist_le_pi_dist a b i
    _ = _ := by simp

theorem log_singularValueFunction_div_time (c : ℝ) {t : ℝ} (ht : 0 < t)
    (p : PhaseSpace) (d : ℝ) :
    Real.log (singularValueFunction (fderiv ℝ (evolution c t) p).toLinearMap d) / t =
      spectrumInterpolation (normalizedLogSingularValues c t p) d := by
  unfold singularValueFunction spectralProduct spectrumInterpolation
  rw [← Fin.prod_univ_eq_prod_range]
  rw [Real.log_prod (fun i _ => ne_of_gt (Real.rpow_pos_of_pos
    (singularValues_evolution_pos c ht.le p i) _)), Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Real.log_rpow (singularValues_evolution_pos c ht.le p i)]
  simp only [normalizedLogSingularValues, mul_div_assoc]

theorem tendstoUniformly_spectrumInterpolation {a : ℝ → Fin 5 → ℝ} {b : Fin 5 → ℝ}
    (h : Tendsto a atTop (𝓝 b)) :
    TendstoUniformly (fun t d => spectrumInterpolation (a t) d) (spectrumInterpolation b) atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp h (ε / 5) (by positivity)
  filter_upwards [eventually_ge_atTop N] with t ht d
  have hdist : dist b (a t) < ε / 5 := by simpa only [dist_comm] using hN t ht
  exact (spectrumInterpolation_dist_le b (a t) d).trans_lt (by linarith)

/-- Uniform real-time convergence on the complete dimension interval. -/
theorem tendstoUniformlyOn_log_singularValueFunction (c : ℝ) (p : PhaseSpace) :
    TendstoUniformlyOn (fun t d => Real.log
      (singularValueFunction (fderiv ℝ (evolution c t) p).toLinearMap d) / t)
      (spectrumInterpolation (lyapunovExponent c p)) atTop (Icc 0 5) := by
  have hvec : Tendsto (fun t => normalizedLogSingularValues c t p) atTop
      (𝓝 (lyapunovExponent c p)) :=
    tendsto_pi_nhds.mpr (fun i => tendsto_lyapunovExponent c p i)
  have h := Metric.tendstoUniformly_iff.mp (tendstoUniformly_spectrumInterpolation hvec)
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [h ε hε, eventually_gt_atTop (0 : ℝ)] with t hbound ht d hd
  rw [log_singularValueFunction_div_time c ht p d]
  exact hbound d

end Eden
