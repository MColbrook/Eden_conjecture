import Eden.PeriodicGap
import Eden.ExteriorCocycle

/-!
# Growth maximised over the periodic and equilibrium set

The spatial supremum is formed from the ambient singular values before the
ordinary real-time limit. The unit periodic circles attain every integer product
maximum; the origin and outer circles give componentwise smaller ordered rates.
-/

noncomputable section
open Set Filter Topology
namespace Eden

theorem normalizedLogSingularValues_periodic_le_unit {c t : ℝ}
    (hc : 4 < c) (ht : 0 < t) {p : PhaseSpace}
    (hp : p ∈ periodicEquilibriumSet c) :
    ∀ i : Fin 5, normalizedLogSingularValues c t p i ≤ ![2, 0, -2, -2, -c] i := by
  rw [periodicEquilibriumSet_eq_positiveReturnSet (show 0 < c by linarith)] at hp
  rcases (mem_positiveReturnSet_iff (by linarith) p).mp hp with rfl | h | h | h | h
  · have hzero : normalizedLogSingularValues c t 0 = ![-2, -2, -2, -2, -c] := by
      rw [normalizedLogSingularValues_of_stationary_radii c ht 0
        (Or.inl (by simp [radiusSq₁])) (Or.inl (by simp [radiusSq₂]))]
      simpa [radiusSq₁, radiusSq₂] using descending_radiusPairSpectrum_zero_zero hc
    rw [hzero]
    intro i; fin_cases i <;> norm_num
  · rw [normalizedLogSingularValues_unit_circle hc ht (Or.inl h)]
    exact fun _ => le_rfl
  · rw [normalizedLogSingularValues_outer_circle hc ht (Or.inl h)]
    intro i; fin_cases i <;> norm_num
  · rw [normalizedLogSingularValues_unit_circle hc ht (Or.inr h)]
    exact fun _ => le_rfl
  · rw [normalizedLogSingularValues_outer_circle hc ht (Or.inr h)]
    intro i; fin_cases i <;> norm_num

theorem spectrumInterpolation_mono_spectrum {a b : Fin 5 → ℝ}
    (h : ∀ i, a i ≤ b i) (d : ℝ) : spectrumInterpolation a d ≤ spectrumInterpolation b d := by
  exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (h i)
    (singularWeight_bounds i d).1)

theorem spectrumInterpolation_integer (a : Fin 5 → ℝ) {k : ℕ} (hk : k ≤ 5) :
    spectrumInterpolation a k = spectrumPartialSum a k := by
  rcases eq_or_lt_of_le hk with rfl | hk
  · exact spectrumInterpolation_five a
  · simpa using spectrumInterpolation_interpolate a hk (α := 0) le_rfl zero_le_one

theorem singularValueFunction_evolution_eq_exp_interpolation (c : ℝ) {t : ℝ}
    (ht : 0 < t) (p : PhaseSpace) (d : ℝ) :
    singularValueFunction (fderiv ℝ (evolution c t) p).toLinearMap d =
      Real.exp (t * spectrumInterpolation (normalizedLogSingularValues c t p) d) := by
  calc
    _ = Real.exp (Real.log (singularValueFunction
        (fderiv ℝ (evolution c t) p).toLinearMap d)) :=
      (Real.exp_log (singularValueFunction_evolution_pos c ht.le p d)).symm
    _ = _ := by
      congr 1
      have h := (div_eq_iff ht.ne').mp (log_singularValueFunction_div_time c ht p d)
      linarith

/-- Integer singular-value products over the full periodic/equilibrium set. -/
def periodicIntegerGrowthValues (c : ℝ) (k : ℕ) (t : ℝ) : Set ℝ :=
  (fun p => singularValueFunction (fderiv ℝ (evolution c t) p).toLinearMap k) ''
    periodicEquilibriumSet c

/-- The spatial supremum precedes the logarithm. -/
def periodicGlobalLogGrowth (c : ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  Real.log (sSup (periodicIntegerGrowthValues c k t))

/-- The real-time growth limit of the logarithmic spatial supremum. -/
def periodicGlobalGrowthRate (c : ℝ) (k : ℕ) : ℝ :=
  limUnder atTop (fun t : ℝ => periodicGlobalLogGrowth c k t / t)

/-- Every integer product maximum is attained on a unit periodic circle, including
t=0. -/
theorem periodicIntegerGrowthValues_isGreatest {c t : ℝ} (hc : 4 < c)
    (ht : 0 ≤ t) {k : ℕ} (hk : k ≤ 5) :
    IsGreatest (periodicIntegerGrowthValues c k t)
      (Real.exp (t * spectrumPartialSum ![2, 0, -2, -2, -c] k)) := by
  obtain ⟨q, hq⟩ := firstCircle_nonempty (show (0 : ℝ) ≤ 1 by norm_num)
  have hqP : q ∈ periodicEquilibriumSet c := by
    rw [periodicEquilibriumSet_eq_positiveReturnSet (show 0 < c by linarith)]
    exact (mem_positiveReturnSet_iff (by linarith) q).mpr (Or.inr (Or.inl hq))
  rcases eq_or_lt_of_le ht with rfl | ht
  · constructor
    · refine ⟨q, hqP, ?_⟩
      simp [singularValueFunction_integer_evolution_zero hk]
    · rintro x ⟨p, hp, rfl⟩
      simp [singularValueFunction_integer_evolution_zero hk]
  constructor
  · refine ⟨q, hqP, ?_⟩
    dsimp only
    rw [singularValueFunction_evolution_eq_exp_interpolation c ht,
      normalizedLogSingularValues_unit_circle hc ht (Or.inl hq),
      spectrumInterpolation_integer _ hk]
  · rintro x ⟨p, hp, rfl⟩
    dsimp only
    rw [singularValueFunction_evolution_eq_exp_interpolation c ht]
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ ht.le
    exact (spectrumInterpolation_mono_spectrum
      (normalizedLogSingularValues_periodic_le_unit hc ht hp) k).trans_eq
      (spectrumInterpolation_integer _ hk)

/-- The logarithmic spatial supremum is linear in every nonnegative real time. -/
theorem periodicGlobalLogGrowth_eq {c t : ℝ} (hc : 4 < c) (ht : 0 ≤ t)
    {k : ℕ} (hk : k ≤ 5) :
    periodicGlobalLogGrowth c k t = t * spectrumPartialSum ![2, 0, -2, -2, -c] k := by
  rw [periodicGlobalLogGrowth, (periodicIntegerGrowthValues_isGreatest hc ht hk).csSup_eq,
    Real.log_exp]

theorem tendsto_periodicGlobalLogGrowth_div {c : ℝ} (hc : 4 < c)
    {k : ℕ} (hk : k ≤ 5) :
    Tendsto (fun t : ℝ => periodicGlobalLogGrowth c k t / t) atTop
      (𝓝 (spectrumPartialSum ![2, 0, -2, -2, -c] k)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [periodicGlobalLogGrowth_eq hc ht.le hk, mul_div_cancel_left₀ _ ht.ne']

theorem periodicGlobalGrowthRate_eq {c : ℝ} (hc : 4 < c) {k : ℕ} (hk : k ≤ 5) :
    periodicGlobalGrowthRate c k = spectrumPartialSum ![2, 0, -2, -2, -c] k :=
  (tendsto_periodicGlobalLogGrowth_div hc hk).limUnder_eq

/-- All six global sums, including the empty sum at index zero. -/
theorem periodicGlobalGrowthRate_table {c : ℝ} (hc : 4 < c) :
    (fun k : Fin 6 => periodicGlobalGrowthRate c k) = ![0, 2, 2, 0, -2, -2 - c] := by
  funext k
  rw [periodicGlobalGrowthRate_eq hc (by omega)]
  fin_cases k <;> norm_num [spectrumPartialSum, spectrumEntry, Finset.sum_range_succ]
  all_goals ring

end Eden
