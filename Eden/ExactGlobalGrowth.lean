import Eden.GlobalGrowthLimits
import Eden.FiniteTimeDimension
import Eden.OrderedStationarySpectrum

/-!
# Exact fourth and fifth global growth rates

The sharp spatial suprema follow from the derivative formulas on A
and are attained on the invariant torus, including at time zero.
-/

noncomputable section
open Set Filter Topology
namespace Eden

/-- Sharp spatial suprema for k=4,5, valid at every nonnegative real time. -/
theorem supremumSingularProduct_four_five {c t : ℝ} (hc : 4 ≤ c) (ht : 0 ≤ t)
    {k : ℕ} (hk₄ : 4 ≤ k) (hk₅ : k ≤ 5) :
    supremumSingularProduct c k t =
      Real.exp (4 * t - c * t * ((k : ℝ) - 4)) := by
  have hl : (4 : ℝ) ≤ k := by exact_mod_cast hk₄
  have hu : (k : ℝ) ≤ 5 := by exact_mod_cast hk₅
  apply le_antisymm
  · apply csSup_le (integerGrowthValues_nonempty c k t)
    rintro x ⟨p, hp, rfl⟩
    dsimp only
    rw [singularValueFunction_evolution_on_four_five hc ht hp hl hu]
    exact Real.exp_le_exp.mpr (by linarith [volumeDefect_nonneg ht p])
  · obtain ⟨p, hp⟩ := torus_nonempty
    have ha := torus_subset_attractor hp
    have he : volumeDefect t p = 0 := by
      simp [volumeDefect, hp.1, hp.2.1]
    have hv := singularValueFunction_le_supremum hk₅ hc ht ha
    rw [singularValueFunction_evolution_on_four_five hc ht ha hl hu, he] at hv
    simpa using hv

/-- The fourth logarithmic spatial supremum equals 4t, including t=0. -/
theorem globalLogGrowth_four {c t : ℝ} (hc : 4 ≤ c) (ht : 0 ≤ t) :
    globalLogGrowth c 4 t = 4 * t := by
  rw [globalLogGrowth, supremumSingularProduct_four_five hc ht (by norm_num) (by norm_num)]
  simp

/-- The fifth logarithmic spatial supremum equals (4-c)t, including t=0. -/
theorem globalLogGrowth_five {c t : ℝ} (hc : 4 ≤ c) (ht : 0 ≤ t) :
    globalLogGrowth c 5 t = (4 - c) * t := by
  rw [globalLogGrowth, supremumSingularProduct_four_five hc ht (by norm_num) (by norm_num),
    Real.log_exp]
  norm_num
  ring

/-- The ordinary real-time fourth global growth rate is four for c≥4. -/
theorem globalGrowthRate_four {c : ℝ} (hc : 4 ≤ c) : globalGrowthRate c 4 = 4 := by
  apply Tendsto.limUnder_eq
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [globalLogGrowth_four hc ht.le, mul_div_cancel_right₀ _ ht.ne']

/-- The ordinary real-time fifth global growth rate is 4-c for c≥4. -/
theorem globalGrowthRate_five {c : ℝ} (hc : 4 ≤ c) : globalGrowthRate c 5 = 4 - c := by
  apply Tendsto.limUnder_eq
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [globalLogGrowth_five hc ht.le, mul_div_cancel_right₀ _ ht.ne']

theorem globalLogGrowth_index_zero {c t : ℝ} (hc : 4 ≤ c) (ht : 0 ≤ t) :
    globalLogGrowth c 0 t = 0 := by
  have hb := globalLogGrowth_bounds (k := 0) (by omega) hc ht
  norm_num at hb
  exact le_antisymm hb.2 hb.1

theorem globalGrowthRate_zero {c : ℝ} (hc : 4 ≤ c) : globalGrowthRate c 0 = 0 := by
  apply Tendsto.limUnder_eq
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  simp [globalLogGrowth_index_zero hc ht]

theorem singularValueFunction_torus_integer_ge_one {k : ℕ} (hk : k ≤ 4)
    {c t : ℝ} (hc : 0 ≤ c) (ht : 0 ≤ t) {p : PhaseSpace} (hp : p ∈ torus) :
    1 ≤ singularValueFunction (fderiv ℝ (evolution c t) p).toLinearMap k := by
  rw [singularValueFunction_integer_eq_fin_prod _ (by omega)]
  apply Finset.one_le_prod
  intro i hi
  have hentry (j : Fin 5) (hj : j.val < 4) :
      1 ≤ (fderiv ℝ (evolution c t) p).toLinearMap.singularValues j := by
    have hv := congrFun (singularValues_on_torus hc ht hp) j
    have he : 1 ≤ Real.exp (2 * t) := Real.one_le_exp_iff.mpr (by positivity)
    fin_cases j <;> simp_all
  exact hentry (Fin.castLE (by omega) i) (lt_of_lt_of_le i.isLt hk)

theorem globalLogGrowth_nonneg {k : ℕ} (hk : k ≤ 4) {c t : ℝ}
    (hc : 4 ≤ c) (ht : 0 ≤ t) : 0 ≤ globalLogGrowth c k t := by
  obtain ⟨p, hp⟩ := torus_nonempty
  apply Real.log_nonneg
  exact (singularValueFunction_torus_integer_ge_one hk (by linarith) ht hp).trans
    (singularValueFunction_le_supremum (by omega) hc ht (torus_subset_attractor hp))

theorem globalGrowthRate_nonneg {k : ℕ} (hk : k ≤ 4) {c : ℝ} (hc : 4 ≤ c) :
    0 ≤ globalGrowthRate c k := by
  apply ge_of_tendsto (tendsto_globalGrowthRate (by omega) hc)
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  exact div_nonneg (globalLogGrowth_nonneg hk hc ht) ht

theorem globalGrowthRate_five_neg {c : ℝ} (hc : 4 < c) : globalGrowthRate c 5 < 0 := by
  rw [globalGrowthRate_five hc.le]
  linarith

end Eden
