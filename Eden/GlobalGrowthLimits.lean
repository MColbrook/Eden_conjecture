import Eden.RealSubadditive

/-!
# Limits of spatially maximised growth

The spatial supremum of each singular-value product precedes the logarithm
and the real-time limit.
-/

noncomputable section
open Set Filter Topology
namespace Eden

/-- The limiting logarithmic spatial growth rate. Existence
of the ordinary real-time limit is proved below for c≥4 and k≤5. -/
def globalGrowthRate (c : ℝ) (k : ℕ) : ℝ :=
  limUnder atTop (fun t : ℝ => globalLogGrowth c k t / t)

theorem tendsto_globalLogGrowth_div_inf {k : ℕ} (hk : k ≤ 5) {c : ℝ}
    (hc : 4 ≤ c) :
    Tendsto (fun t : ℝ => globalLogGrowth c k t / t) atTop
      (𝓝 (sInf ((fun T : ℝ => globalLogGrowth c k T / T) '' Ioi 0))) := by
  obtain ⟨C, hC, hb⟩ := exists_globalLogGrowth_linear_bound hk hc
  exact tendsto_real_subadditive_div
    (fun _ _ hs ht => globalLogGrowth_subadditive hk hc hs ht) hC hb

/-- For c≥4 and k≤5, the rate is the infimum over all positive real times. -/
theorem globalGrowthRate_eq_inf {k : ℕ} (hk : k ≤ 5) {c : ℝ} (hc : 4 ≤ c) :
    globalGrowthRate c k =
      sInf ((fun T : ℝ => globalLogGrowth c k T / T) '' Ioi 0) :=
  (tendsto_globalLogGrowth_div_inf hk hc).limUnder_eq

/-- Ordinary convergence through all real times for c≥4 and k≤5. -/
theorem tendsto_globalGrowthRate {k : ℕ} (hk : k ≤ 5) {c : ℝ} (hc : 4 ≤ c) :
    Tendsto (fun t : ℝ => globalLogGrowth c k t / t) atTop
      (𝓝 (globalGrowthRate c k)) := by
  rw [globalGrowthRate_eq_inf hk hc]
  exact tendsto_globalLogGrowth_div_inf hk hc

end Eden
