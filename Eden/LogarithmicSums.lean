import Eden.RealTimeAverages
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Real-time logarithmic growth of finite positive sums

The elementary squeeze max(f,g)<=f+g<=2*max(f,g) shows that a sum has
the larger of the two exponential growth rates. Finite induction retains
all terms and handles equal rates. The proof uses Mathlib's real logarithm,
filter squeeze theorem and finite-sum limit calculus.
-/

noncomputable section
open Filter Set
open scoped Topology
namespace Eden

theorem log_add_bounds {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    max (Real.log x) (Real.log y) ≤ Real.log (x + y) ∧
      Real.log (x + y) ≤ Real.log 2 + max (Real.log x) (Real.log y) := by
  have hlow : max (Real.log x) (Real.log y) ≤ Real.log (x + y) :=
    max_le (Real.log_le_log hx (by linarith)) (Real.log_le_log hy (by linarith))
  refine ⟨hlow, ?_⟩
  rcases le_total x y with h | h
  · rw [max_eq_right (Real.log_le_log hx h)]
    calc
      Real.log (x + y) ≤ Real.log (2 * y) := Real.log_le_log (by positivity) (by linarith)
      _ = Real.log 2 + Real.log y := Real.log_mul (by norm_num) hy.ne'
  · rw [max_eq_left (Real.log_le_log hy h)]
    calc
      Real.log (x + y) ≤ Real.log (2 * x) := Real.log_le_log (by positivity) (by linarith)
      _ = Real.log 2 + Real.log x := Real.log_mul (by norm_num) hx.ne'

theorem tendsto_log_add_div {f g : ℝ → ℝ} {a b : ℝ}
    (hfpos : ∀ᶠ t in atTop, 0 < f t) (hgpos : ∀ᶠ t in atTop, 0 < g t)
    (hf : Tendsto (fun t => Real.log (f t) / t) atTop (𝓝 a))
    (hg : Tendsto (fun t => Real.log (g t) / t) atTop (𝓝 b)) :
    Tendsto (fun t => Real.log (f t + g t) / t) atTop (𝓝 (max a b)) := by
  have hm := hf.max hg
  have hc : Tendsto (fun t : ℝ => Real.log 2 / t) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hm (by simpa using hc.add hm)
  · filter_upwards [hfpos, hgpos, eventually_gt_atTop (0 : ℝ)] with t hft hgt ht
    have h := (div_le_div_of_nonneg_right (log_add_bounds hft hgt).1 ht.le)
    simpa only [max_div_div_right ht.le] using h
  · filter_upwards [hfpos, hgpos, eventually_gt_atTop (0 : ℝ)] with t hft hgt ht
    have h := (div_le_div_of_nonneg_right (log_add_bounds hft hgt).2 ht.le)
    simpa only [add_div, max_div_div_right ht.le] using h

/-- Every nonempty finite positive sum has the maximal individual
logarithmic growth rate, along all real times tending to infinity. -/
theorem tendsto_log_finset_sum_div {I : Type*} (s : Finset I) (hs : s.Nonempty)
    (f : I → ℝ → ℝ) (a : I → ℝ)
    (hfpos : ∀ i ∈ s, ∀ᶠ t in atTop, 0 < f i t)
    (hf : ∀ i ∈ s, Tendsto (fun t => Real.log (f i t) / t) atTop (𝓝 (a i))) :
    Tendsto (fun t => Real.log (∑ i ∈ s, f i t) / t) atTop (𝓝 (s.sup' hs a)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp at hs
  | @insert i s hi ih =>
    by_cases hs' : s.Nonempty
    · have hsumpos : ∀ᶠ t in atTop, 0 < ∑ j ∈ s, f j t := by
        have hpos : ∀ᶠ t in atTop, ∀ j ∈ s, 0 < f j t :=
          (eventually_all_finset s).mpr (fun j hj => hfpos j (Finset.mem_insert_of_mem hj))
        filter_upwards [hpos] with t ht
        exact Finset.sum_pos ht hs'
      have h := tendsto_log_add_div (hfpos i (Finset.mem_insert_self _ _)) hsumpos
        (hf i (Finset.mem_insert_self _ _))
        (ih hs' (fun j hj => hfpos j (Finset.mem_insert_of_mem hj))
          (fun j hj => hf j (Finset.mem_insert_of_mem hj)))
      simpa [Finset.sum_insert hi, Finset.sup'_insert hs'] using h
    · have hz : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs'
      subst s
      simpa using hf i (Finset.mem_insert_self _ _)

end Eden
