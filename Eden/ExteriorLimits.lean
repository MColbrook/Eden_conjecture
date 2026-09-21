import Eden.ExteriorGeometry
import Eden.LogarithmicSums
import Eden.FactorLimits

/-!
# Limits for fixed exterior vectors

The exact squared norm is a finite sum of positive squares after zero
coordinates have been removed. Its growth is the largest rate among the
nonzero coordinates, with respect to the fixed initial orthonormal frame.
This proves existence along real time for every nonzero exterior vector.
-/

noncomputable section
open Filter Set
open scoped Topology
namespace Eden

/-- The sum of the limiting block exponents selected by an exterior index. -/
def exteriorRate (k : ℕ) (c : ℝ) (p : PhaseSpace) (s : ExteriorIndex k) : ℝ :=
  ∑ i : Fin k, factorExponents c p (Set.powersetCard.ofFinEmbEquiv.symm s i)

/-- Nonzero coordinates in the fixed initial exterior frame. -/
def exteriorSupport (k : ℕ) (p : PhaseSpace) (v : ExteriorSpace k) : Finset (ExteriorIndex k) :=
  Finset.univ.filter (fun s => exteriorInitialCoordinates k p v s ≠ 0)

theorem exteriorSupport_nonempty {k : ℕ} (p : PhaseSpace) {v : ExteriorSpace k} (hv : v ≠ 0) :
    (exteriorSupport k p v).Nonempty := by
  classical
  have h := exteriorInitialCoordinates_ne_zero p hv
  by_contra hn
  apply h
  ext s
  have hnot : ¬s ∈ exteriorSupport k p v := fun hs => hn ⟨s, hs⟩
  simpa [exteriorSupport] using hnot

theorem exteriorFactor_pos (k : ℕ) (c : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (p : PhaseSpace) (s : ExteriorIndex k) :
    0 < exteriorFactor k (derivativeFactors c t p) s :=
  Finset.prod_pos (fun _ _ => derivativeFactors_pos c ht p _)

theorem tendsto_log_exteriorFactor_div (k : ℕ) (c : ℝ) (p : PhaseSpace) (s : ExteriorIndex k) :
    Tendsto (fun t => Real.log (exteriorFactor k (derivativeFactors c t p) s) / t)
      atTop (𝓝 (exteriorRate k c p s)) := by
  have h := tendsto_finsetSum Finset.univ (fun i _ =>
    tendsto_log_derivativeFactors_div c p (Set.powersetCard.ofFinEmbEquiv.symm s i))
  apply h.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  simp only [exteriorFactor, Real.log_prod (fun i _ =>
    (derivativeFactors_pos c ht p (Set.powersetCard.ofFinEmbEquiv.symm s i)).ne'), Finset.sum_div]

theorem norm_sq_exteriorEvolution_support (k : ℕ) (c : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (p : PhaseSpace) (v : ExteriorSpace k) :
    ‖exteriorEvolution k c t p v‖ ^ 2 = ∑ s ∈ exteriorSupport k p v,
      (exteriorFactor k (derivativeFactors c t p) s * exteriorInitialCoordinates k p v s) ^ 2 := by
  classical
  rw [norm_sq_exteriorEvolution k c ht]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro s _ hs
  have hz : exteriorInitialCoordinates k p v s = 0 := by simpa [exteriorSupport] using hs
  simp [hz]

theorem tendsto_log_exterior_coordinate_sq_div (k : ℕ) (c : ℝ) (p : PhaseSpace)
    (s : ExteriorIndex k) {a : ℝ} (ha : a ≠ 0) :
    Tendsto (fun t => Real.log ((exteriorFactor k (derivativeFactors c t p) s * a) ^ 2) / t)
      atTop (𝓝 (2 * exteriorRate k c p s)) := by
  have hc : Tendsto (fun t : ℝ => Real.log a / t) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have h := ((tendsto_log_exteriorFactor_div k c p s).add hc).const_mul 2
  simp only [add_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  rw [Real.log_pow, Real.log_mul (exteriorFactor_pos k c ht p s).ne' ha]
  push_cast
  ring

/-- Every fixed nonzero exterior vector has an ordinary logarithmic growth
limit. Its value is the greatest sum of block exponents with a nonzero
initial coordinate; time ranges over all reals tending to infinity. -/
theorem tendsto_log_norm_exteriorEvolution_div {k : ℕ} (c : ℝ) (p : PhaseSpace)
    {v : ExteriorSpace k} (hv : v ≠ 0) :
    Tendsto (fun t => Real.log ‖exteriorEvolution k c t p v‖ / t) atTop
      (𝓝 ((exteriorSupport k p v).sup' (exteriorSupport_nonempty p hv) (exteriorRate k c p))) := by
  classical
  let s := exteriorSupport k p v
  have hs : s.Nonempty := exteriorSupport_nonempty p hv
  let f := fun j t => (exteriorFactor k (derivativeFactors c t p) j *
    exteriorInitialCoordinates k p v j) ^ 2
  have ha (j : ExteriorIndex k) (hj : j ∈ s) : exteriorInitialCoordinates k p v j ≠ 0 :=
    (Finset.mem_filter.mp hj).2
  have hp (j : ExteriorIndex k) (hj : j ∈ s) : ∀ᶠ t in atTop, 0 < f j t := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact sq_pos_of_ne_zero (mul_ne_zero (exteriorFactor_pos k c ht p j).ne' (ha j hj))
  have h := tendsto_log_finset_sum_div s hs f (fun j => 2 * exteriorRate k c p j) hp
    (fun j hj => tendsto_log_exterior_coordinate_sq_div k c p j (ha j hj))
  have hsup : s.sup' hs (fun j => 2 * exteriorRate k c p j) =
      2 * s.sup' hs (exteriorRate k c p) := by
    symm
    exact Finset.apply_sup'_eq_sup'_comp hs (fun r : ℝ => 2 * r)
      (fun x y => by exact mul_max_of_nonneg x y (show (0 : ℝ) ≤ 2 by norm_num))
  rw [hsup] at h
  have hhalf := h.div_const 2
  simp only [mul_div_cancel_left₀ _ (show (2 : ℝ) ≠ 0 by norm_num)] at hhalf
  apply hhalf.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  symm
  change Real.log ‖exteriorEvolution k c t p v‖ / t =
    (Real.log (∑ j ∈ exteriorSupport k p v,
      (exteriorFactor k (derivativeFactors c t p) j * exteriorInitialCoordinates k p v j) ^ 2) / t) / 2
  rw [← norm_sq_exteriorEvolution_support k c ht p v, Real.log_pow]
  push_cast
  ring

end Eden
