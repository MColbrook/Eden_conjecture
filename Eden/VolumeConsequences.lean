import Eden.VolumeGrowth
import Eden.Uniqueness

/-!
# Strict separation of planar growth and logarithmic volume growth

These are consequences for the evolution and its ambient Euclidean derivative.
-/

noncomputable section
namespace Eden

theorem exp_fifth_lt_planar_bound {c t : ℝ} (hc : 4 < c) (ht : 0 < t) :
    Real.exp (-c * t) < Real.exp (-4 * t) :=
  Real.exp_lt_exp.mpr (by nlinarith)

theorem derivativeFactors_planar_lower_bound (c : ℝ) {t : ℝ} (ht : 0 ≤ t)
    {p : PhaseSpace} (hp : p ∈ attractor) (i : Fin 4) :
    Real.exp (-4 * t) ≤ derivativeFactors c t p i.castSucc := by
  have h₂ : Real.exp (-4 * t) ≤ Real.exp (-2 * t) :=
    Real.exp_le_exp.mpr (by linarith)
  fin_cases i
  · exact radialAmplitude_lower_bound ht (radiusSq₁_nonneg p) hp.1
  · exact h₂.trans (planarAmplitude_lower_bound ht (radiusSq₁_nonneg p) hp.1)
  · exact radialAmplitude_lower_bound ht (radiusSq₂_nonneg p) hp.2.1
  · exact h₂.trans (planarAmplitude_lower_bound ht (radiusSq₂_nonneg p) hp.2.1)

/-- On A, at positive time and c>4, each of the four planar entries of the ambient
orthogonal factorisation strictly exceeds its fifth entry. The planar entries
here are in block order, not descending order. -/
theorem derivativeFactors_fifth_lt_planar {c t : ℝ} (hc : 4 < c) (ht : 0 < t)
    {p : PhaseSpace} (hp : p ∈ attractor) (i : Fin 4) :
    derivativeFactors c t p 4 < derivativeFactors c t p i.castSucc :=
  (exp_fifth_lt_planar_bound hc ht).trans_le (derivativeFactors_planar_lower_bound c ht.le hp i)

theorem continuousOn_volumeDefect_integrand (c : ℝ) (p : PhaseSpace) :
    ContinuousOn (fun τ => (radiusSq₁ (evolution c τ p) - 1) ^ 2 +
      (radiusSq₂ (evolution c τ p) - 1) ^ 2) (Set.Ici 0) :=
  (((continuous_radiusSq₁.comp_continuousOn (continuousOn_evolution c p)).sub
    continuousOn_const).pow 2).add
    (((continuous_radiusSq₂.comp_continuousOn (continuousOn_evolution c p)).sub
      continuousOn_const).pow 2)

theorem volumeDefect_integrand_nonneg (c τ : ℝ) (p : PhaseSpace) :
    0 ≤ (radiusSq₁ (evolution c τ p) - 1) ^ 2 +
      (radiusSq₂ (evolution c τ p) - 1) ^ 2 :=
  add_nonneg (sq_nonneg _) (sq_nonneg _)

/-- The logarithm of the product of the four largest ordered ambient singular
values, on A for c>=4 and t>=0, equals the exact integrated rate. -/
theorem log_singularValues_fderiv_evolution_prod_four {c t : ℝ}
    (hc : 4 ≤ c) (ht : 0 ≤ t) {p : PhaseSpace} (hp : p ∈ attractor) :
    Real.log (∏ i : Fin 4, (fderiv ℝ (evolution c t) p).toLinearMap.singularValues i) =
      4 * t - 6 * volumeDefect t p := by
  rw [singularValues_fderiv_evolution_prod_four hc ht hp, Real.log_exp]

end Eden
