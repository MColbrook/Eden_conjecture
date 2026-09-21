import Eden.InvariantSets
import Eden.GrowthRates
import Eden.SingularValues

/-!
# Lower bounds for the derivative factors on the invariant discs

Integration of the polynomial rate bounds along the radial evolution gives
bounds for the derivative factors. The ordered singular-value multiset then
identifies the fifth singular value. The proof uses Mathlib's
interval-integral monotonicity.
-/

noncomputable section
open Set
namespace Eden

private theorem rate_intervalIntegrable {f : ℝ → ℝ} (hf : Continuous f)
    {t : ℝ} (ht : 0 ≤ t) (s : ℝ) :
    IntervalIntegrable (fun τ => f (squaredRadiusEvolution τ s))
      MeasureTheory.volume 0 t :=
  (hf.comp_continuousOn ((continuousOn_squaredRadiusEvolution_time s).mono
    (show Icc 0 t ⊆ Ici 0 from fun _ h => h.1))).intervalIntegrable_of_Icc ht

theorem log_radialAmplitude_lower_bound {t s : ℝ} (ht : 0 ≤ t)
    (hs₀ : 0 ≤ s) (hs₂ : s ≤ 2) : -4 * t ≤ Real.log (radialAmplitude t s) := by
  rw [log_radialAmplitude_eq_integral ht hs₀]
  have ha : Continuous radialRate := by unfold radialRate; fun_prop
  have hi := intervalIntegral.integral_mono_on ht
    (intervalIntegrable_const (c := (-4 : ℝ))) (rate_intervalIntegrable ha ht s)
    (fun τ hτ => radialRate_lower_bound
      (squaredRadiusEvolution_nonneg hτ.1 hs₀)
      ((squaredRadiusEvolution_le_two_iff hτ.1).2 hs₂))
  simpa [mul_comm] using hi

theorem log_planarAmplitude_lower_bound {t s : ℝ} (ht : 0 ≤ t)
    (hs₀ : 0 ≤ s) (hs₂ : s ≤ 2) : -2 * t ≤ Real.log (planarAmplitude t s) := by
  rw [log_planarAmplitude_eq_integral ht hs₀]
  have hb : Continuous tangentialRate := by unfold tangentialRate; fun_prop
  have hi := intervalIntegral.integral_mono_on ht
    (intervalIntegrable_const (c := (-2 : ℝ))) (rate_intervalIntegrable hb ht s)
    (fun τ hτ => tangentialRate_lower_bound
      (squaredRadiusEvolution_nonneg hτ.1 hs₀)
      ((squaredRadiusEvolution_le_two_iff hτ.1).2 hs₂))
  simpa [mul_comm] using hi

theorem radialAmplitude_lower_bound {t s : ℝ} (ht : 0 ≤ t)
    (hs₀ : 0 ≤ s) (hs₂ : s ≤ 2) : Real.exp (-4 * t) ≤ radialAmplitude t s := by
  simpa only [Real.exp_log (radialAmplitude_pos ht hs₀)] using
    Real.exp_le_exp.mpr (log_radialAmplitude_lower_bound ht hs₀ hs₂)

theorem planarAmplitude_lower_bound {t s : ℝ} (ht : 0 ≤ t)
    (hs₀ : 0 ≤ s) (hs₂ : s ≤ 2) : Real.exp (-2 * t) ≤ planarAmplitude t s := by
  simpa only [Real.exp_log (planarAmplitude_pos ht hs₀)] using
    Real.exp_le_exp.mpr (log_planarAmplitude_lower_bound ht hs₀ hs₂)

/-- On the invariant squared-radius interval [1,2], tangential growth has
nonnegative logarithm at every forward time, including the neutral cases. -/
theorem log_planarAmplitude_nonneg {t s : ℝ} (ht : 0 ≤ t)
    (hs₁ : 1 ≤ s) (hs₂ : s ≤ 2) : 0 ≤ Real.log (planarAmplitude t s) := by
  rw [log_planarAmplitude_eq_integral ht (by linarith)]
  apply intervalIntegral.integral_nonneg ht
  intro τ hτ
  apply tangentialRate_nonneg
  · have h := (strictMono_squaredRadiusEvolution hτ.1).monotone hs₁
    simpa using h
  · exact (squaredRadiusEvolution_le_two_iff hτ.1).mpr hs₂

theorem one_le_planarAmplitude {t s : ℝ} (ht : 0 ≤ t)
    (hs₁ : 1 ≤ s) (hs₂ : s ≤ 2) : 1 ≤ planarAmplitude t s := by
  simpa only [Real.exp_zero, Real.exp_log (planarAmplitude_pos ht (by linarith))] using
    Real.exp_le_exp.mpr (log_planarAmplitude_nonneg ht hs₁ hs₂)

theorem derivativeFactors_ge_fifth {c t : ℝ} (hc : 4 ≤ c) (ht : 0 ≤ t)
    {p : PhaseSpace} (hp : p ∈ attractor) (i : Fin 5) :
    Real.exp (-c * t) ≤ derivativeFactors c t p i := by
  have h₄ : Real.exp (-c * t) ≤ Real.exp (-4 * t) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have h₂ : Real.exp (-c * t) ≤ Real.exp (-2 * t) :=
    Real.exp_le_exp.mpr (by nlinarith)
  fin_cases i
  · exact h₄.trans (radialAmplitude_lower_bound ht (radiusSq₁_nonneg p) hp.1)
  · exact h₂.trans (planarAmplitude_lower_bound ht (radiusSq₁_nonneg p) hp.1)
  · exact h₄.trans (radialAmplitude_lower_bound ht (radiusSq₂_nonneg p) hp.2.1)
  · exact h₂.trans (planarAmplitude_lower_bound ht (radiusSq₂_nonneg p) hp.2.1)
  · exact le_rfl

/-- Mathlib indexes the five ambient singular values from zero. -/
theorem singularValues_fderiv_evolution_fifth {c t : ℝ} (hc : 4 ≤ c) (ht : 0 ≤ t)
    {p : PhaseSpace} (hp : p ∈ attractor) :
    (fderiv ℝ (evolution c t) p).toLinearMap.singularValues 4 = Real.exp (-c * t) := by
  let A := (fderiv ℝ (evolution c t) p).toLinearMap
  have hm := singularValues_fderiv_evolution c ht p
  have hf : Real.exp (-c * t) ∈
      Finset.univ.val.map (fun i : Fin 5 => derivativeFactors c t p i) := by
    exact Multiset.mem_map.mpr ⟨4, by simp, rfl⟩
  rw [← hm] at hf
  obtain ⟨i, _, hi⟩ := Multiset.mem_map.mp hf
  have hle : A.singularValues 4 ≤ Real.exp (-c * t) := by
    rw [← hi]
    exact A.singularValues_antitone (by omega)
  have hs : A.singularValues 4 ∈
      Finset.univ.val.map (fun i : Fin 5 => A.singularValues i) :=
    Multiset.mem_map.mpr ⟨4, by simp, rfl⟩
  change A.singularValues 4 ∈ _ at hs
  rw [hm] at hs
  obtain ⟨j, _, hj⟩ := Multiset.mem_map.mp hs
  exact le_antisymm hle (hj ▸ derivativeFactors_ge_fifth hc ht hp j)

end Eden
