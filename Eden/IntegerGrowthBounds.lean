import Eden.ExteriorCocycle
import Eden.FactorBounds

/-!
# Uniform bounds for integer singular-value growth

The polynomial rates have elementary global upper bounds. Integration and
the lower bounds on A give two-sided estimates for every integer product.
-/

noncomputable section
open Set
namespace Eden

theorem radialRate_upper_bound (s : ℝ) : radialRate s ≤ 3 := by
  dsimp [radialRate]
  nlinarith [sq_nonneg (10 * s - 9)]

theorem tangentialRate_upper_bound (s : ℝ) : tangentialRate s ≤ 3 := by
  dsimp [tangentialRate]
  nlinarith [sq_nonneg (2 * s - 3)]

private theorem growth_rate_intervalIntegrable {f : ℝ → ℝ} (hf : Continuous f)
    {t : ℝ} (ht : 0 ≤ t) (s : ℝ) :
    IntervalIntegrable (fun τ => f (squaredRadiusEvolution τ s))
      MeasureTheory.volume 0 t :=
  (hf.comp_continuousOn ((continuousOn_squaredRadiusEvolution_time s).mono
    (show Icc 0 t ⊆ Ici 0 from fun _ h => h.1))).intervalIntegrable_of_Icc ht

theorem log_radialAmplitude_upper_bound {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    Real.log (radialAmplitude t s) ≤ 3 * t := by
  rw [log_radialAmplitude_eq_integral ht hs]
  have ha : Continuous radialRate := by unfold radialRate; fun_prop
  have hi := intervalIntegral.integral_mono_on ht (growth_rate_intervalIntegrable ha ht s)
    (intervalIntegrable_const (c := (3 : ℝ))) (fun τ _ => radialRate_upper_bound _)
  simpa [mul_comm] using hi

theorem log_planarAmplitude_upper_bound {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    Real.log (planarAmplitude t s) ≤ 3 * t := by
  rw [log_planarAmplitude_eq_integral ht hs]
  have hb : Continuous tangentialRate := by unfold tangentialRate; fun_prop
  have hi := intervalIntegral.integral_mono_on ht (growth_rate_intervalIntegrable hb ht s)
    (intervalIntegrable_const (c := (3 : ℝ))) (fun τ _ => tangentialRate_upper_bound _)
  simpa [mul_comm] using hi

theorem radialAmplitude_upper_bound {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    radialAmplitude t s ≤ Real.exp (3 * t) := by
  simpa only [Real.exp_log (radialAmplitude_pos ht hs)] using
    Real.exp_le_exp.mpr (log_radialAmplitude_upper_bound ht hs)

theorem planarAmplitude_upper_bound {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    planarAmplitude t s ≤ Real.exp (3 * t) := by
  simpa only [Real.exp_log (planarAmplitude_pos ht hs)] using
    Real.exp_le_exp.mpr (log_planarAmplitude_upper_bound ht hs)

theorem derivativeFactors_upper_bound {c t : ℝ} (hc : 0 ≤ c) (ht : 0 ≤ t)
    (p : PhaseSpace) (i : Fin 5) : derivativeFactors c t p i ≤ Real.exp (3 * t) := by
  fin_cases i
  · exact radialAmplitude_upper_bound ht (radiusSq₁_nonneg p)
  · exact planarAmplitude_upper_bound ht (radiusSq₁_nonneg p)
  · exact radialAmplitude_upper_bound ht (radiusSq₂_nonneg p)
  · exact planarAmplitude_upper_bound ht (radiusSq₂_nonneg p)
  · exact Real.exp_le_exp.mpr (by nlinarith)

theorem singularValues_evolution_bounds {c t : ℝ} (hc : 4 ≤ c) (ht : 0 ≤ t)
    {p : PhaseSpace} (hp : p ∈ attractor) (i : Fin 5) :
    Real.exp (-c * t) ≤ (fderiv ℝ (evolution c t) p).toLinearMap.singularValues i ∧
      (fderiv ℝ (evolution c t) p).toLinearMap.singularValues i ≤ Real.exp (3 * t) := by
  obtain ⟨e, he⟩ := exists_equiv_of_multiset_eq (singularValues_fderiv_evolution c ht p)
  rw [← he i]
  exact ⟨derivativeFactors_ge_fifth hc ht hp (e i),
    derivativeFactors_upper_bound (by linarith) ht p (e i)⟩

/-- Explicit bounds on the nonnegative time domain, including t=0 and k=0. -/
theorem singularValueFunction_integer_evolution_bounds {k : ℕ} (hk : k ≤ 5)
    {c t : ℝ} (hc : 4 ≤ c) (ht : 0 ≤ t) {p : PhaseSpace} (hp : p ∈ attractor) :
    Real.exp ((k : ℝ) * (-c * t)) ≤
        singularValueFunction (fderiv ℝ (evolution c t) p).toLinearMap k ∧
      singularValueFunction (fderiv ℝ (evolution c t) p).toLinearMap k ≤
        Real.exp ((k : ℝ) * (3 * t)) := by
  rw [singularValueFunction_integer_eq_fin_prod _ hk]
  constructor
  · calc
      _ = ∏ _i : Fin k, Real.exp (-c * t) := by
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Real.exp_nat_mul]
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => (Real.exp_pos _).le)
        (fun i _ => (singularValues_evolution_bounds hc ht hp (Fin.castLE hk i)).1)
  · calc
      _ ≤ ∏ _i : Fin k, Real.exp (3 * t) := Finset.prod_le_prod
        (fun i _ => (singularValues_evolution_pos c ht p (Fin.castLE hk i)).le)
        (fun i _ => (singularValues_evolution_bounds hc ht hp (Fin.castLE hk i)).2)
      _ = _ := by
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Real.exp_nat_mul]

end Eden
