import Eden.FactorBounds

/-!
# The sharp four-dimensional volume growth

The rate identity `a(s) + b(s) = 2 - 6(s-1)^2` is integrated along trajectories.
Its nonnegative defect vanishes exactly at unit initial radius. The fifth
singular value and the full singular-value multiset identify the product of the
four largest singular values, including its equality set. The integral arguments
reuse Mathlib's interval-integral additivity, monotonicity and strict positivity
on an interval.
-/

noncomputable section
open Set
namespace Eden

/-- The integral defect for one squared radius, nonnegative when `t ≥ 0`. -/
def radialDefect (t s : ℝ) : ℝ :=
  ∫ τ in (0 : ℝ)..t, (squaredRadiusEvolution τ s - 1) ^ 2

private theorem defect_intervalIntegrable {t : ℝ} (ht : 0 ≤ t) (s : ℝ) :
    IntervalIntegrable (fun τ => (squaredRadiusEvolution τ s - 1) ^ 2)
      MeasureTheory.volume 0 t := by
  have hc := (((continuousOn_squaredRadiusEvolution_time s).mono
    (show Icc 0 t ⊆ Ici 0 from fun _ h => h.1)).sub
      (continuousOn_const (c := (1 : ℝ)))).pow 2
  exact hc.intervalIntegrable_of_Icc ht

theorem radialDefect_nonneg {t : ℝ} (ht : 0 ≤ t) (s : ℝ) : 0 ≤ radialDefect t s :=
  intervalIntegral.integral_nonneg_of_forall ht (fun _ => sq_nonneg _)

@[simp] theorem radialDefect_at_one (t : ℝ) : radialDefect t 1 = 0 := by
  simp [radialDefect]

theorem radialDefect_pos {t s : ℝ} (ht : 0 < t) (hs : s ≠ 1) :
    0 < radialDefect t s := by
  apply intervalIntegral.intervalIntegral_pos_of_pos_on (defect_intervalIntegrable ht.le s)
    (fun τ hτ => ?_) ht
  apply sq_pos_of_ne_zero
  apply sub_ne_zero.mpr
  intro heq
  have hinj := (strictMono_squaredRadiusEvolution hτ.1.le).injective
  exact hs (hinj (heq.trans (squaredRadiusEvolution_at_one τ).symm))

theorem radialDefect_eq_zero_iff {t s : ℝ} (ht : 0 < t) :
    radialDefect t s = 0 ↔ s = 1 := by
  constructor
  · intro h
    by_contra hs
    exact (ne_of_gt (radialDefect_pos ht hs)) h
  · rintro rfl
    exact radialDefect_at_one t

theorem log_planar_factors {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    Real.log (radialAmplitude t s) + Real.log (planarAmplitude t s) =
      2 * t - 6 * radialDefect t s := by
  have hcont := (continuousOn_squaredRadiusEvolution_time s).mono
    (show Icc 0 t ⊆ Ici 0 from fun _ h => h.1)
  have ha : Continuous radialRate := by unfold radialRate; fun_prop
  have hb : Continuous tangentialRate := by unfold tangentialRate; fun_prop
  have hai := (ha.comp_continuousOn hcont).intervalIntegrable_of_Icc
    (μ := MeasureTheory.volume) ht
  have hbi := (hb.comp_continuousOn hcont).intervalIntegrable_of_Icc
    (μ := MeasureTheory.volume) ht
  simp only [Function.comp_def] at hai hbi
  rw [log_radialAmplitude_eq_integral ht hs, log_planarAmplitude_eq_integral ht hs,
    ← intervalIntegral.integral_add hai hbi]
  simp_rw [rates_sum]
  rw [intervalIntegral.integral_sub intervalIntegrable_const
    ((defect_intervalIntegrable ht s).const_mul 6), intervalIntegral.integral_const_mul]
  simp [radialDefect, mul_comm]

theorem planar_factors_product {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    radialAmplitude t s * planarAmplitude t s = Real.exp (2 * t - 6 * radialDefect t s) := by
  rw [← log_planar_factors ht hs, Real.exp_add,
    Real.exp_log (radialAmplitude_pos ht hs), Real.exp_log (planarAmplitude_pos ht hs)]

/-- The manuscript's sum of the two radial integral defects. -/
def volumeDefect (t : ℝ) (p : PhaseSpace) : ℝ :=
  radialDefect t (radiusSq₁ p) + radialDefect t (radiusSq₂ p)

/-- This is exactly the manuscript's integral along the trajectory. -/
theorem volumeDefect_eq_integral_evolution (c : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (p : PhaseSpace) :
    volumeDefect t p = ∫ τ in (0 : ℝ)..t,
      ((radiusSq₁ (evolution c τ p) - 1) ^ 2 +
        (radiusSq₂ (evolution c τ p) - 1) ^ 2) := by
  unfold volumeDefect radialDefect
  rw [← intervalIntegral.integral_add (defect_intervalIntegrable ht (radiusSq₁ p))
    (defect_intervalIntegrable ht (radiusSq₂ p))]
  apply intervalIntegral.integral_congr
  intro τ hτ
  have hτ₀ : 0 ≤ τ := (uIcc_of_le ht ▸ hτ).1
  dsimp only
  rw [radiusSq₁_evolution c hτ₀, radiusSq₂_evolution c hτ₀]

theorem volumeDefect_nonneg {t : ℝ} (ht : 0 ≤ t) (p : PhaseSpace) :
    0 ≤ volumeDefect t p :=
  add_nonneg (radialDefect_nonneg ht _) (radialDefect_nonneg ht _)

theorem volumeDefect_eq_zero_iff {t : ℝ} (ht : 0 < t)
    {p : PhaseSpace} (hp : p ∈ attractor) : volumeDefect t p = 0 ↔ p ∈ torus := by
  have h₁ := radialDefect_nonneg ht.le (radiusSq₁ p)
  have h₂ := radialDefect_nonneg ht.le (radiusSq₂ p)
  constructor
  · intro hz
    have hz₁ : radialDefect t (radiusSq₁ p) = 0 := by dsimp [volumeDefect] at hz; linarith
    have hz₂ : radialDefect t (radiusSq₂ p) = 0 := by dsimp [volumeDefect] at hz; linarith
    exact ⟨(radialDefect_eq_zero_iff ht).1 hz₁,
      (radialDefect_eq_zero_iff ht).1 hz₂, hp.2.2⟩
  · intro hT
    simp [volumeDefect, hT.1, hT.2.1]

/-- Product of the first four standard, descending ambient singular values. -/
theorem singularValues_fderiv_evolution_prod_four {c t : ℝ} (hc : 4 ≤ c) (ht : 0 ≤ t)
    {p : PhaseSpace} (hp : p ∈ attractor) :
    (∏ i : Fin 4, (fderiv ℝ (evolution c t) p).toLinearMap.singularValues i) =
      Real.exp (4 * t - 6 * volumeDefect t p) := by
  let A := (fderiv ℝ (evolution c t) p).toLinearMap
  have hm := congrArg Multiset.prod (singularValues_fderiv_evolution c ht p)
  have hprod : (∏ i : Fin 5, A.singularValues i) = ∏ i : Fin 5, derivativeFactors c t p i := by
    simpa only [Finset.prod_eq_multiset_prod] using hm
  rw [Fin.prod_univ_castSucc] at hprod
  have hlast := singularValues_fderiv_evolution_fifth hc ht hp
  change A.singularValues 4 = _ at hlast
  simp only [Fin.val_castSucc, Fin.val_last] at hprod
  rw [hlast] at hprod
  have hright : (∏ i : Fin 5, derivativeFactors c t p i) =
      Real.exp (4 * t - 6 * volumeDefect t p) * Real.exp (-c * t) := by
    rw [Fin.prod_univ_five]
    change radialAmplitude t (radiusSq₁ p) * planarAmplitude t (radiusSq₁ p) *
      radialAmplitude t (radiusSq₂ p) * planarAmplitude t (radiusSq₂ p) *
      Real.exp (-c * t) = _
    rw [mul_assoc (radialAmplitude t (radiusSq₁ p) * planarAmplitude t (radiusSq₁ p))
      (radialAmplitude t (radiusSq₂ p)) (planarAmplitude t (radiusSq₂ p)),
      planar_factors_product ht (radiusSq₁_nonneg p),
      planar_factors_product ht (radiusSq₂_nonneg p), ← Real.exp_add]
    congr 2
    dsimp [volumeDefect]
    ring
  rw [hright] at hprod
  exact mul_right_cancel₀ (ne_of_gt (Real.exp_pos _)) hprod

theorem singularValues_fderiv_evolution_prod_four_le {c t : ℝ}
    (hc : 4 ≤ c) (ht : 0 ≤ t) {p : PhaseSpace} (hp : p ∈ attractor) :
    (∏ i : Fin 4, (fderiv ℝ (evolution c t) p).toLinearMap.singularValues i) ≤
      Real.exp (4 * t) := by
  rw [singularValues_fderiv_evolution_prod_four hc ht hp]
  exact Real.exp_le_exp.mpr (by linarith [volumeDefect_nonneg ht p])

theorem singularValues_fderiv_evolution_prod_four_eq_iff {c t : ℝ}
    (hc : 4 ≤ c) (ht : 0 < t) {p : PhaseSpace} (hp : p ∈ attractor) :
    (∏ i : Fin 4, (fderiv ℝ (evolution c t) p).toLinearMap.singularValues i) =
      Real.exp (4 * t) ↔ p ∈ torus := by
  rw [singularValues_fderiv_evolution_prod_four hc ht.le hp, Real.exp_eq_exp]
  rw [← volumeDefect_eq_zero_iff ht hp]
  constructor <;> intro h <;> linarith

end Eden
