import Eden.InitialDerivative
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Integral expressions for the planar derivative factors

The time derivatives of the two positive scales are identified with
the radial and tangential rate polynomials. The fundamental theorem of
calculus then gives the exponential integral expressions in the manuscript.
The domain is every nonnegative initial squared radius and every nonnegative
time, including both zero endpoints.

The proof reuses Mathlib's logarithmic derivative. The interval-integral
fundamental theorem is due to Yury Kudryashov, Patrick Massot and Sébastien Gouëzel.
The identification of these factors with singular values is a separate step.
-/

noncomputable section
open Set
namespace Eden

theorem hasDerivAt_sqrt_radialDiscriminant {t : ℝ} (ht : 0 ≤ t) (s : ℝ) :
    HasDerivAt (fun τ => Real.sqrt (radialDiscriminant τ s))
      (-2 * (1 - (squaredRadiusEvolution t s - 1) ^ 2) *
        Real.sqrt (radialDiscriminant t s)) t := by
  have he : HasDerivAt (fun τ : ℝ => Real.exp (-4 * τ))
      (Real.exp (-4 * t) * (-4)) t := by
    simpa using ((hasDerivAt_id t).const_mul (-4 : ℝ)).exp
  have hd := he.add (((hasDerivAt_const t (1 : ℝ)).sub he).mul_const ((s - 1) ^ 2))
  have hr := hd.sqrt (ne_of_gt (radialDiscriminant_pos ht s))
  have hR := sqrt_radialDiscriminant_pos ht s
  have hsq := Real.sq_sqrt (le_of_lt (radialDiscriminant_pos ht s))
  apply hr.congr_deriv
  change (Real.exp (-4 * t) * (-4) +
      (0 - Real.exp (-4 * t) * (-4)) * (s - 1) ^ 2) /
      (2 * Real.sqrt (radialDiscriminant t s)) = _
  dsimp only [squaredRadiusEvolution]
  field_simp [ne_of_gt hR]
  dsimp only [radialDiscriminant] at hsq ⊢
  simp only [neg_mul] at hsq ⊢
  nlinarith

/-- The radial factor has the manuscript's radial logarithmic growth rate. -/
theorem hasDerivAt_radialAmplitude {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    HasDerivAt (fun τ => radialAmplitude τ s)
      (radialRate (squaredRadiusEvolution t s) * radialAmplitude t s) t := by
  have he : HasDerivAt (fun τ : ℝ => Real.exp (-4 * τ))
      (Real.exp (-4 * t) * (-4)) t := by
    simpa using ((hasDerivAt_id t).const_mul (-4 : ℝ)).exp
  have hg := hasDerivAt_planarAmplitude ht hs
  have hr := hasDerivAt_sqrt_radialDiscriminant ht s
  have hp := planarAmplitude_pos ht hs
  have hR := sqrt_radialDiscriminant_pos ht s
  have hden := hg.mul (hr.pow 3)
  apply (he.div hden (ne_of_gt (mul_pos hp (pow_pos hR 3)))).congr_deriv
  dsimp [radialAmplitude, radialRate, q]
  field_simp [ne_of_gt hp, ne_of_gt hR]
  ring

@[simp] theorem radialAmplitude_zero_time (s : ℝ) : radialAmplitude 0 s = 1 := by
  simp [radialAmplitude]

theorem hasDerivAt_log_planarAmplitude {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    HasDerivAt (fun τ => Real.log (planarAmplitude τ s))
      (tangentialRate (squaredRadiusEvolution t s)) t := by
  have hp := planarAmplitude_pos ht hs
  apply ((hasDerivAt_planarAmplitude ht hs).log (ne_of_gt hp)).congr_deriv
  simp [tangentialRate_eq_q, ne_of_gt hp]

theorem hasDerivAt_log_radialAmplitude {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    HasDerivAt (fun τ => Real.log (radialAmplitude τ s))
      (radialRate (squaredRadiusEvolution t s)) t := by
  have hp := radialAmplitude_pos ht hs
  apply ((hasDerivAt_radialAmplitude ht hs).log (ne_of_gt hp)).congr_deriv
  simp [ne_of_gt hp]

theorem continuousOn_squaredRadiusEvolution_time (s : ℝ) :
    ContinuousOn (fun t => squaredRadiusEvolution t s) (Ici 0) :=
  fun _ ht => (hasDerivAt_squaredRadiusEvolution ht s).continuousAt.continuousWithinAt

theorem log_planarAmplitude_eq_integral {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    Real.log (planarAmplitude t s) =
      ∫ τ in (0 : ℝ)..t, tangentialRate (squaredRadiusEvolution τ s) := by
  have hb : Continuous tangentialRate := by unfold tangentialRate; fun_prop
  have hcont := hb.comp_continuousOn
    ((continuousOn_squaredRadiusEvolution_time s).mono
      (show Icc 0 t ⊆ Ici 0 from fun _ h => h.1))
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := 0) (b := t)
    (fun τ hτ => hasDerivAt_log_planarAmplitude ((uIcc_of_le ht ▸ hτ).1) hs)
    (hcont.intervalIntegrable_of_Icc ht)
  simpa using hFTC.symm

theorem log_radialAmplitude_eq_integral {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    Real.log (radialAmplitude t s) =
      ∫ τ in (0 : ℝ)..t, radialRate (squaredRadiusEvolution τ s) := by
  have ha : Continuous radialRate := by unfold radialRate; fun_prop
  have hcont := ha.comp_continuousOn
    ((continuousOn_squaredRadiusEvolution_time s).mono
      (show Icc 0 t ⊆ Ici 0 from fun _ h => h.1))
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := 0) (b := t)
    (fun τ hτ => hasDerivAt_log_radialAmplitude ((uIcc_of_le ht ▸ hτ).1) hs)
    (hcont.intervalIntegrable_of_Icc ht)
  simpa using hFTC.symm

/-- The tangential factor is the exponential integral of the tangential rate. -/
theorem planarAmplitude_eq_exp_integral {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    planarAmplitude t s =
      Real.exp (∫ τ in (0 : ℝ)..t, tangentialRate (squaredRadiusEvolution τ s)) := by
  rw [← log_planarAmplitude_eq_integral ht hs, Real.exp_log (planarAmplitude_pos ht hs)]

/-- The radial factor is the exponential integral of the radial rate. -/
theorem radialAmplitude_eq_exp_integral {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    radialAmplitude t s =
      Real.exp (∫ τ in (0 : ℝ)..t, radialRate (squaredRadiusEvolution τ s)) := by
  rw [← log_radialAmplitude_eq_integral ht hs, Real.exp_log (radialAmplitude_pos ht hs)]

end Eden
