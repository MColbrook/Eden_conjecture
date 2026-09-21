import Eden.PeriodicSets
import Eden.DimensionTable
import Eden.FiniteTimeKaplanYorke

/-!
# Exact dimensions at equilibria and periodic points

At stationary radii the normalized logarithms of the derivative factors are
independent of positive time. Sorting their complete multiset therefore gives
the limiting spectrum at every such time. The finite-time dimension and its
limiting Kaplan--Yorke value consequently agree throughout the
periodic/equilibrium set.
-/

noncomputable section
open Set
namespace Eden

theorem log_planarAmplitude_div_of_stationary {t s : ℝ} (ht : 0 < t)
    (hs : s = 0 ∨ s = 1 ∨ s = 2) :
    Real.log (planarAmplitude t s) / t = tangentialRate s := by
  rcases hs with rfl | rfl | rfl
  · rw [planarAmplitude_at_zero ht.le, Real.log_exp]
    dsimp [tangentialRate]
    field_simp
    ring
  · rw [planarAmplitude_at_one ht.le]
    norm_num [tangentialRate]
  · rw [planarAmplitude_at_two ht.le]
    norm_num [tangentialRate]

theorem log_radialAmplitude_div_of_stationary {t s : ℝ} (ht : 0 < t)
    (hs : s = 0 ∨ s = 1 ∨ s = 2) :
    Real.log (radialAmplitude t s) / t = radialRate s := by
  rcases hs with rfl | rfl | rfl
  · rw [radialAmplitude_at_zero ht.le, Real.log_exp]
    dsimp [radialRate]
    field_simp
    ring
  · rw [radialAmplitude_at_one ht.le, Real.log_exp]
    norm_num [radialRate]
    field_simp
  · rw [radialAmplitude_at_two ht.le, Real.log_exp]
    norm_num [radialRate]
    field_simp

theorem limitingSquaredRadius_of_stationary {s : ℝ} (hs : s = 0 ∨ s = 1 ∨ s = 2) :
    limitingSquaredRadius s = s := by
  rcases hs with rfl | rfl | rfl <;> norm_num [limitingSquaredRadius]

theorem normalizedLogSingularValues_of_stationary_radii (c : ℝ) {t : ℝ}
    (ht : 0 < t) (p : PhaseSpace)
    (h₁ : radiusSq₁ p = 0 ∨ radiusSq₁ p = 1 ∨ radiusSq₁ p = 2)
    (h₂ : radiusSq₂ p = 0 ∨ radiusSq₂ p = 1 ∨ radiusSq₂ p = 2) :
    normalizedLogSingularValues c t p =
      descending (radiusPairSpectrum c (radiusSq₁ p) (radiusSq₂ p)) := by
  rw [normalizedLogSingularValues_eq_descending c ht p]
  congr 1
  funext i
  fin_cases i
  · exact log_radialAmplitude_div_of_stationary ht h₁
  · exact log_planarAmplitude_div_of_stationary ht h₁
  · exact log_radialAmplitude_div_of_stationary ht h₂
  · exact log_planarAmplitude_div_of_stationary ht h₂
  · change Real.log (Real.exp (-c * t)) / t = -c
    rw [Real.log_exp]
    field_simp

theorem normalizedLogSingularValues_eq_lyapunovExponent_of_stationary (c : ℝ)
    {t : ℝ} (ht : 0 < t) (p : PhaseSpace)
    (h₁ : radiusSq₁ p = 0 ∨ radiusSq₁ p = 1 ∨ radiusSq₁ p = 2)
    (h₂ : radiusSq₂ p = 0 ∨ radiusSq₂ p = 1 ∨ radiusSq₂ p = 2) :
    normalizedLogSingularValues c t p = lyapunovExponent c p := by
  rw [normalizedLogSingularValues_of_stationary_radii c ht p h₁ h₂,
    lyapunovExponent_eq_radiusPairSpectrum, limitingSquaredRadius_of_stationary h₁,
    limitingSquaredRadius_of_stationary h₂]

/-- Both dimensions agree at every positive time throughout the periodic/equilibrium
set, using the ordered singular-value exponents. -/
theorem finiteTimeDimension_eq_asymptotic_on_periodic {c t : ℝ} (hc : 0 < c)
    (ht : 0 < t) {p : PhaseSpace} (hp : p ∈ periodicEquilibriumSet c) :
    finiteTimeDimension c t p = asymptoticDimension c p := by
  rw [periodicEquilibriumSet_eq_positiveReturnSet hc] at hp
  obtain ⟨u, hu, hret⟩ := hp
  have hs := stationary_radii_of_evolution_return c hu hret
  rw [finiteTimeDimension_eq_kaplanYorke c ht p,
    normalizedLogSingularValues_eq_lyapunovExponent_of_stationary c ht p hs.1 hs.2]
  rfl

theorem asymptoticDimension_at_origin {c : ℝ} (hc : 4 < c) :
    asymptoticDimension c 0 = 0 := by
  rw [asymptoticDimension, lyapunovExponent_eq_radiusPairSpectrum]
  norm_num [radiusSq₁, radiusSq₂, limitingSquaredRadius]
  rw [descending_radiusPairSpectrum_zero_zero hc, kaplanYorkeDimension_zero_zero hc]

theorem asymptoticDimension_first_unit_circle {c : ℝ} (hc : 4 < c)
    {p : PhaseSpace} (hp : p ∈ firstCircle 1) : asymptoticDimension c p = 3 := by
  rw [asymptoticDimension, lyapunovExponent_eq_radiusPairSpectrum, hp.1, hp.2.1]
  norm_num [limitingSquaredRadius]
  rw [descending_radiusPairSpectrum_swap c 1 0, descending_radiusPairSpectrum_zero_one hc,
    kaplanYorkeDimension_zero_one hc]

theorem asymptoticDimension_second_unit_circle {c : ℝ} (hc : 4 < c)
    {p : PhaseSpace} (hp : p ∈ secondCircle 1) : asymptoticDimension c p = 3 := by
  rw [asymptoticDimension, lyapunovExponent_eq_radiusPairSpectrum, hp.1, hp.2.1]
  norm_num [limitingSquaredRadius]
  rw [descending_radiusPairSpectrum_zero_one hc, kaplanYorkeDimension_zero_one hc]

theorem asymptoticDimension_first_outer_circle {c : ℝ} (hc : 4 < c)
    {p : PhaseSpace} (hp : p ∈ firstCircle 2) : asymptoticDimension c p = 1 := by
  rw [asymptoticDimension, lyapunovExponent_eq_radiusPairSpectrum, hp.1, hp.2.1]
  norm_num [limitingSquaredRadius]
  rw [descending_radiusPairSpectrum_swap c 2 0, descending_radiusPairSpectrum_zero_two hc,
    kaplanYorkeDimension_zero_two hc]

theorem asymptoticDimension_second_outer_circle {c : ℝ} (hc : 4 < c)
    {p : PhaseSpace} (hp : p ∈ secondCircle 2) : asymptoticDimension c p = 1 := by
  rw [asymptoticDimension, lyapunovExponent_eq_radiusPairSpectrum, hp.1, hp.2.1]
  norm_num [limitingSquaredRadius]
  rw [descending_radiusPairSpectrum_zero_two hc, kaplanYorkeDimension_zero_two hc]

/-- The ordered normalized finite-time rates on either unit periodic circle. -/
theorem normalizedLogSingularValues_unit_circle {c t : ℝ} (hc : 4 < c)
    (ht : 0 < t) {p : PhaseSpace} (hp : p ∈ firstCircle 1 ∨ p ∈ secondCircle 1) :
    normalizedLogSingularValues c t p = ![2, 0, -2, -2, -c] := by
  rcases hp with hp | hp
  · rw [normalizedLogSingularValues_of_stationary_radii c ht p
      (Or.inr (Or.inl hp.1)) (Or.inl hp.2.1), hp.1, hp.2.1,
      descending_radiusPairSpectrum_swap c 1 0, descending_radiusPairSpectrum_zero_one hc]
  · rw [normalizedLogSingularValues_of_stationary_radii c ht p
      (Or.inl hp.1) (Or.inr (Or.inl hp.2.1)), hp.1, hp.2.1,
      descending_radiusPairSpectrum_zero_one hc]

/-- The ordered normalized finite-time rates on either outer periodic circle. -/
theorem normalizedLogSingularValues_outer_circle {c t : ℝ} (hc : 4 < c)
    (ht : 0 < t) {p : PhaseSpace} (hp : p ∈ firstCircle 2 ∨ p ∈ secondCircle 2) :
    normalizedLogSingularValues c t p = ![0, -2, -2, -4, -c] := by
  rcases hp with hp | hp
  · rw [normalizedLogSingularValues_of_stationary_radii c ht p
      (Or.inr (Or.inr hp.1)) (Or.inl hp.2.1), hp.1, hp.2.1,
      descending_radiusPairSpectrum_swap c 2 0, descending_radiusPairSpectrum_zero_two hc]
  · rw [normalizedLogSingularValues_of_stationary_radii c ht p
      (Or.inl hp.1) (Or.inr (Or.inr hp.2.1)), hp.1, hp.2.1,
      descending_radiusPairSpectrum_zero_two hc]

theorem finiteTimeDimension_at_origin {c t : ℝ} (hc : 4 < c) (ht : 0 < t) :
    finiteTimeDimension c t 0 = 0 := by
  have hp : (0 : PhaseSpace) ∈ periodicEquilibriumSet c := by
    rw [periodicEquilibriumSet_eq_positiveReturnSet (show 0 < c by linarith)]
    exact ⟨1, by norm_num, evolution_origin c 1⟩
  rw [finiteTimeDimension_eq_asymptotic_on_periodic (by linarith) ht hp,
    asymptoticDimension_at_origin hc]

theorem asymptoticDimension_periodic_le_three {c : ℝ} (hc : 4 < c)
    {p : PhaseSpace} (hp : p ∈ periodicEquilibriumSet c) : asymptoticDimension c p ≤ 3 := by
  rw [periodicEquilibriumSet_eq_positiveReturnSet (show 0 < c by linarith)] at hp
  rcases (mem_positiveReturnSet_iff (by linarith) p).mp hp with rfl | h | h | h | h
  · rw [asymptoticDimension_at_origin hc]; norm_num
  · exact (asymptoticDimension_first_unit_circle hc h).le
  · rw [asymptoticDimension_first_outer_circle hc h]; norm_num
  · exact (asymptoticDimension_second_unit_circle hc h).le
  · rw [asymptoticDimension_second_outer_circle hc h]; norm_num

end Eden
