import Eden.RadialReturns
import Mathlib.NumberTheory.Real.Irrational

/-!
# Irrational frequencies exclude simultaneous planar returns

The argument uses the Cartesian solution, including its radial amplitude.
Mathlib's `Real.cos_eq_one_iff` supplies integer multiples of `2*pi`, and
`irrational_sqrt_two` excludes their simultaneous occurrence. The irrationality
library is due to Mario Carneiro, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne
and Yury Kudryashov.
-/

noncomputable section
namespace Eden

theorem rotation_fixed_iff {x y θ : ℝ} (hs : x ^ 2 + y ^ 2 ≠ 0) :
    (x * Real.cos θ - y * Real.sin θ = x ∧
      x * Real.sin θ + y * Real.cos θ = y) ↔
      Real.cos θ = 1 ∧ Real.sin θ = 0 := by
  constructor
  · rintro ⟨hx, hy⟩
    have hprod : (x ^ 2 + y ^ 2) * (Real.cos θ - 1) = 0 := by
      nlinarith [congrArg (fun a : ℝ => x * a) hx,
        congrArg (fun a : ℝ => y * a) hy]
    have hcos : Real.cos θ = 1 := by
      have := (mul_eq_zero.mp hprod).resolve_left hs
      linarith
    refine ⟨hcos, ?_⟩
    have hid := Real.sin_sq_add_cos_sq θ
    rw [hcos] at hid
    nlinarith [sq_nonneg (Real.sin θ)]
  · rintro ⟨hc, hs⟩
    simp [hc, hs]

theorem planar_return_cos_sin (Ω : ℝ) {t x y : ℝ} (ht : 0 < t)
    (hs : x ^ 2 + y ^ 2 ≠ 0)
    (hx : planarX Ω t x y = x) (hy : planarY Ω t x y = y) :
    Real.cos (Ω * t) = 1 ∧ Real.sin (Ω * t) = 0 := by
  have hr : squaredRadiusEvolution t (x ^ 2 + y ^ 2) = x ^ 2 + y ^ 2 := by
    rw [← planar_radius_sq Ω ht.le, hx, hy]
  have hstationary := (squaredRadiusEvolution_eq_self_iff ht).mp hr
  have hg : planarAmplitude t (x ^ 2 + y ^ 2) = 1 := by
    rcases hstationary with h₀ | h₁ | h₂
    · exact False.elim (hs h₀)
    · rw [h₁, planarAmplitude_at_one ht.le]
    · rw [h₂, planarAmplitude_at_two ht.le]
  apply (rotation_fixed_iff hs).mp
  constructor
  · simpa only [planarX, hg, one_mul] using hx
  · simpa only [planarY, hg, one_mul] using hy

theorem not_simultaneous_rotation_returns {t : ℝ} (ht : 0 < t) :
    ¬(Real.cos t = 1 ∧ Real.cos (Real.sqrt 2 * t) = 1) := by
  rintro ⟨h₁, h₂⟩
  obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff t).mp h₁
  obtain ⟨m, hm⟩ := (Real.cos_eq_one_iff (Real.sqrt 2 * t)).mp h₂
  have hn₀ : (n : ℝ) ≠ 0 := by
    intro hzero
    rw [hzero, zero_mul] at hn
    linarith
  have hpi : (2 : ℝ) * Real.pi ≠ 0 := ne_of_gt (by positivity)
  have hmul : Real.sqrt 2 * (n : ℝ) = (m : ℝ) := by
    apply mul_right_cancel₀ hpi
    calc
      _ = Real.sqrt 2 * ((n : ℝ) * (2 * Real.pi)) := by ring
      _ = _ := by rw [hn]; exact hm.symm
  exact irrational_sqrt_two.ne_rational m n ((eq_div_iff hn₀).mpr hmul)

theorem first_cos_eq_one_of_evolution_return (c : ℝ) {t : ℝ} (ht : 0 < t)
    {p : PhaseSpace} (hs : radiusSq₁ p ≠ 0) (h : evolution c t p = p) :
    Real.cos t = 1 := by
  have hx : planarX 1 t (p 0) (p 1) = p 0 := by
    simpa [evolution] using congrArg (fun q : PhaseSpace => q 0) h
  have hy : planarY 1 t (p 0) (p 1) = p 1 := by
    simpa [evolution] using congrArg (fun q : PhaseSpace => q 1) h
  simpa only [one_mul] using (planar_return_cos_sin 1 ht hs hx hy).1

theorem second_cos_eq_one_of_evolution_return (c : ℝ) {t : ℝ} (ht : 0 < t)
    {p : PhaseSpace} (hs : radiusSq₂ p ≠ 0) (h : evolution c t p = p) :
    Real.cos (Real.sqrt 2 * t) = 1 := by
  have hx : planarX (Real.sqrt 2) t (p 2) (p 3) = p 2 := by
    simpa [evolution] using congrArg (fun q : PhaseSpace => q 2) h
  have hy : planarY (Real.sqrt 2) t (p 2) (p 3) = p 3 := by
    simpa [evolution] using congrArg (fun q : PhaseSpace => q 3) h
  exact (planar_return_cos_sin (Real.sqrt 2) ht hs hx hy).1

/-- Every positive-time return has at least one zero planar coordinate. -/
theorem one_radius_zero_of_evolution_return (c : ℝ) {t : ℝ} (ht : 0 < t)
    {p : PhaseSpace} (h : evolution c t p = p) : radiusSq₁ p = 0 ∨ radiusSq₂ p = 0 := by
  by_cases h₁ : radiusSq₁ p = 0
  · exact Or.inl h₁
  by_cases h₂ : radiusSq₂ p = 0
  · exact Or.inr h₂
  exact False.elim (not_simultaneous_rotation_returns ht
    ⟨first_cos_eq_one_of_evolution_return c ht h₁ h,
      second_cos_eq_one_of_evolution_return c ht h₂ h⟩)

/-- No point on the torus has a positive real return time. -/
theorem torus_no_positive_return (c : ℝ) {p : PhaseSpace} (hp : p ∈ torus)
    {t : ℝ} (ht : 0 < t) : evolution c t p ≠ p := by
  intro h
  rcases one_radius_zero_of_evolution_return c ht h with h₁ | h₂
  · linarith [hp.1]
  · linarith [hp.2.1]

end Eden
