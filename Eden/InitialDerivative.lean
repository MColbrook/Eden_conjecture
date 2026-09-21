import Eden.Evolution

/-!
# Smooth dependence on the initial point

The positive denominators in the explicit solution give smooth dependence
on every ambient initial point, including the origin of either planar block.
The radial scale is derived from the scalar derivative and subsequently
identified as a singular value by the orthogonal decomposition.
-/

noncomputable section
namespace Eden

theorem contDiff_amplitudeSq {t : ℝ} (ht : 0 ≤ t) (n : WithTop ℕ∞) :
    ContDiff ℝ n (amplitudeSq t) := by
  have hd : ContDiff ℝ n (radialDiscriminant t) := by
    unfold radialDiscriminant
    fun_prop
  have hr := hd.sqrt (fun s => ne_of_gt (radialDiscriminant_pos ht s))
  have hR : ∀ s, Real.sqrt (radialDiscriminant t s) ≠ 0 :=
    fun s => ne_of_gt (sqrt_radialDiscriminant_pos ht s)
  have hR1 : ∀ s, Real.sqrt (radialDiscriminant t s) + 1 ≠ 0 :=
    fun s => ne_of_gt (by positivity)
  unfold amplitudeSq
  exact (contDiff_const.add
    (((contDiff_id.sub contDiff_const).mul contDiff_const).div
      (hr.add contDiff_const) hR1)).div hr hR

theorem contDiffAt_planarAmplitude {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s)
    (n : WithTop ℕ∞) : ContDiffAt ℝ n (planarAmplitude t) s :=
  (contDiff_amplitudeSq ht n).contDiffAt.sqrt (ne_of_gt (amplitudeSq_pos ht hs))

/-- Scale in the direction of the initial radius, positive for `t ≥ 0`, `s ≥ 0`.
Its connection to the initial-radius derivative is proved below. -/
def radialAmplitude (t s : ℝ) : ℝ :=
  Real.exp (-4 * t) /
    (planarAmplitude t s * Real.sqrt (radialDiscriminant t s) ^ 3)

theorem radialAmplitude_pos {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    0 < radialAmplitude t s := by
  exact div_pos (Real.exp_pos _)
    (mul_pos (planarAmplitude_pos ht hs)
      (pow_pos (sqrt_radialDiscriminant_pos ht s) 3))

/-- Differentiating `s B(t,s) = S(t,s)` gives the radial derivative identity
without division by the initial radius, so it remains valid at `s=0`. -/
theorem amplitudeSq_parameter_identity {t : ℝ} (ht : 0 ≤ t) (s : ℝ) :
    amplitudeSq t s + s * deriv (amplitudeSq t) s =
      Real.exp (-4 * t) / Real.sqrt (radialDiscriminant t s) ^ 3 := by
  have hB := ((contDiff_amplitudeSq ht 1).differentiable one_ne_zero s).hasDerivAt
  have hp := (hasDerivAt_id s).mul hB
  change HasDerivAt (fun r => r * amplitudeSq t r)
    (1 * amplitudeSq t s + s * deriv (amplitudeSq t) s) s at hp
  have hS : HasDerivAt (squaredRadiusEvolution t)
      (amplitudeSq t s + s * deriv (amplitudeSq t) s) s := by
    simpa only [mul_amplitudeSq ht, one_mul] using hp
  exact hS.unique (hasDerivAt_squaredRadiusEvolution_parameter ht s)

/-- The radial derivative of `r ↦ r g(t,r²)` expressed through the derivative
of the amplitude with respect to squared radius. The identity includes zero. -/
theorem planarAmplitude_parameter_identity {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    planarAmplitude t s + 2 * s * deriv (planarAmplitude t) s =
      radialAmplitude t s := by
  have hB := ((contDiff_amplitudeSq ht 1).differentiable one_ne_zero s).hasDerivAt
  have hg := hB.sqrt (ne_of_gt (amplitudeSq_pos ht hs))
  have hd : deriv (planarAmplitude t) s =
      deriv (amplitudeSq t) s / (2 * planarAmplitude t s) := hg.deriv
  have hp := planarAmplitude_pos ht hs
  have hR := sqrt_radialDiscriminant_pos ht s
  have hsq := planarAmplitude_sq ht hs
  have hrel := amplitudeSq_parameter_identity ht s
  rw [hd]
  unfold radialAmplitude
  field_simp [ne_of_gt hp, ne_of_gt hR] at hrel ⊢
  nlinarith [congrArg (fun x : ℝ => x * Real.sqrt (radialDiscriminant t s) ^ 3) hsq]

/-- Smooth dependence on all five ambient coordinates, in the Euclidean norm. -/
theorem contDiff_evolution (c : ℝ) {t : ℝ} (ht : 0 ≤ t) (n : WithTop ℕ∞) :
    ContDiff ℝ n (evolution c t) := by
  have h₁ : ContDiff ℝ n (fun p : PhaseSpace =>
      planarAmplitude t (p 0 ^ 2 + p 1 ^ 2)) := by
    apply contDiff_iff_contDiffAt.2
    intro p
    have hr : ContDiffAt ℝ n (fun p : PhaseSpace => p 0 ^ 2 + p 1 ^ 2) p := by
      fun_prop
    have h := (contDiffAt_planarAmplitude ht
      (add_nonneg (sq_nonneg (p 0)) (sq_nonneg (p 1))) n).comp p hr
    exact h
  have h₂ : ContDiff ℝ n (fun p : PhaseSpace =>
      planarAmplitude t (p 2 ^ 2 + p 3 ^ 2)) := by
    apply contDiff_iff_contDiffAt.2
    intro p
    have hr : ContDiffAt ℝ n (fun p : PhaseSpace => p 2 ^ 2 + p 3 ^ 2) p := by
      fun_prop
    have h := (contDiffAt_planarAmplitude ht
      (add_nonneg (sq_nonneg (p 2)) (sq_nonneg (p 3))) n).comp p hr
    exact h
  rw [contDiff_piLp]
  intro i
  fin_cases i <;> simp [evolution, planarX, planarY] <;> fun_prop

end Eden
