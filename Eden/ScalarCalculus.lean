import Eden.ScalarFlow
import Mathlib.Tactic.FunProp

/-!
# Derivatives of the radial solution and planar amplitude

The scalar formulas are differentiated both in time and in their initial
parameter. Positivity removes the apparent singularity at initial radius zero.
These facts supply the analytic ingredients for constructing the planar
evolution in Colbrook's example.

The proofs use Mathlib's derivative calculus for quotients and square roots
(Sébastien Gouëzel, Yury Kudryashov and other Mathlib contributors), together
with its locality principle `HasDerivAt.congr_of_eventuallyEq`.
-/

noncomputable section
open scoped Topology
open Filter

namespace Eden

/-- The positive scale factor in the planar evolution for `t ≥ 0`, `s ≥ 0`. -/
def planarAmplitude (t s : ℝ) : ℝ := Real.sqrt (amplitudeSq t s)

theorem hasDerivAt_squaredRadiusEvolution_parameter {t : ℝ} (ht : 0 ≤ t) (s : ℝ) :
    HasDerivAt (squaredRadiusEvolution t)
      (Real.exp (-4 * t) / Real.sqrt (radialDiscriminant t s) ^ 3) s := by
  have hu := (hasDerivAt_id s).sub_const 1
  have hd := ((hu.pow 2).const_mul (1 - Real.exp (-4 * t))).const_add
    (Real.exp (-4 * t))
  have hr := hd.sqrt (ne_of_gt (radialDiscriminant_pos ht s))
  have hR := sqrt_radialDiscriminant_pos ht s
  have hq := hu.div hr (ne_of_gt hR)
  have hsq := Real.sq_sqrt (le_of_lt (radialDiscriminant_pos ht s))
  apply (hq.const_add 1).congr_deriv
  dsimp [radialDiscriminant] at hR hsq ⊢
  simp only [neg_mul] at hR hsq ⊢
  field_simp [ne_of_gt hR]
  nlinarith

theorem continuous_radialDiscriminant_time (s : ℝ) :
    Continuous (fun t => radialDiscriminant t s) := by
  unfold radialDiscriminant
  fun_prop

/-- The time derivative of the squared amplitude, including initial radius zero. -/
theorem hasDerivAt_amplitudeSq_of_discriminant_pos {t s : ℝ}
    (hD : 0 < radialDiscriminant t s) :
    HasDerivAt (fun τ => amplitudeSq τ s)
      (2 * q (squaredRadiusEvolution t s) * amplitudeSq t s) t := by
  by_cases hs : s = 0
  · subst s
    have he : HasDerivAt (fun τ : ℝ => Real.exp (-4 * τ))
        (Real.exp (-4 * t) * (-4)) t := by
      simpa using ((hasDerivAt_id t).const_mul (-4 : ℝ)).exp
    norm_num [q, mul_comm] at he ⊢
    exact he
  have hpos : ∀ᶠ τ in 𝓝 t, 0 < radialDiscriminant τ s :=
    (continuous_radialDiscriminant_time s).continuousAt.eventually
      (Ioi_mem_nhds hD)
  have heq : (fun τ => amplitudeSq τ s) =ᶠ[𝓝 t]
      (fun τ => squaredRadiusEvolution τ s / s) := by
    filter_upwards [hpos] with τ hτ
    apply (eq_div_iff hs).2
    simpa only [mul_comm] using mul_amplitudeSq_of_discriminant_pos hτ
  have hder := ((hasDerivAt_squaredRadiusEvolution_of_discriminant_pos hD).div_const s).congr_of_eventuallyEq heq
  apply hder.congr_deriv
  rw [← mul_amplitudeSq_of_discriminant_pos hD]
  unfold q
  field_simp

theorem hasDerivAt_amplitudeSq {t : ℝ} (ht : 0 ≤ t) (s : ℝ) :
    HasDerivAt (fun τ => amplitudeSq τ s)
      (2 * q (squaredRadiusEvolution t s) * amplitudeSq t s) t :=
  hasDerivAt_amplitudeSq_of_discriminant_pos (radialDiscriminant_pos ht s)

theorem planarAmplitude_pos {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    0 < planarAmplitude t s :=
  Real.sqrt_pos.2 (amplitudeSq_pos ht hs)

theorem planarAmplitude_sq {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    planarAmplitude t s ^ 2 = amplitudeSq t s :=
  Real.sq_sqrt (le_of_lt (amplitudeSq_pos ht hs))

@[simp] theorem planarAmplitude_zero_time (s : ℝ) : planarAmplitude 0 s = 1 := by
  simp [planarAmplitude]

/-- The planar amplitude has exactly the tangential logarithmic growth rate. -/
theorem hasDerivAt_planarAmplitude_of_pos {t s : ℝ}
    (hD : 0 < radialDiscriminant t s) (hB : 0 < amplitudeSq t s) :
    HasDerivAt (fun τ => planarAmplitude τ s)
      (q (squaredRadiusEvolution t s) * planarAmplitude t s) t := by
  have hg : 0 < planarAmplitude t s := Real.sqrt_pos.2 hB
  have hsq : planarAmplitude t s ^ 2 = amplitudeSq t s := Real.sq_sqrt hB.le
  apply ((hasDerivAt_amplitudeSq_of_discriminant_pos hD).sqrt (ne_of_gt hB)).congr_deriv
  dsimp [planarAmplitude] at hg hsq ⊢
  field_simp [ne_of_gt hg]
  nlinarith [congrArg (fun x : ℝ => q (squaredRadiusEvolution t s) * x) hsq]

theorem hasDerivAt_planarAmplitude {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    HasDerivAt (fun τ => planarAmplitude τ s)
      (q (squaredRadiusEvolution t s) * planarAmplitude t s) t :=
  hasDerivAt_planarAmplitude_of_pos (radialDiscriminant_pos ht s) (amplitudeSq_pos ht hs)

end Eden
