import Eden.PhysicalRadius
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# Lifted angles along nonzero planar trajectories

An initial argument determines the real lift theta(t)=theta(0)+Omega*t.
The formulas use an arbitrary initial angle and do not differentiate the
principal argument across its cut. Existence of an initial angle follows
from Mathlib's complex argument identities.
-/

noncomputable section
namespace Eden

theorem radiusEvolution_eq_amplitude {t r : ℝ} (ht : 0 ≤ t) (hr : 0 ≤ r) :
    radiusEvolution t r = r * planarAmplitude t (r ^ 2) := by
  have h₁ := radiusEvolution_sq ht r
  have h₂ := planarAmplitude_sq ht (sq_nonneg r)
  have h₃ := mul_amplitudeSq ht (r ^ 2)
  have hn := radiusEvolution_nonneg t r
  have hg := planarAmplitude_pos ht (sq_nonneg r)
  have hp := mul_nonneg hr hg.le
  nlinarith [sq_nonneg (radiusEvolution t r + r * planarAmplitude t (r ^ 2)),
    congrArg (fun a : ℝ => r ^ 2 * a) h₂]

theorem planar_evolution_polar (Ω θ : ℝ) {t r : ℝ} (ht : 0 ≤ t) (hr : 0 ≤ r) :
    planarX Ω t (r * Real.cos θ) (r * Real.sin θ) =
        radiusEvolution t r * Real.cos (θ + Ω * t) ∧
      planarY Ω t (r * Real.cos θ) (r * Real.sin θ) =
        radiusEvolution t r * Real.sin (θ + Ω * t) := by
  have hs : (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 = r ^ 2 := by
    nlinarith [congrArg (fun a : ℝ => r ^ 2 * a) (Real.sin_sq_add_cos_sq θ)]
  rw [radiusEvolution_eq_amplitude ht hr]
  simp only [planarX, planarY, hs, Real.cos_add, Real.sin_add]
  constructor <;> ring

theorem exists_initial_polar_angle (x y : ℝ) :
    ∃ θ : ℝ, x = Real.sqrt (x ^ 2 + y ^ 2) * Real.cos θ ∧
      y = Real.sqrt (x ^ 2 + y ^ 2) * Real.sin θ := by
  let z : ℂ := ⟨x, y⟩
  refine ⟨Complex.arg z, ?_, ?_⟩
  · simpa [z, Complex.norm_def, Complex.normSq_apply, pow_two] using
      (Complex.norm_mul_cos_arg z).symm
  · simpa [z, Complex.norm_def, Complex.normSq_apply, pow_two] using
      (Complex.norm_mul_sin_arg z).symm

/-- Every nonzero initial planar point has a real angular lift with constant
derivative Omega and a strictly positive radius at each finite forward time. -/
theorem exists_planar_angular_lift (Ω x y : ℝ) (hxy : x ^ 2 + y ^ 2 ≠ 0) :
    ∃ θ : ℝ,
      (∀ t : ℝ, HasDerivAt (fun τ => θ + Ω * τ) Ω t) ∧
      ∀ t : ℝ, 0 ≤ t →
        0 < radiusEvolution t (Real.sqrt (x ^ 2 + y ^ 2)) ∧
        planarX Ω t x y = radiusEvolution t (Real.sqrt (x ^ 2 + y ^ 2)) *
          Real.cos (θ + Ω * t) ∧
        planarY Ω t x y = radiusEvolution t (Real.sqrt (x ^ 2 + y ^ 2)) *
          Real.sin (θ + Ω * t) := by
  obtain ⟨θ, hx, hy⟩ := exists_initial_polar_angle x y
  refine ⟨θ, ?_, ?_⟩
  · intro t
    have h := (hasDerivAt_const t θ).add ((hasDerivAt_id t).const_mul Ω)
    change HasDerivAt (fun τ => θ + Ω * τ) (0 + Ω * 1) t at h
    simpa only [mul_one, zero_add] using h
  · intro t ht
    refine ⟨radiusEvolution_pos ht (Real.sqrt_pos.2
      (lt_of_le_of_ne (add_nonneg (sq_nonneg x) (sq_nonneg y)) (Ne.symm hxy))), ?_⟩
    have hp := planar_evolution_polar Ω θ ht (Real.sqrt_nonneg (x ^ 2 + y ^ 2))
    rw [← hx, ← hy] at hp
    exact hp

end Eden
