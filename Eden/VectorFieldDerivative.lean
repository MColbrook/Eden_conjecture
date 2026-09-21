import Eden.CartesianDerivative
import Mathlib.LinearAlgebra.Trace

/-!
# The derivative of the polynomial vector field

The scalar derivative, chain rule and product rule give each coordinate of the
Fréchet derivative, on the whole ambient Euclidean space. Its trace is
calculated in `Eden.Divergence`.
-/

noncomputable section
namespace Eden

theorem hasDerivAt_q (s : ℝ) : HasDerivAt q (-2 * s + 3) s := by
  have h := (((hasDerivAt_id s).sub_const 1).neg).mul ((hasDerivAt_id s).sub_const 2)
  change HasDerivAt q _ s at h
  apply h.congr_deriv
  dsimp
  ring

theorem deriv_q (s : ℝ) : deriv q s = -2 * s + 3 := (hasDerivAt_q s).deriv

theorem radialRate_eq_q_add_deriv (s : ℝ) : radialRate s = q s + 2 * s * deriv q s := by
  rw [deriv_q]
  exact radialRate_eq_q_add s

section Composition
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f g : E → ℝ} {f' g' : E →L[ℝ] ℝ} {p : E}

theorem fderiv_planarVectorX_apply (Ω : ℝ)
    (hf : HasFDerivAt f f' p) (hg : HasFDerivAt g g' p) (v : E) :
    fderiv ℝ (fun u => q (f u ^ 2 + g u ^ 2) * f u - Ω * g u) p v =
      q (f p ^ 2 + g p ^ 2) * f' v +
        2 * deriv q (f p ^ 2 + g p ^ 2) * (f p * f' v + g p * g' v) * f p - Ω * g' v := by
  have hr := (hf.pow 2).add (hg.pow 2)
  have hq := (hasDerivAt_q (f p ^ 2 + g p ^ 2)).comp_hasFDerivAt p hr
  have h := (hq.mul hf).sub (hg.const_mul Ω)
  change HasFDerivAt (fun u => q (f u ^ 2 + g u ^ 2) * f u - Ω * g u) _ p at h
  rw [h.fderiv, deriv_q]
  simp [smul_eq_mul]
  ring

theorem fderiv_planarVectorY_apply (Ω : ℝ)
    (hf : HasFDerivAt f f' p) (hg : HasFDerivAt g g' p) (v : E) :
    fderiv ℝ (fun u => q (f u ^ 2 + g u ^ 2) * g u + Ω * f u) p v =
      q (f p ^ 2 + g p ^ 2) * g' v +
        2 * deriv q (f p ^ 2 + g p ^ 2) * (f p * f' v + g p * g' v) * g p + Ω * f' v := by
  have hr := (hf.pow 2).add (hg.pow 2)
  have hq := (hasDerivAt_q (f p ^ 2 + g p ^ 2)).comp_hasFDerivAt p hr
  have h := (hq.mul hg).add (hf.const_mul Ω)
  change HasFDerivAt (fun u => q (f u ^ 2 + g u ^ 2) * g u + Ω * f u) _ p at h
  rw [h.fderiv, deriv_q]
  simp [smul_eq_mul]
  ring

end Composition

/-- The full ambient Jacobian applied to a direction, with no radius or parameter
restriction. All components are those of the derivative. -/
theorem fderiv_vectorField_apply (c : ℝ) (p v : PhaseSpace) :
    fderiv ℝ (vectorField c) p v =
      !₂[q (radiusSq₁ p) * v 0 + 2 * deriv q (radiusSq₁ p) *
          (p 0 * v 0 + p 1 * v 1) * p 0 - v 1,
        q (radiusSq₁ p) * v 1 + 2 * deriv q (radiusSq₁ p) *
          (p 0 * v 0 + p 1 * v 1) * p 1 + v 0,
        q (radiusSq₂ p) * v 2 + 2 * deriv q (radiusSq₂ p) *
          (p 2 * v 2 + p 3 * v 3) * p 2 - Real.sqrt 2 * v 3,
        q (radiusSq₂ p) * v 3 + 2 * deriv q (radiusSq₂ p) *
          (p 2 * v 2 + p 3 * v 3) * p 3 + Real.sqrt 2 * v 2,
        -c * v 4] := by
  have hd := ((contDiff_vectorField c 1).differentiable one_ne_zero p).hasFDerivAt
  have hcoord (i : Fin 5) : fderiv ℝ (fun u => vectorField c u i) p v =
      fderiv ℝ (vectorField c) p v i := by
    have h := (PiLp.hasFDerivAt_apply 2 (vectorField c p) i).comp p hd
    change HasFDerivAt (fun u => vectorField c u i) _ p at h
    rw [h.fderiv]
    rfl
  ext i
  rw [← hcoord i]
  fin_cases i
  · simpa [vectorField, radiusSq₁] using fderiv_planarVectorX_apply 1
      (PiLp.hasFDerivAt_apply 2 p 0) (PiLp.hasFDerivAt_apply 2 p 1) v
  · simpa [vectorField, radiusSq₁] using fderiv_planarVectorY_apply 1
      (PiLp.hasFDerivAt_apply 2 p 0) (PiLp.hasFDerivAt_apply 2 p 1) v
  · simpa [vectorField, radiusSq₂] using fderiv_planarVectorX_apply (Real.sqrt 2)
      (PiLp.hasFDerivAt_apply 2 p 2) (PiLp.hasFDerivAt_apply 2 p 3) v
  · simpa [vectorField, radiusSq₂] using fderiv_planarVectorY_apply (Real.sqrt 2)
      (PiLp.hasFDerivAt_apply 2 p 2) (PiLp.hasFDerivAt_apply 2 p 3) v
  · have hw := (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 p 4).const_mul (-c)
    simpa [vectorField] using congrArg (fun L : PhaseSpace →L[ℝ] ℝ => L v) hw.fderiv

end Eden
