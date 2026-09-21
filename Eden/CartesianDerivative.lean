import Eden.InitialDerivative
import Mathlib.Analysis.Calculus.FDeriv.Pow

/-!
# Cartesian formula for the ambient derivative

The derivative is calculated by the chain and product rules. The formulas
remain valid when a planar coordinate is zero and impose no radius bound.
They are identities for Mathlib's Fréchet derivative of `evolution`.
-/

noncomputable section
namespace Eden

/-- First Cartesian component of the planar derivative at `(x,y)` applied to
the direction `(dx,dy)`, for angular frequency `Ω` and time `t ≥ 0`.
The connection to the derivative is proved in `fderiv_planarX_apply`. -/
def planarDerivativeX (Ω t x y dx dy : ℝ) : ℝ :=
  planarAmplitude t (x ^ 2 + y ^ 2) * (dx * Real.cos (Ω * t) - dy * Real.sin (Ω * t)) +
    2 * deriv (planarAmplitude t) (x ^ 2 + y ^ 2) * (x * dx + y * dy) *
      (x * Real.cos (Ω * t) - y * Real.sin (Ω * t))

/-- Second Cartesian component of the planar derivative at `(x,y)` applied to
the direction `(dx,dy)`, for angular frequency `Ω` and time `t ≥ 0`.
The connection to the derivative is proved in `fderiv_planarY_apply`. -/
def planarDerivativeY (Ω t x y dx dy : ℝ) : ℝ :=
  planarAmplitude t (x ^ 2 + y ^ 2) * (dx * Real.sin (Ω * t) + dy * Real.cos (Ω * t)) +
    2 * deriv (planarAmplitude t) (x ^ 2 + y ^ 2) * (x * dx + y * dy) *
      (x * Real.sin (Ω * t) + y * Real.cos (Ω * t))

section Composition
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f g : E → ℝ} {f' g' : E →L[ℝ] ℝ} {p : E}

theorem fderiv_planarX_apply (Ω : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (hf : HasFDerivAt f f' p) (hg : HasFDerivAt g g' p) (v : E) :
    fderiv ℝ (fun u => planarX Ω t (f u) (g u)) p v =
      planarDerivativeX Ω t (f p) (g p) (f' v) (g' v) := by
  have hr := (hf.pow 2).add (hg.pow 2)
  have ha := (contDiffAt_planarAmplitude ht
    (add_nonneg (sq_nonneg (f p)) (sq_nonneg (g p))) 1).differentiableAt_one.hasDerivAt
  have hcomp := ha.comp_hasFDerivAt p hr
  have hrot := (hf.mul_const (Real.cos (Ω * t))).sub (hg.mul_const (Real.sin (Ω * t)))
  have hprod := hcomp.mul hrot
  change HasFDerivAt (fun u => planarX Ω t (f u) (g u)) _ p at hprod
  rw [hprod.fderiv]
  simp [planarDerivativeX, smul_eq_mul]
  ring

theorem fderiv_planarY_apply (Ω : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (hf : HasFDerivAt f f' p) (hg : HasFDerivAt g g' p) (v : E) :
    fderiv ℝ (fun u => planarY Ω t (f u) (g u)) p v =
      planarDerivativeY Ω t (f p) (g p) (f' v) (g' v) := by
  have hr := (hf.pow 2).add (hg.pow 2)
  have ha := (contDiffAt_planarAmplitude ht
    (add_nonneg (sq_nonneg (f p)) (sq_nonneg (g p))) 1).differentiableAt_one.hasDerivAt
  have hcomp := ha.comp_hasFDerivAt p hr
  have hrot := (hf.mul_const (Real.sin (Ω * t))).add (hg.mul_const (Real.cos (Ω * t)))
  have hprod := hcomp.mul hrot
  change HasFDerivAt (fun u => planarY Ω t (f u) (g u)) _ p at hprod
  rw [hprod.fderiv]
  simp [planarDerivativeY, smul_eq_mul]
  ring

end Composition

/-- Every coordinate of the five-dimensional Fréchet derivative. -/
theorem fderiv_evolution_apply (c : ℝ) {t : ℝ} (ht : 0 ≤ t) (p v : PhaseSpace) :
    fderiv ℝ (evolution c t) p v =
      !₂[planarDerivativeX 1 t (p 0) (p 1) (v 0) (v 1),
         planarDerivativeY 1 t (p 0) (p 1) (v 0) (v 1),
         planarDerivativeX (Real.sqrt 2) t (p 2) (p 3) (v 2) (v 3),
         planarDerivativeY (Real.sqrt 2) t (p 2) (p 3) (v 2) (v 3),
         Real.exp (-c * t) * v 4] := by
  have hd := ((contDiff_evolution c ht 1).differentiable one_ne_zero p).hasFDerivAt
  have hcoord (i : Fin 5) : fderiv ℝ (fun u => evolution c t u i) p v =
      fderiv ℝ (evolution c t) p v i := by
    have h := (PiLp.hasFDerivAt_apply 2 (evolution c t p) i).comp p hd
    change HasFDerivAt (fun u => evolution c t u i) _ p at h
    rw [h.fderiv]
    rfl
  ext i
  rw [← hcoord i]
  fin_cases i
  · simpa [evolution] using fderiv_planarX_apply 1 ht
      (PiLp.hasFDerivAt_apply 2 p 0) (PiLp.hasFDerivAt_apply 2 p 1) v
  · simpa [evolution] using fderiv_planarY_apply 1 ht
      (PiLp.hasFDerivAt_apply 2 p 0) (PiLp.hasFDerivAt_apply 2 p 1) v
  · simpa [evolution] using fderiv_planarX_apply (Real.sqrt 2) ht
      (PiLp.hasFDerivAt_apply 2 p 2) (PiLp.hasFDerivAt_apply 2 p 3) v
  · simpa [evolution] using fderiv_planarY_apply (Real.sqrt 2) ht
      (PiLp.hasFDerivAt_apply 2 p 2) (PiLp.hasFDerivAt_apply 2 p 3) v
  · have hw := (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 p 4).const_mul (Real.exp (-c * t))
    simpa [evolution] using congrArg (fun L : PhaseSpace →L[ℝ] ℝ => L v) hw.fderiv

end Eden
