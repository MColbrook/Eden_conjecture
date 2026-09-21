import Eden.PlanarFlow
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic.FinCases

/-!
# Global forward solutions of the five-dimensional equation

The explicit planar solutions and the exponential fifth coordinate give a
solution for every initial point and every nonnegative time. Coordinatewise
calculus uses Mathlib's `PiLp` derivative API in the ambient Euclidean norm
(Anatole Dedecker and Eric Wieser).
-/

noncomputable section
namespace Eden

/-- Explicit evolution of the five-dimensional polynomial equation. Its ODE
and initial condition hold on the entire nonnegative time half-line. -/
def evolution (c t : ℝ) (p : PhaseSpace) : PhaseSpace :=
  !₂[planarX 1 t (p 0) (p 1), planarY 1 t (p 0) (p 1),
     planarX (Real.sqrt 2) t (p 2) (p 3), planarY (Real.sqrt 2) t (p 2) (p 3),
     Real.exp (-c * t) * p 4]

@[simp] theorem evolution_zero_time (c : ℝ) (p : PhaseSpace) : evolution c 0 p = p := by
  ext i
  fin_cases i <;> simp [evolution]

/-- Coordinate derivatives assemble into the Euclidean vector derivative. -/
theorem hasDerivAt_euclidean_of_coord {n : ℕ}
    {f : ℝ → EuclideanSpace ℝ (Fin n)} {v : EuclideanSpace ℝ (Fin n)} {t : ℝ}
    (hf : ∀ i, HasDerivAt (fun τ => f τ i) (v i) t) : HasDerivAt f v t := by
  rw [hasDerivAt_iff_hasFDerivAt, ← hasFDerivWithinAt_univ]
  apply (hasFDerivWithinAt_piLp (p := 2)).2
  intro i
  rw [ContinuousLinearMap.comp_toSpanSingleton]
  exact (hf i).hasDerivWithinAt

/-- The explicit evolution satisfies the Cartesian vector field. -/
theorem hasDerivAt_evolution (c : ℝ) {t : ℝ} (ht : 0 ≤ t) (p : PhaseSpace) :
    HasDerivAt (fun τ => evolution c τ p) (vectorField c (evolution c t p)) t := by
  apply hasDerivAt_euclidean_of_coord
  intro i
  fin_cases i
  · simpa [evolution, vectorField, radiusSq₁] using
      hasDerivAt_planarX 1 ht (p 0) (p 1)
  · simpa [evolution, vectorField, radiusSq₁] using
      hasDerivAt_planarY 1 ht (p 0) (p 1)
  · simpa [evolution, vectorField, radiusSq₂] using
      hasDerivAt_planarX (Real.sqrt 2) ht (p 2) (p 3)
  · simpa [evolution, vectorField, radiusSq₂] using
      hasDerivAt_planarY (Real.sqrt 2) ht (p 2) (p 3)
  · have hw := (((hasDerivAt_id t).const_mul (-c)).exp).mul_const (p 4)
    simpa [evolution, vectorField, mul_assoc, mul_comm, mul_left_comm] using hw

/-- A global forward solution exists through every point of the ambient space.
-/
theorem exists_global_forward_solution (c : ℝ) (p : PhaseSpace) :
    ∃ f : ℝ → PhaseSpace, f 0 = p ∧
      ∀ t, 0 ≤ t → HasDerivAt f (vectorField c (f t)) t :=
  ⟨fun t => evolution c t p, evolution_zero_time c p,
    fun _ ht => hasDerivAt_evolution c ht p⟩

/-- Polynomial smoothness of the vector field, at every differentiability order. -/
theorem contDiff_vectorField (c : ℝ) (n : WithTop ℕ∞) : ContDiff ℝ n (vectorField c) := by
  rw [contDiff_piLp]
  intro i
  fin_cases i <;> simp [vectorField, radiusSq₁, radiusSq₂, q] <;> fun_prop

end Eden
