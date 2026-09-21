import Eden.VectorFieldDerivative

/-!
# Global divergence of the vector field

Divergence is the trace of the Fréchet derivative. Mathlib's
basis-independent trace-to-matrix theorem reduces it to the Euclidean
coordinate diagonal (Johannes Hölzl, Patrick Massot, Casper Putz,
Anne Baanen and Antoine Labelle).
-/

noncomputable section
namespace Eden

/-- Divergence of the ambient vector field, defined by derivative trace. -/
def divergence (c : ℝ) (p : PhaseSpace) : ℝ :=
  LinearMap.trace ℝ PhaseSpace (fderiv ℝ (vectorField c) p).toLinearMap

theorem divergence_eq_rates (c : ℝ) (p : PhaseSpace) :
    divergence c p = radialRate (radiusSq₁ p) + tangentialRate (radiusSq₁ p) +
      radialRate (radiusSq₂ p) + tangentialRate (radiusSq₂ p) - c := by
  unfold divergence
  rw [LinearMap.trace_eq_matrix_trace ℝ (EuclideanSpace.basisFun (Fin 5) ℝ).toBasis]
  simp [Matrix.trace, LinearMap.toMatrix_apply, EuclideanSpace.basisFun_apply,
    OrthonormalBasis.coe_toBasis_repr_apply, PiLp.single_apply, Fin.sum_univ_succ,
    fderiv_vectorField_apply, radialRate_eq_q_add_deriv, tangentialRate_eq_q]
  dsimp [radiusSq₁, radiusSq₂]
  ring

/-- The exact global divergence identity holds at every ambient point and
for every real parameter. -/
theorem divergence_eq (c : ℝ) (p : PhaseSpace) :
    divergence c p = 4 - c - 6 * (radiusSq₁ p - 1) ^ 2 - 6 * (radiusSq₂ p - 1) ^ 2 := by
  rw [divergence_eq_rates]
  exact total_rate_identity _ _ _

theorem divergence_le (c : ℝ) (p : PhaseSpace) : divergence c p ≤ 4 - c := by
  rw [divergence_eq_rates]
  exact total_rate_le _ _ _

theorem divergence_neg {c : ℝ} (hc : 4 < c) (p : PhaseSpace) : divergence c p < 0 := by
  linarith [divergence_le c p]

end Eden
