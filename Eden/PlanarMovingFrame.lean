import Eden.PlanarDerivative

/-!
# Variations in the rotating orthonormal frame

The perturbation is the derivative applied to an initial variation, expressed in
the rotating radial frame. Its two components satisfy the decoupled variational
equations. The right derivative at time zero is also included; the ordinary
derivative statement holds at every positive time.
-/

noncomputable section
namespace Eden

/-- Components in the moving orthonormal frame of a variation, whose initial
components in the radial frame are v. -/
def planarMovingPerturbation (Ω t : ℝ) (p v : PlanarSpace) : PlanarSpace :=
  (planarRadialFrame p).symm ((planarAngularRotation Ω t).symm
    (fderiv ℝ (planarEvolution Ω t) p (planarRadialFrame p v)))

theorem planarMovingPerturbation_eq (Ω : ℝ) {t : ℝ} (ht : 0 ≤ t) (p v : PlanarSpace) :
    planarMovingPerturbation Ω t p v = planarDiagonal (planarFactors t p) v := by
  simp [planarMovingPerturbation, fderiv_planarEvolution_radialFrame Ω ht]

@[simp] theorem planarMovingPerturbation_zero_time (Ω : ℝ) (p v : PlanarSpace) :
    planarMovingPerturbation Ω 0 p v = v := by
  rw [planarMovingPerturbation_eq Ω le_rfl]
  ext i
  fin_cases i <;> simp [planarDiagonal, planarFactors]

/-- The right-sided variational equations include time zero and zero initial radius,
using the Cartesian input frame in the latter case. -/
theorem hasDerivWithinAt_planarMovingPerturbation (Ω : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (p v : PlanarSpace) :
    HasDerivWithinAt (fun τ => planarMovingPerturbation Ω τ p v)
      (!₂[radialRate (planarEvolution Ω t p 0 ^ 2 + planarEvolution Ω t p 1 ^ 2) *
          planarMovingPerturbation Ω t p v 0,
        tangentialRate (planarEvolution Ω t p 0 ^ 2 + planarEvolution Ω t p 1 ^ 2) *
          planarMovingPerturbation Ω t p v 1]) (Set.Ici 0) t := by
  have hs := add_nonneg (sq_nonneg (p 0)) (sq_nonneg (p 1))
  have hd : HasDerivAt (fun τ => planarDiagonal (planarFactors τ p) v)
      (!₂[radialRate (squaredRadiusEvolution t (p 0 ^ 2 + p 1 ^ 2)) *
          (radialAmplitude t (p 0 ^ 2 + p 1 ^ 2) * v 0),
        tangentialRate (squaredRadiusEvolution t (p 0 ^ 2 + p 1 ^ 2)) *
          (planarAmplitude t (p 0 ^ 2 + p 1 ^ 2) * v 1)]) t := by
    apply hasDerivAt_euclidean_of_coord
    intro i
    fin_cases i
    · simpa [planarDiagonal, planarFactors, mul_assoc] using
        (hasDerivAt_radialAmplitude ht hs).mul_const (v 0)
    · simpa [planarDiagonal, planarFactors, tangentialRate_eq_q, mul_assoc] using
        (hasDerivAt_planarAmplitude ht hs).mul_const (v 1)
  have h : HasDerivWithinAt (fun τ => planarMovingPerturbation Ω τ p v)
      (!₂[radialRate (squaredRadiusEvolution t (p 0 ^ 2 + p 1 ^ 2)) *
          (radialAmplitude t (p 0 ^ 2 + p 1 ^ 2) * v 0),
        tangentialRate (squaredRadiusEvolution t (p 0 ^ 2 + p 1 ^ 2)) *
          (planarAmplitude t (p 0 ^ 2 + p 1 ^ 2) * v 1)]) (Set.Ici 0) t :=
    hd.hasDerivWithinAt.congr_of_mem
      (fun τ hτ => planarMovingPerturbation_eq Ω hτ p v) ht
  rw [planarMovingPerturbation_eq Ω ht]
  simpa [planarEvolution, planar_radius_sq Ω ht, planarDiagonal, planarFactors] using h

/-- The two components of a variation obey xi'=a(s)xi and eta'=b(s)eta in the moving
orthonormal frame, at every positive time. -/
theorem hasDerivAt_planarMovingPerturbation (Ω : ℝ) {t : ℝ} (ht : 0 < t)
    (p v : PlanarSpace) :
    HasDerivAt (fun τ => planarMovingPerturbation Ω τ p v)
      (!₂[radialRate (planarEvolution Ω t p 0 ^ 2 + planarEvolution Ω t p 1 ^ 2) *
          planarMovingPerturbation Ω t p v 0,
        tangentialRate (planarEvolution Ω t p 0 ^ 2 + planarEvolution Ω t p 1 ^ 2) *
          planarMovingPerturbation Ω t p v 1]) t :=
  (hasDerivWithinAt_planarMovingPerturbation Ω ht.le p v).hasDerivAt (Ici_mem_nhds ht)

end Eden
