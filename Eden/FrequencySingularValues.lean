import Eden.FrequencyRotation
import Eden.OrderedStationarySpectrum

/-!
# Unchanged ambient singular values throughout the frequency family

The derivative has the same positive diagonal factors and initial
frame, with a different orthogonal output map. The existing Gram-spectrum
proof and uniqueness of the ordered multiset retain every multiplicity.
-/

noncomputable section
namespace Eden

theorem fderiv_frequencyEvolution_orthogonal (c ν : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (p : PhaseSpace) :
    (fderiv ℝ (frequencyEvolution c ν t) p).toLinearMap =
      orthogonalDiagonalMap (((radialFrame p).trans (angularRotation t)).trans
        (frequencyCorrection ν t)) (radialFrame p) (derivativeFactors c t p) := by
  ext v : 1
  rw [fderiv_frequencyEvolution c ν ht]
  have h := fderiv_evolution_radialFrame c ht p ((radialFrame p).symm v)
  simpa [orthogonalDiagonalMap] using congrArg (frequencyCorrection ν t) h

/-- Full five-value multiset identity, including zero radii and time zero. -/
theorem singularValues_fderiv_frequencyEvolution (c ν : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (p : PhaseSpace) :
    Finset.univ.val.map (fun i : Fin 5 =>
      (fderiv ℝ (frequencyEvolution c ν t) p).toLinearMap.singularValues i) =
      Finset.univ.val.map (fun i : Fin 5 => derivativeFactors c t p i) := by
  rw [fderiv_frequencyEvolution_orthogonal c ν ht]
  exact singularValues_orthogonalDiagonalMap _ _ _
    (fun i => (derivativeFactors_pos c ht p i).le)

theorem ordered_singularValues_frequencyEvolution (c ν : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (p : PhaseSpace) :
    (fun i : Fin 5 => (fderiv ℝ (frequencyEvolution c ν t) p).toLinearMap.singularValues i) =
      fun i : Fin 5 => (fderiv ℝ (evolution c t) p).toLinearMap.singularValues i := by
  apply antitone_eq_of_multiset_eq
  · exact fun i j hij => (fderiv ℝ (frequencyEvolution c ν t) p).toLinearMap.singularValues_antitone hij
  · exact fun i j hij => (fderiv ℝ (evolution c t) p).toLinearMap.singularValues_antitone hij
  · exact (singularValues_fderiv_frequencyEvolution c ν ht p).trans
      (singularValues_fderiv_evolution c ht p).symm

/-- Equality of the singular-value sequences, including their zero tails. -/
theorem singularValues_frequencyEvolution_eq (c ν : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (p : PhaseSpace) :
    (fderiv ℝ (frequencyEvolution c ν t) p).toLinearMap.singularValues =
      (fderiv ℝ (evolution c t) p).toLinearMap.singularValues := by
  ext i
  by_cases hi : i < 5
  · exact congrFun (ordered_singularValues_frequencyEvolution c ν ht p) ⟨i, hi⟩
  · rw [LinearMap.singularValues_of_finrank_le, LinearMap.singularValues_of_finrank_le]
    all_goals simpa only [finrank_euclideanSpace_fin] using Nat.le_of_not_gt hi

theorem fderiv_frequencyEvolution_bijective (c ν : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (p : PhaseSpace) : Function.Bijective (fderiv ℝ (frequencyEvolution c ν t) p) := by
  rw [fderiv_frequencyEvolution c ν ht]
  exact (frequencyCorrection ν t).bijective.comp (fderiv_evolution_bijective c ht p)

end Eden
