import Eden.RadialDynamics
import Eden.Evolution
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# The compact invariant sets

The squared-radius identities connect the scalar dynamics to the
five-dimensional evolution. Compactness follows from the Euclidean norm
and Mathlib's finite-dimensional proper-space theorem.
-/

noncomputable section
namespace Eden

theorem radiusSq₁_nonneg (p : PhaseSpace) : 0 ≤ radiusSq₁ p := by
  exact add_nonneg (sq_nonneg _) (sq_nonneg _)

theorem radiusSq₂_nonneg (p : PhaseSpace) : 0 ≤ radiusSq₂ p := by
  exact add_nonneg (sq_nonneg _) (sq_nonneg _)

theorem continuous_radiusSq₁ : Continuous radiusSq₁ := by
  unfold radiusSq₁
  fun_prop

theorem continuous_radiusSq₂ : Continuous radiusSq₂ := by
  unfold radiusSq₂
  fun_prop

theorem radiusSq₁_evolution (c : ℝ) {t : ℝ} (ht : 0 ≤ t) (p : PhaseSpace) :
    radiusSq₁ (evolution c t p) = squaredRadiusEvolution t (radiusSq₁ p) := by
  simpa [radiusSq₁, evolution] using planar_radius_sq 1 ht (p 0) (p 1)

theorem radiusSq₂_evolution (c : ℝ) {t : ℝ} (ht : 0 ≤ t) (p : PhaseSpace) :
    radiusSq₂ (evolution c t p) = squaredRadiusEvolution t (radiusSq₂ p) := by
  simpa [radiusSq₂, evolution] using planar_radius_sq (Real.sqrt 2) ht (p 2) (p 3)

theorem evolution_mem_attractor (c : ℝ) {t : ℝ} (ht : 0 ≤ t)
    {p : PhaseSpace} (hp : p ∈ attractor) : evolution c t p ∈ attractor := by
  rcases hp with ⟨h₁, h₂, h₄⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [radiusSq₁_evolution c ht]
    exact (squaredRadiusEvolution_le_two_iff ht).2 h₁
  · rw [radiusSq₂_evolution c ht]
    exact (squaredRadiusEvolution_le_two_iff ht).2 h₂
  · simp [evolution, h₄]

theorem evolution_mem_torus (c : ℝ) {t : ℝ} (ht : 0 ≤ t)
    {p : PhaseSpace} (hp : p ∈ torus) : evolution c t p ∈ torus := by
  rcases hp with ⟨h₁, h₂, h₄⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [radiusSq₁_evolution c ht, h₁, squaredRadiusEvolution_at_one]
  · rw [radiusSq₂_evolution c ht, h₂, squaredRadiusEvolution_at_one]
  · simp [evolution, h₄]

theorem torus_subset_attractor : torus ⊆ attractor := by
  intro p hp
  exact ⟨le_trans hp.1.le (by norm_num), le_trans hp.2.1.le (by norm_num), hp.2.2⟩

theorem isClosed_attractor : IsClosed attractor := by
  have hw : Continuous (fun p : PhaseSpace => p 4) := by fun_prop
  exact (isClosed_le continuous_radiusSq₁ continuous_const).inter
    ((isClosed_le continuous_radiusSq₂ continuous_const).inter
      (isClosed_eq hw continuous_const))

theorem isClosed_torus : IsClosed torus := by
  have hw : Continuous (fun p : PhaseSpace => p 4) := by fun_prop
  exact (isClosed_eq continuous_radiusSq₁ continuous_const).inter
    ((isClosed_eq continuous_radiusSq₂ continuous_const).inter
      (isClosed_eq hw continuous_const))

theorem norm_sq_phaseSpace (p : PhaseSpace) :
    ‖p‖ ^ 2 = radiusSq₁ p + radiusSq₂ p + p 4 ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [Fin.sum_univ_succ, radiusSq₁, radiusSq₂]
  ring

theorem norm_le_two_of_mem_attractor {p : PhaseSpace} (hp : p ∈ attractor) :
    ‖p‖ ≤ 2 := by
  have hn := norm_sq_phaseSpace p
  rcases hp with ⟨h₁, h₂, h₄⟩
  rw [h₄] at hn
  nlinarith [norm_nonneg p]

theorem isCompact_attractor : IsCompact attractor := by
  apply (isCompact_closedBall (0 : PhaseSpace) 2).of_isClosed_subset isClosed_attractor
  intro p hp
  simpa only [Metric.mem_closedBall, dist_zero_right] using norm_le_two_of_mem_attractor hp

theorem isCompact_torus : IsCompact torus :=
  isCompact_attractor.of_isClosed_subset isClosed_torus torus_subset_attractor

theorem attractor_nonempty : attractor.Nonempty := by
  refine ⟨0, ?_⟩
  norm_num [attractor, radiusSq₁, radiusSq₂]

theorem torus_nonempty : torus.Nonempty := by
  refine ⟨!₂[1, 0, 1, 0, 0], ?_⟩
  change (1 : ℝ) ^ 2 + 0 ^ 2 = 1 ∧ (1 : ℝ) ^ 2 + 0 ^ 2 = 1 ∧ (0 : ℝ) = 0
  norm_num

end Eden
