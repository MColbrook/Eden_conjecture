import Eden.FrequencyEvolution
import Eden.DerivativeDecomposition

/-!
# The frequency change as an ambient isometry

At each fixed time, changing the second frequency rotates the second output
plane. Differentiation gives the corresponding identity for the ambient
Fréchet derivatives.
-/

noncomputable section
open Set
namespace Eden

/-- Additional rotation of the second output plane relative to frequency sqrt2. -/
def frequencyCorrection (ν t : ℝ) : PhaseSpace ≃ₗᵢ[ℝ] PhaseSpace :=
  blockRotation 1 0 (Real.cos ((ν - Real.sqrt 2) * t)) (Real.sin ((ν - Real.sqrt 2) * t))
    (by norm_num) (Real.cos_sq_add_sin_sq _)

/-- Changing frequency is a time-dependent output isometry of the flow. -/
theorem frequencyEvolution_eq_correction (c ν t : ℝ) (p : PhaseSpace) :
    frequencyEvolution c ν t p = frequencyCorrection ν t (evolution c t p) := by
  ext i
  fin_cases i <;> simp [frequencyEvolution, evolution, frequencyCorrection, rotateBlocks,
    planarX, planarY]
  all_goals
    rw [show ν * t = (ν - Real.sqrt 2) * t + Real.sqrt 2 * t by ring, Real.cos_add, Real.sin_add]
    ring

theorem radiusSq_frequencyCorrection (ν t : ℝ) (p : PhaseSpace) :
    radiusSq₁ (frequencyCorrection ν t p) = radiusSq₁ p ∧
    radiusSq₂ (frequencyCorrection ν t p) = radiusSq₂ p := by
  constructor
  · simp [frequencyCorrection, rotateBlocks, radiusSq₁]
  · have h := congrArg (fun z : ℝ => z * (p 2 ^ 2 + p 3 ^ 2))
      (Real.cos_sq_add_sin_sq ((ν - Real.sqrt 2) * t))
    simp [frequencyCorrection, rotateBlocks, radiusSq₂]
    nlinarith

theorem frequencyCorrection_fifth (ν t : ℝ) (p : PhaseSpace) :
    frequencyCorrection ν t p 4 = p 4 := rfl

theorem frequencyCorrection_mem_attractor_iff (ν t : ℝ) (p : PhaseSpace) :
    frequencyCorrection ν t p ∈ attractor ↔ p ∈ attractor := by
  simp only [attractor, mem_ofPred_eq, (radiusSq_frequencyCorrection ν t p).1,
    (radiusSq_frequencyCorrection ν t p).2, frequencyCorrection_fifth]

theorem frequencyCorrection_mem_torus_iff (ν t : ℝ) (p : PhaseSpace) :
    frequencyCorrection ν t p ∈ torus ↔ p ∈ torus := by
  simp only [torus, mem_ofPred_eq, (radiusSq_frequencyCorrection ν t p).1,
    (radiusSq_frequencyCorrection ν t p).2, frequencyCorrection_fifth]

theorem frequencyCorrection_image_attractor (ν t : ℝ) :
    frequencyCorrection ν t '' attractor = attractor := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact (frequencyCorrection_mem_attractor_iff ν t q).2 hq
  · intro hp
    refine ⟨(frequencyCorrection ν t).symm p, ?_, (frequencyCorrection ν t).apply_symm_apply p⟩
    apply (frequencyCorrection_mem_attractor_iff ν t _).1
    simpa using hp

theorem frequencyCorrection_image_torus (ν t : ℝ) :
    frequencyCorrection ν t '' torus = torus := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact (frequencyCorrection_mem_torus_iff ν t q).2 hq
  · intro hp
    refine ⟨(frequencyCorrection ν t).symm p, ?_, (frequencyCorrection ν t).apply_symm_apply p⟩
    apply (frequencyCorrection_mem_torus_iff ν t _).1
    simpa using hp

theorem contDiff_frequencyEvolution (c ν : ℝ) {t : ℝ} (ht : 0 ≤ t) (n : WithTop ℕ∞) :
    ContDiff ℝ n (frequencyEvolution c ν t) := by
  have he : frequencyEvolution c ν t = (frequencyCorrection ν t) ∘ evolution c t :=
    funext (frequencyEvolution_eq_correction c ν t)
  rw [he]
  exact (frequencyCorrection ν t).toContinuousLinearEquiv.contDiff.comp (contDiff_evolution c ht n)

/-- The ambient derivative differs only by an orthogonal output map. -/
theorem fderiv_frequencyEvolution (c ν : ℝ) {t : ℝ} (ht : 0 ≤ t) (p : PhaseSpace) :
    fderiv ℝ (frequencyEvolution c ν t) p =
      (frequencyCorrection ν t).toContinuousLinearEquiv.toContinuousLinearMap.comp
        (fderiv ℝ (evolution c t) p) := by
  have he : frequencyEvolution c ν t = (frequencyCorrection ν t) ∘ evolution c t :=
    funext (frequencyEvolution_eq_correction c ν t)
  rw [he]
  exact ((frequencyCorrection ν t).toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp p
    ((contDiff_evolution c ht 1).differentiable one_ne_zero p).hasFDerivAt).fderiv

end Eden
