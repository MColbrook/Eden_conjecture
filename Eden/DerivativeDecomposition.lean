import Eden.DerivativeFrames

/-!
# Orthogonal factorisation of the ambient derivative

The initial radial frames and their angular rotations give a diagonal form
with positive entries. The equality below is proved for Mathlib's Fréchet
derivative of the five-dimensional evolution, at every ambient point.
It includes zero radii through the Cartesian convention for `radialFrame`.
-/

noncomputable section
namespace Eden

/-- A diagonal real linear map in the fixed Cartesian coordinates. -/
def diagonalLinear (d : PhaseSpace) : PhaseSpace →ₗ[ℝ] PhaseSpace where
  toFun v := WithLp.toLp 2 (fun i => d i * v i)
  map_add' := by intro v w; ext i; simp [mul_add]
  map_smul' := by intro r v; ext i; simp [smul_eq_mul]; ring

@[simp] theorem diagonalLinear_apply (d v : PhaseSpace) (i : Fin 5) :
    diagonalLinear d v i = d i * v i := rfl

/-- The two radial/tangential pairs and the fifth-coordinate factor in the
orthogonal factorisation of the derivative. -/
def derivativeFactors (c t : ℝ) (p : PhaseSpace) : PhaseSpace :=
  !₂[radialAmplitude t (radiusSq₁ p), planarAmplitude t (radiusSq₁ p),
     radialAmplitude t (radiusSq₂ p), planarAmplitude t (radiusSq₂ p), Real.exp (-c * t)]

theorem derivativeFactors_pos (c : ℝ) {t : ℝ} (ht : 0 ≤ t) (p : PhaseSpace) (i : Fin 5) :
    0 < derivativeFactors c t p i := by
  have h₁ : 0 ≤ radiusSq₁ p := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have h₂ : 0 ≤ radiusSq₂ p := add_nonneg (sq_nonneg _) (sq_nonneg _)
  fin_cases i
  · exact radialAmplitude_pos ht h₁
  · exact planarAmplitude_pos ht h₁
  · exact radialAmplitude_pos ht h₂
  · exact planarAmplitude_pos ht h₂
  · exact Real.exp_pos _

/-- Action of the derivative on the whole initial orthonormal frame. -/
theorem fderiv_evolution_radialFrame (c : ℝ) {t : ℝ} (ht : 0 ≤ t) (p v : PhaseSpace) :
    fderiv ℝ (evolution c t) p (radialFrame p v) =
      angularRotation t (radialFrame p (diagonalLinear (derivativeFactors c t p) v)) := by
  have hsq₁ := Real.sq_sqrt (add_nonneg (sq_nonneg (p 0)) (sq_nonneg (p 1)))
  have hsq₂ := Real.sq_sqrt (add_nonneg (sq_nonneg (p 2)) (sq_nonneg (p 3)))
  have hX₁ := planarDerivativeX_on_radialFrame 1 ht
    (radialCos (p 0) (p 1)) (radialSin (p 0) (p 1))
    (Real.sqrt (p 0 ^ 2 + p 1 ^ 2)) (v 0) (v 1) (radialCos_sq_add_radialSin_sq _ _)
  have hY₁ := planarDerivativeY_on_radialFrame 1 ht
    (radialCos (p 0) (p 1)) (radialSin (p 0) (p 1))
    (Real.sqrt (p 0 ^ 2 + p 1 ^ 2)) (v 0) (v 1) (radialCos_sq_add_radialSin_sq _ _)
  have hX₂ := planarDerivativeX_on_radialFrame (Real.sqrt 2) ht
    (radialCos (p 2) (p 3)) (radialSin (p 2) (p 3))
    (Real.sqrt (p 2 ^ 2 + p 3 ^ 2)) (v 2) (v 3) (radialCos_sq_add_radialSin_sq _ _)
  have hY₂ := planarDerivativeY_on_radialFrame (Real.sqrt 2) ht
    (radialCos (p 2) (p 3)) (radialSin (p 2) (p 3))
    (Real.sqrt (p 2 ^ 2 + p 3 ^ 2)) (v 2) (v 3) (radialCos_sq_add_radialSin_sq _ _)
  simp only [radius_mul_radialCos, radius_mul_radialSin, hsq₁, one_mul] at hX₁ hY₁
  simp only [radius_mul_radialCos, radius_mul_radialSin, hsq₂] at hX₂ hY₂
  rw [fderiv_evolution_apply c ht]
  ext i
  fin_cases i
  · simpa [radialFrame, angularRotation, rotateBlocks, diagonalLinear, derivativeFactors,
      radiusSq₁, mul_comm] using hX₁
  · simpa [radialFrame, angularRotation, rotateBlocks, diagonalLinear, derivativeFactors,
      radiusSq₁, mul_comm] using hY₁
  · simpa [radialFrame, angularRotation, rotateBlocks, diagonalLinear, derivativeFactors,
      radiusSq₂, mul_comm] using hX₂
  · simpa [radialFrame, angularRotation, rotateBlocks, diagonalLinear, derivativeFactors,
      radiusSq₂, mul_comm] using hY₂
  · simp [radialFrame, angularRotation, rotateBlocks, diagonalLinear, derivativeFactors]

/-- Orthogonal-diagonal-orthogonal factorisation of the derivative,
with input radial frame fixed by the initial point. -/
theorem fderiv_evolution_orthogonal_decomposition (c : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (p : PhaseSpace) :
    (fderiv ℝ (evolution c t) p).toLinearMap =
      (angularRotation t).toLinearEquiv.toLinearMap ∘ₗ
        (radialFrame p).toLinearEquiv.toLinearMap ∘ₗ
          diagonalLinear (derivativeFactors c t p) ∘ₗ
            (radialFrame p).symm.toLinearEquiv.toLinearMap := by
  ext v : 1
  have h := fderiv_evolution_radialFrame c ht p ((radialFrame p).symm v)
  simpa using h

theorem diagonalLinear_bijective {d : PhaseSpace} (hd : ∀ i, d i ≠ 0) :
    Function.Bijective (diagonalLinear d) := by
  constructor
  · intro v w h
    ext i
    have hi := congrArg (fun u : PhaseSpace => u i) h
    exact mul_left_cancel₀ (hd i) hi
  · intro v
    refine ⟨WithLp.toLp 2 (fun i => v i / d i), ?_⟩
    ext i
    simp only [diagonalLinear_apply]
    field_simp [hd i]

/-- The derivative is invertible at every finite nonnegative time. -/
theorem fderiv_evolution_bijective (c : ℝ) {t : ℝ} (ht : 0 ≤ t) (p : PhaseSpace) :
    Function.Bijective (fderiv ℝ (evolution c t) p) := by
  have heq := fderiv_evolution_orthogonal_decomposition c ht p
  change Function.Bijective (fderiv ℝ (evolution c t) p).toLinearMap
  rw [heq]
  have h := (angularRotation t).bijective.comp ((radialFrame p).bijective.comp
    ((diagonalLinear_bijective (fun i => ne_of_gt (derivativeFactors_pos c ht p i))).comp
      (radialFrame p).symm.bijective))
  exact h

end Eden
