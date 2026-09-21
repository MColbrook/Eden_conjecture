import Eden.ExteriorSingularValues
import Eden.Uniqueness

/-!
# Exterior composition and the derivative cocycle

The derivative cocycle follows by differentiating the proved semigroup
identity at every ambient point. Functoriality of exterior powers and
submultiplicativity of the usual operator norm then give the integer
singular-value-product inequality. All times are real and nonnegative.
-/

noncomputable section
namespace Eden

theorem exteriorOperator_comp (k : ℕ) (A B : PhaseSpace →ₗ[ℝ] PhaseSpace) :
    exteriorOperator k (A ∘ₗ B) = (exteriorOperator k A).comp (exteriorOperator k B) := by
  apply ContinuousLinearMap.ext
  intro v
  exact congrArg (fun f : ExteriorSpace k →ₗ[ℝ] ExteriorSpace k => f v)
    (exteriorPower.map_comp B A)

/-- The integer product is submultiplicative for arbitrary ambient maps,
including singular maps. -/
theorem singularValueFunction_integer_comp_le {k : ℕ} (hk : k ≤ 5)
    (A B : PhaseSpace →ₗ[ℝ] PhaseSpace) :
    singularValueFunction (A ∘ₗ B) k ≤ singularValueFunction A k * singularValueFunction B k := by
  rw [← norm_exteriorOperator_eq_singularValueFunction hk,
    ← norm_exteriorOperator_eq_singularValueFunction hk A,
    ← norm_exteriorOperator_eq_singularValueFunction hk B, exteriorOperator_comp]
  exact ContinuousLinearMap.opNorm_comp_le _ _

/-- The Frechet derivative of the flow satisfies the cocycle law. -/
theorem fderiv_evolution_add (c : ℝ) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    (p : PhaseSpace) :
    fderiv ℝ (evolution c (s + t)) p =
      (fderiv ℝ (evolution c t) (evolution c s p)).comp (fderiv ℝ (evolution c s) p) := by
  have he : evolution c (s + t) = (evolution c t) ∘ (evolution c s) :=
    funext (evolution_add c hs ht)
  rw [he]
  exact fderiv_comp p ((contDiff_evolution c ht 1).differentiable one_ne_zero _)
    ((contDiff_evolution c hs 1).differentiable one_ne_zero p)

theorem singularValueFunction_evolution_add_le {k : ℕ} (hk : k ≤ 5) (c : ℝ)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (p : PhaseSpace) :
    singularValueFunction (fderiv ℝ (evolution c (s + t)) p).toLinearMap k ≤
      singularValueFunction (fderiv ℝ (evolution c t) (evolution c s p)).toLinearMap k *
        singularValueFunction (fderiv ℝ (evolution c s) p).toLinearMap k := by
  rw [fderiv_evolution_add c hs ht p]
  exact singularValueFunction_integer_comp_le hk _ _

theorem singularValueFunction_integer_evolution_pos {k : ℕ} (hk : k ≤ 5) (c : ℝ)
    {t : ℝ} (ht : 0 ≤ t) (p : PhaseSpace) :
    0 < singularValueFunction (fderiv ℝ (evolution c t) p).toLinearMap k := by
  obtain ⟨s, hs⟩ := (isGreatest_exteriorFactor hk c ht p).1
  rw [← hs]
  exact exteriorFactor_pos k c ht p s

theorem singularValueFunction_integer_evolution_zero {k : ℕ} (hk : k ≤ 5)
    (c : ℝ) (p : PhaseSpace) :
    singularValueFunction (fderiv ℝ (evolution c 0) p).toLinearMap k = 1 := by
  obtain ⟨s, hs⟩ := (isGreatest_exteriorFactor hk c (le_refl (0 : ℝ)) p).1
  rw [← hs]
  have hd : derivativeFactors c 0 p = WithLp.toLp 2 (fun _ : Fin 5 => (1 : ℝ)) := by
    ext i
    fin_cases i <;> simp [derivativeFactors]
  simp [exteriorFactor, hd]

end Eden
