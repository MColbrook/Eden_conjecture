import Eden.Evolution
import Eden.RadialDynamics
import Eden.PhysicalRadius

/-!
# Complete trajectories inside the attractor

For initial squared radii in [0,2], the discriminant and squared amplitude
are positive at every real time. The local calculus lemmas therefore prove
the Cartesian ODE on the entire real line, with values in A.
-/

noncomputable section
namespace Eden

theorem amplitudeSq_pos_on_interval (t : ℝ) {s : ℝ} (hs₀ : 0 ≤ s) (hs₂ : s ≤ 2) :
    0 < amplitudeSq t s := by
  have hD := radialDiscriminant_pos_on_interval t hs₀ hs₂
  have hR := Real.sqrt_pos.2 hD
  have hsq := Real.sq_sqrt hD.le
  have he := Real.exp_pos (-4 * t)
  have hu : (s - 1) ^ 2 ≤ 1 := by nlinarith
  have hm := mul_nonneg (sub_nonneg.mpr hu) he.le
  have hbound : (s - 1) ^ 2 ≤ radialDiscriminant t s := by
    dsimp [radialDiscriminant]
    nlinarith
  have hRge : 1 - s ≤ Real.sqrt (radialDiscriminant t s) := by
    nlinarith
  have hnum : 0 < Real.sqrt (radialDiscriminant t s) + 1 +
      (s - 2) * (1 - Real.exp (-4 * t)) := by
    rcases lt_or_eq_of_le hs₂ with hs₂ | hs₂
    · have hp := mul_pos (sub_pos.mpr hs₂) he
      nlinarith
    · subst s
      nlinarith
  have hden : 0 < Real.sqrt (radialDiscriminant t s) + 1 := by linarith
  have hquot : -1 < (s - 2) * (1 - Real.exp (-4 * t)) /
      (Real.sqrt (radialDiscriminant t s) + 1) :=
    (lt_div_iff₀ hden).2 (by linarith)
  exact div_pos (by linarith) hR

theorem squaredRadiusEvolution_mem_lower_interval (t : ℝ) {s : ℝ}
    (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1) :
    squaredRadiusEvolution t s ∈ Set.Icc 0 1 := by
  have hS := squaredRadiusEvolution_mem_interval t hs₀ (by linarith : s ≤ 2)
  have hR := Real.sqrt_pos.2 (radialDiscriminant_pos_on_interval t hs₀ (by linarith : s ≤ 2))
  refine ⟨hS.1, ?_⟩
  have hq : (s - 1) / Real.sqrt (radialDiscriminant t s) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) hR.le
  dsimp [squaredRadiusEvolution]
  linarith

theorem squaredRadiusEvolution_mem_upper_interval (t : ℝ) {s : ℝ}
    (hs₁ : 1 ≤ s) (hs₂ : s ≤ 2) :
    squaredRadiusEvolution t s ∈ Set.Icc 1 2 := by
  have hS := squaredRadiusEvolution_mem_interval t (by linarith : 0 ≤ s) hs₂
  refine ⟨?_, hS.2⟩
  have hq : 0 ≤ (s - 1) / Real.sqrt (radialDiscriminant t s) :=
    div_nonneg (by linarith) (Real.sqrt_nonneg _)
  dsimp [squaredRadiusEvolution]
  linarith

theorem hasDerivAt_evolution_of_mem_attractor (c t : ℝ) {p : PhaseSpace}
    (hp : p ∈ attractor) :
    HasDerivAt (fun τ => evolution c τ p) (vectorField c (evolution c t p)) t := by
  have hs₁ : 0 ≤ p 0 ^ 2 + p 1 ^ 2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hs₂ : 0 ≤ p 2 ^ 2 + p 3 ^ 2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hD₁ := radialDiscriminant_pos_on_interval t hs₁ hp.1
  have hD₂ := radialDiscriminant_pos_on_interval t hs₂ hp.2.1
  have hB₁ := amplitudeSq_pos_on_interval t hs₁ hp.1
  have hB₂ := amplitudeSq_pos_on_interval t hs₂ hp.2.1
  apply hasDerivAt_euclidean_of_coord
  intro i
  fin_cases i
  · simpa [evolution, vectorField, radiusSq₁] using hasDerivAt_planarX_of_pos 1 hD₁ hB₁
  · simpa [evolution, vectorField, radiusSq₁] using hasDerivAt_planarY_of_pos 1 hD₁ hB₁
  · simpa [evolution, vectorField, radiusSq₂] using hasDerivAt_planarX_of_pos (Real.sqrt 2) hD₂ hB₂
  · simpa [evolution, vectorField, radiusSq₂] using hasDerivAt_planarY_of_pos (Real.sqrt 2) hD₂ hB₂
  · have hw := (((hasDerivAt_id t).const_mul (-c)).exp).mul_const (p 4)
    simpa [evolution, vectorField, mul_assoc, mul_comm, mul_left_comm] using hw

theorem radiusSq₁_evolution_all_time (c t : ℝ) {p : PhaseSpace} (hp : p ∈ attractor) :
    radiusSq₁ (evolution c t p) = squaredRadiusEvolution t (radiusSq₁ p) := by
  have hs : 0 ≤ p 0 ^ 2 + p 1 ^ 2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
  simpa [evolution, radiusSq₁] using planar_radius_sq_of_pos 1
    (radialDiscriminant_pos_on_interval t hs hp.1) (amplitudeSq_pos_on_interval t hs hp.1)

theorem radiusSq₂_evolution_all_time (c t : ℝ) {p : PhaseSpace} (hp : p ∈ attractor) :
    radiusSq₂ (evolution c t p) = squaredRadiusEvolution t (radiusSq₂ p) := by
  have hs : 0 ≤ p 2 ^ 2 + p 3 ^ 2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
  simpa [evolution, radiusSq₂] using planar_radius_sq_of_pos (Real.sqrt 2)
    (radialDiscriminant_pos_on_interval t hs hp.2.1) (amplitudeSq_pos_on_interval t hs hp.2.1)

theorem evolution_mem_attractor_all_time (c t : ℝ) {p : PhaseSpace} (hp : p ∈ attractor) :
    evolution c t p ∈ attractor := by
  have hs₁ : 0 ≤ radiusSq₁ p := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hs₂ : 0 ≤ radiusSq₂ p := add_nonneg (sq_nonneg _) (sq_nonneg _)
  refine ⟨?_, ?_, ?_⟩
  · rw [radiusSq₁_evolution_all_time c t hp]
    exact (squaredRadiusEvolution_mem_interval t hs₁ hp.1).2
  · rw [radiusSq₂_evolution_all_time c t hp]
    exact (squaredRadiusEvolution_mem_interval t hs₂ hp.2.1).2
  · simp [evolution, hp.2.2]

/-- For every real `c`, every point of `A` lies on an ODE solution
defined for all real times and remaining in `A`. -/
theorem exists_complete_solution_in_attractor (c : ℝ) {p : PhaseSpace} (hp : p ∈ attractor) :
    ∃ f : ℝ → PhaseSpace, f 0 = p ∧ ∀ t : ℝ,
      f t ∈ attractor ∧ HasDerivAt f (vectorField c (f t)) t :=
  ⟨fun t => evolution c t p, evolution_zero_time c p, fun t =>
    ⟨evolution_mem_attractor_all_time c t hp, hasDerivAt_evolution_of_mem_attractor c t hp⟩⟩

theorem radiusEvolution_mem_lower_interval (t : ℝ) {r : ℝ} (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1) :
    radiusEvolution t r ∈ Set.Icc 0 1 := by
  have hS := squaredRadiusEvolution_mem_lower_interval t (sq_nonneg r)
    (show r ^ 2 ≤ 1 by nlinarith)
  exact ⟨Real.sqrt_nonneg _, by simpa only [radiusEvolution, Real.sqrt_one] using Real.sqrt_le_sqrt hS.2⟩

theorem radiusEvolution_mem_upper_interval (t : ℝ) {r : ℝ}
    (hr₁ : 1 ≤ r) (hr₂ : r ≤ Real.sqrt 2) :
    radiusEvolution t r ∈ Set.Icc 1 (Real.sqrt 2) := by
  have hsq : r ^ 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg (2 : ℝ)]
  have hS := squaredRadiusEvolution_mem_upper_interval t (show 1 ≤ r ^ 2 by nlinarith) hsq
  exact ⟨by simpa only [radiusEvolution, Real.sqrt_one] using Real.sqrt_le_sqrt hS.1, Real.sqrt_le_sqrt hS.2⟩

theorem hasDerivAt_radiusEvolution_all_time (t : ℝ) {r : ℝ}
    (hr₀ : 0 ≤ r) (hr₂ : r ≤ Real.sqrt 2) :
    HasDerivAt (fun τ => radiusEvolution τ r) (radialField (radiusEvolution t r)) t := by
  rcases eq_or_lt_of_le hr₀ with hr | hr
  · subst r
    simpa [radialField] using hasDerivAt_const t (0 : ℝ)
  have hs₂ : r ^ 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg (2 : ℝ)]
  have hD := radialDiscriminant_pos_on_interval t (sq_nonneg r) hs₂
  have hB := amplitudeSq_pos_on_interval t (sq_nonneg r) hs₂
  have hpos : 0 < squaredRadiusEvolution t (r ^ 2) := by
    rw [← mul_amplitudeSq_of_discriminant_pos hD]
    exact mul_pos (sq_pos_of_pos hr) hB
  have hR : 0 < radiusEvolution t r := Real.sqrt_pos.2 hpos
  have hsq : radiusEvolution t r ^ 2 = squaredRadiusEvolution t (r ^ 2) :=
    Real.sq_sqrt hpos.le
  apply ((hasDerivAt_squaredRadiusEvolution_of_discriminant_pos hD).sqrt hpos.ne').congr_deriv
  change (-2 * squaredRadiusEvolution t (r ^ 2) *
      (squaredRadiusEvolution t (r ^ 2) - 1) *
      (squaredRadiusEvolution t (r ^ 2) - 2)) /
      (2 * radiusEvolution t r) = radialField (radiusEvolution t r)
  rw [← hsq]
  unfold radialField
  field_simp

end Eden
