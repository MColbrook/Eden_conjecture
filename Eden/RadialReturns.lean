import Eden.InvariantSets
import Eden.StationaryFactors

/-!
# Positive-time returns force stationary radii

The explicit scalar solution excludes nonstationary radial returns. Applied to
the Cartesian evolution, this restricts every positive-time return to the three
stationary squared radii. When `c>0`, the fifth coordinate of every returning
point also vanishes.
-/

noncomputable section
namespace Eden

/-- At positive time, the only fixed initial squared radii are 0, 1 and 2. -/
theorem squaredRadiusEvolution_eq_self_iff {t s : ℝ} (ht : 0 < t) :
    squaredRadiusEvolution t s = s ↔ s = 0 ∨ s = 1 ∨ s = 2 := by
  constructor
  · intro h
    by_cases hs : s = 1
    · exact Or.inr (Or.inl hs)
    have hR := sqrt_radialDiscriminant_pos ht.le s
    have hratio : (s - 1) / Real.sqrt (radialDiscriminant t s) = s - 1 := by
      dsimp [squaredRadiusEvolution] at h
      linarith
    have hmul := (div_eq_iff (ne_of_gt hR)).mp hratio
    have hprod : (s - 1) * (Real.sqrt (radialDiscriminant t s) - 1) = 0 := by
      nlinarith
    have hroot : Real.sqrt (radialDiscriminant t s) = 1 := by
      have := (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hs)
      linarith
    have hD : radialDiscriminant t s = 1 := by
      have hsq := Real.sq_sqrt (radialDiscriminant_pos ht.le s).le
      rw [hroot] at hsq
      nlinarith
    have hE : 0 < 1 - Real.exp (-4 * t) := by
      have := Real.exp_lt_one_iff.mpr (show -4 * t < 0 by linarith)
      linarith
    have hprod₂ : (1 - Real.exp (-4 * t)) * (s * (s - 2)) = 0 := by
      dsimp [radialDiscriminant] at hD
      nlinarith
    have hsprod := (mul_eq_zero.mp hprod₂).resolve_left (ne_of_gt hE)
    rcases mul_eq_zero.mp hsprod with hs₀ | hs₂
    · exact Or.inl hs₀
    · exact Or.inr (Or.inr (by linarith))
  · rintro (rfl | rfl | rfl) <;> simp

theorem radiusSq₁_eq_zero_iff (p : PhaseSpace) :
    radiusSq₁ p = 0 ↔ p 0 = 0 ∧ p 1 = 0 := by
  constructor
  · intro h
    dsimp [radiusSq₁] at h
    constructor <;> nlinarith [sq_nonneg (p 0), sq_nonneg (p 1)]
  · rintro ⟨h₀, h₁⟩
    simp [radiusSq₁, h₀, h₁]

theorem radiusSq₂_eq_zero_iff (p : PhaseSpace) :
    radiusSq₂ p = 0 ↔ p 2 = 0 ∧ p 3 = 0 := by
  constructor
  · intro h
    dsimp [radiusSq₂] at h
    constructor <;> nlinarith [sq_nonneg (p 2), sq_nonneg (p 3)]
  · rintro ⟨h₂, h₃⟩
    simp [radiusSq₂, h₂, h₃]

theorem stationary_radii_of_evolution_return (c : ℝ) {t : ℝ} (ht : 0 < t)
    {p : PhaseSpace} (h : evolution c t p = p) :
    (radiusSq₁ p = 0 ∨ radiusSq₁ p = 1 ∨ radiusSq₁ p = 2) ∧
    (radiusSq₂ p = 0 ∨ radiusSq₂ p = 1 ∨ radiusSq₂ p = 2) := by
  constructor
  · apply (squaredRadiusEvolution_eq_self_iff ht).mp
    simpa only [radiusSq₁_evolution c ht.le p] using congrArg radiusSq₁ h
  · apply (squaredRadiusEvolution_eq_self_iff ht).mp
    simpa only [radiusSq₂_evolution c ht.le p] using congrArg radiusSq₂ h

theorem fifth_eq_zero_of_evolution_return {c t : ℝ} (hc : 0 < c) (ht : 0 < t)
    {p : PhaseSpace} (h : evolution c t p = p) : p 4 = 0 := by
  have h₄ := congrArg (fun q : PhaseSpace => q 4) h
  have heq : Real.exp (-c * t) * p 4 = p 4 := by simpa [evolution] using h₄
  have hE : Real.exp (-c * t) < 1 :=
    Real.exp_lt_one_iff.mpr (by nlinarith [mul_pos hc ht])
  have hprod : (Real.exp (-c * t) - 1) * p 4 = 0 := by nlinarith
  exact (mul_eq_zero.mp hprod).resolve_left (ne_of_lt (by linarith))

end Eden
