import Eden.RotationReturns

/-!
# Equilibria and periodic points

The sets below refer to the vector field and positive real return times of its
evolution. The circles are specified by squared radius; their ordinary radii are
one and `sqrt(2)` in the applications.
-/

noncomputable section
open Set
namespace Eden

/-- Equilibria of the Cartesian vector field. -/
def equilibriumSet (c : ℝ) : Set PhaseSpace := {p | vectorField c p = 0}

/-- Points with a positive real return time, including stationary points. -/
def positiveReturnSet (c : ℝ) : Set PhaseSpace :=
  {p | ∃ t : ℝ, 0 < t ∧ evolution c t p = p}

/-- The union of equilibria and periodic points in the attractor. -/
def periodicEquilibriumSet (c : ℝ) : Set PhaseSpace :=
  attractor ∩ (equilibriumSet c ∪ positiveReturnSet c)

/-- Circle of squared radius `s` in the first plane, with all other coordinates
zero. -/
def firstCircle (s : ℝ) : Set PhaseSpace :=
  {p | radiusSq₁ p = s ∧ radiusSq₂ p = 0 ∧ p 4 = 0}

/-- Circle of squared radius `s` in the second plane, with all other coordinates
zero. -/
def secondCircle (s : ℝ) : Set PhaseSpace :=
  {p | radiusSq₁ p = 0 ∧ radiusSq₂ p = s ∧ p 4 = 0}

@[simp] theorem evolution_origin (c t : ℝ) : evolution c t 0 = 0 := by
  ext i
  fin_cases i <;> simp [evolution]

theorem eq_zero_of_radii_and_fifth_zero {p : PhaseSpace}
    (h₁ : radiusSq₁ p = 0) (h₂ : radiusSq₂ p = 0) (hw : p 4 = 0) : p = 0 := by
  obtain ⟨h₀, h₁⟩ := (radiusSq₁_eq_zero_iff p).mp h₁
  obtain ⟨h₂, h₃⟩ := (radiusSq₂_eq_zero_iff p).mp h₂
  ext i
  fin_cases i <;> simp_all

/-- The origin is the unique equilibrium whenever the fifth-coordinate coefficient
is nonzero. -/
theorem vectorField_eq_zero_iff {c : ℝ} (hc : c ≠ 0) (p : PhaseSpace) :
    vectorField c p = 0 ↔ p = 0 := by
  constructor
  · intro h
    have h₀ : q (radiusSq₁ p) * p 0 - p 1 = 0 := by
      simpa [vectorField] using congrArg (fun v : PhaseSpace => v 0) h
    have h₁ : q (radiusSq₁ p) * p 1 + p 0 = 0 := by
      simpa [vectorField] using congrArg (fun v : PhaseSpace => v 1) h
    have h₂ : q (radiusSq₂ p) * p 2 - Real.sqrt 2 * p 3 = 0 := by
      simpa [vectorField] using congrArg (fun v : PhaseSpace => v 2) h
    have h₃ : q (radiusSq₂ p) * p 3 + Real.sqrt 2 * p 2 = 0 := by
      simpa [vectorField] using congrArg (fun v : PhaseSpace => v 3) h
    have hw : -c * p 4 = 0 := by
      simpa [vectorField] using congrArg (fun v : PhaseSpace => v 4) h
    apply eq_zero_of_radii_and_fifth_zero
    · dsimp [radiusSq₁]
      nlinarith [congrArg (fun a : ℝ => p 0 * a) h₁,
        congrArg (fun a : ℝ => p 1 * a) h₀]
    · have hprod : Real.sqrt 2 * (p 2 ^ 2 + p 3 ^ 2) = 0 := by
        nlinarith [congrArg (fun a : ℝ => p 2 * a) h₃,
          congrArg (fun a : ℝ => p 3 * a) h₂]
      exact (mul_eq_zero.mp hprod).resolve_left (ne_of_gt (by positivity))
    · exact (mul_eq_zero.mp hw).resolve_left (neg_ne_zero.mpr hc)
  · rintro rfl
    ext i
    fin_cases i <;> simp [vectorField, radiusSq₁, radiusSq₂]

theorem equilibriumSet_eq_singleton {c : ℝ} (hc : c ≠ 0) :
    equilibriumSet c = {0} := by
  ext p
  exact vectorField_eq_zero_iff hc p

theorem first_plane_return (c : ℝ) {p : PhaseSpace}
    (h₁ : radiusSq₁ p = 1 ∨ radiusSq₁ p = 2)
    (h₂ : radiusSq₂ p = 0) (hw : p 4 = 0) :
    evolution c (2 * Real.pi) p = p := by
  have ht : 0 ≤ 2 * Real.pi := by positivity
  have hg : planarAmplitude (2 * Real.pi) (p 0 ^ 2 + p 1 ^ 2) = 1 := by
    change planarAmplitude (2 * Real.pi) (radiusSq₁ p) = 1
    rcases h₁ with h₁ | h₁
    · rw [h₁, planarAmplitude_at_one ht]
    · rw [h₁, planarAmplitude_at_two ht]
  obtain ⟨h₂, h₃⟩ := (radiusSq₂_eq_zero_iff p).mp h₂
  ext i
  fin_cases i <;> simp [evolution, planarX, planarY, hg, h₂, h₃, hw]

theorem second_plane_return (c : ℝ) {p : PhaseSpace}
    (h₁ : radiusSq₁ p = 0) (h₂ : radiusSq₂ p = 1 ∨ radiusSq₂ p = 2)
    (hw : p 4 = 0) : evolution c (2 * Real.pi / Real.sqrt 2) p = p := by
  have ht : 0 ≤ 2 * Real.pi / Real.sqrt 2 := by positivity
  have hangle : Real.sqrt 2 * (2 * Real.pi / Real.sqrt 2) = 2 * Real.pi := by
    field_simp
  have hg : planarAmplitude (2 * Real.pi / Real.sqrt 2) (p 2 ^ 2 + p 3 ^ 2) = 1 := by
    change planarAmplitude (2 * Real.pi / Real.sqrt 2) (radiusSq₂ p) = 1
    rcases h₂ with h₂ | h₂
    · rw [h₂, planarAmplitude_at_one ht]
    · rw [h₂, planarAmplitude_at_two ht]
  obtain ⟨h₀, h₁⟩ := (radiusSq₁_eq_zero_iff p).mp h₁
  ext i
  fin_cases i <;> simp [evolution, planarX, planarY, hg, hangle, h₀, h₁, hw]

/-- Every positive-return point is the origin or lies on exactly one of the four
circles; the converse supplies explicit positive return times. -/
theorem mem_positiveReturnSet_iff {c : ℝ} (hc : 0 < c) (p : PhaseSpace) :
    p ∈ positiveReturnSet c ↔ p = 0 ∨ p ∈ firstCircle 1 ∨ p ∈ firstCircle 2 ∨
      p ∈ secondCircle 1 ∨ p ∈ secondCircle 2 := by
  constructor
  · rintro ⟨t, ht, hret⟩
    have hs := stationary_radii_of_evolution_return c ht hret
    have hw := fifth_eq_zero_of_evolution_return hc ht hret
    rcases one_radius_zero_of_evolution_return c ht hret with h₁ | h₂
    · rcases hs.2 with h₂ | h₂ | h₂
      · exact Or.inl (eq_zero_of_radii_and_fifth_zero h₁ h₂ hw)
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h₁, h₂, hw⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨h₁, h₂, hw⟩)))
    · rcases hs.1 with h₁ | h₁ | h₁
      · exact Or.inl (eq_zero_of_radii_and_fifth_zero h₁ h₂ hw)
      · exact Or.inr (Or.inl ⟨h₁, h₂, hw⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨h₁, h₂, hw⟩))
  · rintro (rfl | h | h | h | h)
    · exact ⟨1, by norm_num, evolution_origin c 1⟩
    · exact ⟨2 * Real.pi, by positivity, first_plane_return c (Or.inl h.1) h.2.1 h.2.2⟩
    · exact ⟨2 * Real.pi, by positivity, first_plane_return c (Or.inr h.1) h.2.1 h.2.2⟩
    · exact ⟨2 * Real.pi / Real.sqrt 2, by positivity,
        second_plane_return c h.1 (Or.inl h.2.1) h.2.2⟩
    · exact ⟨2 * Real.pi / Real.sqrt 2, by positivity,
        second_plane_return c h.1 (Or.inr h.2.1) h.2.2⟩

theorem positiveReturnSet_subset_attractor {c : ℝ} (hc : 0 < c) :
    positiveReturnSet c ⊆ attractor := by
  intro p hp
  rcases (mem_positiveReturnSet_iff hc p).mp hp with rfl | h | h | h | h
  · simp [attractor, radiusSq₁, radiusSq₂]
  all_goals constructor
  all_goals first | linarith [h.1] | exact ⟨by linarith [h.2.1], h.2.2⟩

theorem periodicEquilibriumSet_eq_positiveReturnSet {c : ℝ} (hc : 0 < c) :
    periodicEquilibriumSet c = positiveReturnSet c := by
  ext p
  constructor
  · rintro ⟨hp, heq | hret⟩
    · have hz := (vectorField_eq_zero_iff (ne_of_gt hc) p).mp heq
      subst p
      exact ⟨1, by norm_num, evolution_origin c 1⟩
    · exact hret
  · intro hp
    exact ⟨positiveReturnSet_subset_attractor hc hp, Or.inr hp⟩

end Eden
