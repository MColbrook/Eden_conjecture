import Eden.CircleOrbits

/-!
# Angular coordinates on the invariant torus

The parametrization is onto the torus and is periodic by `2*pi` in either angle.
Its evolution is the linear angular motion with exact frequencies one and
`sqrt(2)`, for every real time.
-/

noncomputable section
open Set
namespace Eden

/-- The two standard angular coordinates, mapped into Euclidean phase space. -/
def torusPoint (θ₁ θ₂ : ℝ) : PhaseSpace :=
  !₂[Real.cos θ₁, Real.sin θ₁, Real.cos θ₂, Real.sin θ₂, 0]

theorem torusPoint_mem (θ₁ θ₂ : ℝ) : torusPoint θ₁ θ₂ ∈ torus := by
  simp [torusPoint, torus, radiusSq₁, radiusSq₂, Real.cos_sq_add_sin_sq]

theorem exists_torusPoint_of_mem {p : PhaseSpace} (hp : p ∈ torus) :
    ∃ θ₁ θ₂ : ℝ, torusPoint θ₁ θ₂ = p := by
  obtain ⟨θ₁, _, hx₁, hy₁⟩ := exists_positive_rotation_between
    (show (0 : ℝ) < 1 by norm_num) (x := 1) (y := 0) (by norm_num) hp.1
  obtain ⟨θ₂, _, hx₂, hy₂⟩ := exists_positive_rotation_between
    (show (0 : ℝ) < 1 by norm_num) (x := 1) (y := 0) (by norm_num) hp.2.1
  simp only [one_mul, zero_mul, sub_zero, add_zero] at hx₁ hy₁ hx₂ hy₂
  refine ⟨θ₁, θ₂, ?_⟩
  ext i
  fin_cases i <;> simp [torusPoint, hx₁, hy₁, hx₂, hy₂, hp.2.2]

theorem torusPoint_add_two_pi_first (θ₁ θ₂ : ℝ) :
    torusPoint (θ₁ + 2 * Real.pi) θ₂ = torusPoint θ₁ θ₂ := by
  simp [torusPoint]

theorem torusPoint_add_two_pi_second (θ₁ θ₂ : ℝ) :
    torusPoint θ₁ (θ₂ + 2 * Real.pi) = torusPoint θ₁ θ₂ := by
  simp [torusPoint]

theorem planarAmplitude_at_one_all (t : ℝ) : planarAmplitude t 1 = 1 := by
  have hD : 0 < radialDiscriminant t 1 := by
    simpa [radialDiscriminant] using Real.exp_pos (-4 * t)
  have hB : amplitudeSq t 1 = 1 := by
    simpa using mul_amplitudeSq_of_discriminant_pos hD
  simp [planarAmplitude, hB]

/-- The torus flow is the irrational linear angular flow, for all real times and all
real c; the angular map is periodic in both coordinates. -/
theorem evolution_torusPoint (c t θ₁ θ₂ : ℝ) :
    evolution c t (torusPoint θ₁ θ₂) =
      torusPoint (θ₁ + t) (θ₂ + Real.sqrt 2 * t) := by
  ext i
  fin_cases i <;> simp [evolution, torusPoint, planarX, planarY,
    Real.cos_sq_add_sin_sq, planarAmplitude_at_one_all, Real.cos_add, Real.sin_add] <;> ring

theorem torus_invariant_all_real (c t : ℝ) {p : PhaseSpace} (hp : p ∈ torus) :
    evolution c t p ∈ torus := by
  obtain ⟨θ₁, θ₂, rfl⟩ := exists_torusPoint_of_mem hp
  rw [evolution_torusPoint]
  exact torusPoint_mem _ _

end Eden
