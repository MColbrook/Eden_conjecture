import Eden.Evolution
import Eden.InvariantSets

/-!
# The ambient frequency family

The second angular frequency is an arbitrary real parameter. The Cartesian
planar solution and differentiation formulas give the ambient evolution
for every initial point and every nonnegative time.
-/

noncomputable section
namespace Eden

/-- The original five-dimensional polynomial field with second frequency ν. -/
def frequencyVectorField (c ν : ℝ) (p : PhaseSpace) : PhaseSpace :=
  !₂[q (radiusSq₁ p) * p 0 - p 1, q (radiusSq₁ p) * p 1 + p 0,
     q (radiusSq₂ p) * p 2 - ν * p 3, q (radiusSq₂ p) * p 3 + ν * p 2, -c * p 4]

/-- Explicit full ambient evolution for the frequency-dependent ODE. -/
def frequencyEvolution (c ν t : ℝ) (p : PhaseSpace) : PhaseSpace :=
  !₂[planarX 1 t (p 0) (p 1), planarY 1 t (p 0) (p 1),
     planarX ν t (p 2) (p 3), planarY ν t (p 2) (p 3), Real.exp (-c * t) * p 4]

theorem frequencyVectorField_sqrt_two (c : ℝ) :
    frequencyVectorField c (Real.sqrt 2) = vectorField c := rfl

theorem frequencyEvolution_sqrt_two (c t : ℝ) :
    frequencyEvolution c (Real.sqrt 2) t = evolution c t := rfl

@[simp] theorem frequencyEvolution_zero_time (c ν : ℝ) (p : PhaseSpace) :
    frequencyEvolution c ν 0 p = p := by
  ext i
  fin_cases i <;> simp [frequencyEvolution]

/-- The time derivative is the new field, including at time zero. -/
theorem hasDerivAt_frequencyEvolution (c ν : ℝ) {t : ℝ} (ht : 0 ≤ t) (p : PhaseSpace) :
    HasDerivAt (fun τ => frequencyEvolution c ν τ p)
      (frequencyVectorField c ν (frequencyEvolution c ν t p)) t := by
  apply hasDerivAt_euclidean_of_coord
  intro i
  fin_cases i
  · simpa [frequencyEvolution, frequencyVectorField, radiusSq₁] using
      hasDerivAt_planarX 1 ht (p 0) (p 1)
  · simpa [frequencyEvolution, frequencyVectorField, radiusSq₁] using
      hasDerivAt_planarY 1 ht (p 0) (p 1)
  · simpa [frequencyEvolution, frequencyVectorField, radiusSq₂] using
      hasDerivAt_planarX ν ht (p 2) (p 3)
  · simpa [frequencyEvolution, frequencyVectorField, radiusSq₂] using
      hasDerivAt_planarY ν ht (p 2) (p 3)
  · have hw := (((hasDerivAt_id t).const_mul (-c)).exp).mul_const (p 4)
    simpa [frequencyEvolution, frequencyVectorField, mul_assoc, mul_comm, mul_left_comm] using hw

theorem exists_frequency_global_forward_solution (c ν : ℝ) (p : PhaseSpace) :
    ∃ f : ℝ → PhaseSpace, f 0 = p ∧
      ∀ t, 0 ≤ t → HasDerivAt f (frequencyVectorField c ν (f t)) t :=
  ⟨fun t => frequencyEvolution c ν t p, frequencyEvolution_zero_time c ν p,
    fun _ ht => hasDerivAt_frequencyEvolution c ν ht p⟩

theorem contDiff_frequencyVectorField (c ν : ℝ) (n : WithTop ℕ∞) :
    ContDiff ℝ n (frequencyVectorField c ν) := by
  rw [contDiff_piLp]
  intro i
  fin_cases i <;> simp [frequencyVectorField, radiusSq₁, radiusSq₂, q] <;> fun_prop

/-- Both squared-radius trajectories are identical throughout the frequency family. -/
theorem radiusSq_frequencyEvolution (c ν : ℝ) {t : ℝ} (ht : 0 ≤ t) (p : PhaseSpace) :
    radiusSq₁ (frequencyEvolution c ν t p) = squaredRadiusEvolution t (radiusSq₁ p) ∧
    radiusSq₂ (frequencyEvolution c ν t p) = squaredRadiusEvolution t (radiusSq₂ p) := by
  constructor
  · exact planar_radius_sq 1 ht _ _
  · exact planar_radius_sq ν ht _ _

theorem frequencyEvolution_fifth (c ν t : ℝ) (p : PhaseSpace) :
    frequencyEvolution c ν t p 4 = Real.exp (-c * t) * p 4 := rfl

end Eden
