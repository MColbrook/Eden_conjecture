import Eden.FrequencyDimensions
import Eden.FrequencyAttractor
import Eden.FrequencyUniqueness
import Mathlib.Topology.Instances.Rat

/-!
# Periodic maximisers at positive rational frequencies

The angular formula gives a common period 2*pi*b when ν=a/b. The unchanged torus
maximisers are nonstationary periodic points of the changed ODE. Density of the
rationals supplies positive rational frequencies arbitrarily close to √2.
-/

noncomputable section
open Set
namespace Eden

theorem frequencyEvolution_torusPoint (c ν t θ₁ θ₂ : ℝ) :
    frequencyEvolution c ν t (torusPoint θ₁ θ₂) = torusPoint (θ₁ + t) (θ₂ + ν * t) := by
  ext i
  fin_cases i <;> simp [frequencyEvolution, torusPoint, planarX, planarY,
    Real.cos_sq_add_sin_sq, planarAmplitude_at_one_all, Real.cos_add, Real.sin_add] <;> ring

theorem frequencyEvolution_add_on_torus (c ν s t : ℝ) {p : PhaseSpace} (hp : p ∈ torus) :
    frequencyEvolution c ν (s + t) p = frequencyEvolution c ν t (frequencyEvolution c ν s p) := by
  obtain ⟨θ₁, θ₂, rfl⟩ := exists_torusPoint_of_mem hp
  simp only [frequencyEvolution_torusPoint]
  congr 1 <;> ring

/-- The common return time for any integer/natural representation ν=a/b, b>0. -/
theorem frequency_torus_common_return (c : ℝ) {ν : ℝ} {a : ℤ} {b : ℕ}
    (hb : 0 < b) (hν : ν = (a : ℝ) / (b : ℝ)) {p : PhaseSpace} (hp : p ∈ torus) :
    frequencyEvolution c ν (2 * Real.pi * b) p = p := by
  obtain ⟨θ₁, θ₂, rfl⟩ := exists_torusPoint_of_mem hp
  rw [frequencyEvolution_torusPoint]
  have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  have hangle : ν * (2 * Real.pi * b) = (a : ℝ) * (2 * Real.pi) := by
    rw [hν]
    field_simp
  rw [hangle, show 2 * Real.pi * (b : ℝ) = (b : ℝ) * (2 * Real.pi) by ring]
  ext i
  fin_cases i <;> simp [torusPoint]

/-- Every complete torus trajectory has this common positive period. -/
theorem frequency_torus_common_period (c : ℝ) {ν : ℝ} {a : ℤ} {b : ℕ}
    (hb : 0 < b) (hν : ν = (a : ℝ) / (b : ℝ)) {p : PhaseSpace} (hp : p ∈ torus) :
    0 < 2 * Real.pi * b ∧
      Function.Periodic (fun t : ℝ => frequencyEvolution c ν t p) (2 * Real.pi * b) := by
  constructor
  · positivity
  · intro t
    change frequencyEvolution c ν (t + 2 * Real.pi * b) p = frequencyEvolution c ν t p
    rw [add_comm t, frequencyEvolution_add_on_torus c ν _ t hp,
      frequency_torus_common_return c hb hν hp]

theorem rational_frequency_torus_period (c : ℝ) (ν : ℚ) {p : PhaseSpace} (hp : p ∈ torus) :
    0 < 2 * Real.pi * ν.den ∧
      Function.Periodic (fun t : ℝ => frequencyEvolution c (ν : ℝ) t p) (2 * Real.pi * ν.den) := by
  exact frequency_torus_common_period c ν.pos (Rat.cast_def ν) hp

theorem frequency_torus_not_equilibrium (c ν : ℝ) {p : PhaseSpace} (hp : p ∈ torus) :
    frequencyVectorField c ν p ≠ 0 := by
  intro h
  have h₀ := congrArg (fun v : PhaseSpace => v 0) h
  have h₁ := congrArg (fun v : PhaseSpace => v 1) h
  simp [frequencyVectorField, hp.1, q] at h₀ h₁
  have hr := hp.1
  simp [radiusSq₁, h₀, h₁] at hr

/-- Nonstationary periodic points of the changed ODE inside A. -/
def frequencyPeriodicSet (c ν : ℝ) : Set PhaseSpace :=
  {p | p ∈ attractor ∧ frequencyVectorField c ν p ≠ 0 ∧
    ∃ t : ℝ, 0 < t ∧ frequencyEvolution c ν t p = p}

theorem torus_subset_frequencyPeriodicSet (c : ℝ) (ν : ℚ) :
    torus ⊆ frequencyPeriodicSet c (ν : ℝ) := by
  intro p hp
  refine ⟨torus_subset_attractor hp, frequency_torus_not_equilibrium c ν hp,
    2 * Real.pi * ν.den, (rational_frequency_torus_period c ν hp).1, ?_⟩
  exact frequency_torus_common_return c ν.pos (Rat.cast_def ν) hp

/-- The limiting dimension maximum is attained among nonstationary periodic points. -/
theorem frequency_periodic_asymptotic_isGreatest {c : ℝ} (hc : 4 < c) (ν : ℚ) :
    IsGreatest (frequencyAsymptoticDimension c ν '' frequencyPeriodicSet c ν)
      (targetDimension c) := by
  constructor
  · obtain ⟨p, hp⟩ := torus_nonempty
    exact ⟨p, torus_subset_frequencyPeriodicSet c ν hp,
      (frequencyAsymptoticDimension_bound_and_eq hc ν (torus_subset_attractor hp)).2.mpr hp⟩
  · rintro d ⟨p, hp, rfl⟩
    exact (frequencyAsymptoticDimension_bound_and_eq hc ν hp.1).1

/-- The finite-time maximum is likewise attained on periodic points at every
positive time. -/
theorem frequency_periodic_finiteTime_isGreatest {c t : ℝ} (hc : 4 < c)
    (ν : ℚ) (ht : 0 < t) :
    IsGreatest (frequencyFiniteTimeDimension c ν t '' frequencyPeriodicSet c ν)
      (targetDimension c) := by
  constructor
  · obtain ⟨p, hp⟩ := torus_nonempty
    exact ⟨p, torus_subset_frequencyPeriodicSet c ν hp,
      (frequencyFiniteTimeDimension_bound_and_eq hc ν ht (torus_subset_attractor hp)).2.mpr hp⟩
  · rintro d ⟨p, hp, rfl⟩
    exact (frequencyFiniteTimeDimension_bound_and_eq hc ν ht hp.1).1

/-- Positive rational frequencies exist arbitrarily close to sqrt2. -/
theorem exists_positive_rational_frequency {ε : ℝ} (hε : 0 < ε) :
    ∃ ν : ℚ, 0 < ν ∧ |(ν : ℝ) - Real.sqrt 2| < ε := by
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  obtain ⟨ν, hν₀, hν₁⟩ := exists_rat_btwn
    (show max 0 (Real.sqrt 2 - ε) < Real.sqrt 2 + ε by
      exact max_lt (by linarith) (by linarith))
  refine ⟨ν, ?_, ?_⟩
  · exact_mod_cast (lt_of_le_of_lt (le_max_left 0 _) hν₀)
  · rw [abs_lt]
    constructor <;> linarith [le_max_right 0 (Real.sqrt 2 - ε)]

/-- Arbitrarily small positive-rational frequency changes restore periodic
attainment. -/
theorem exists_nearby_frequency_periodic_maximum {c ε : ℝ} (hc : 4 < c) (hε : 0 < ε) :
    ∃ ν : ℚ, 0 < ν ∧ |(ν : ℝ) - Real.sqrt 2| < ε ∧
      IsGreatest (frequencyAsymptoticDimension c ν '' frequencyPeriodicSet c ν)
        (targetDimension c) ∧
      ∀ t : ℝ, 0 < t →
        IsGreatest (frequencyFiniteTimeDimension c ν t '' frequencyPeriodicSet c ν)
          (targetDimension c) := by
  obtain ⟨ν, hν, hclose⟩ := exists_positive_rational_frequency hε
  exact ⟨ν, hν, hclose, frequency_periodic_asymptotic_isGreatest hc ν,
    fun _ ht => frequency_periodic_finiteTime_isGreatest hc ν ht⟩

end Eden
