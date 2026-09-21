import Eden.FrequencyRotation
import Eden.UniformAttraction
import Eden.TorusAngles

/-!
# The global attractor in the frequency family

The additional ambient rotation preserves A, T and Euclidean distances.
Uniform attraction holds for every bounded set. Strict invariance and
attraction imply minimality.
-/

noncomputable section
open Set
namespace Eden

theorem frequencyEvolution_image_attractor (c ν : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    frequencyEvolution c ν t '' attractor = attractor := by
  have he : frequencyEvolution c ν t = (frequencyCorrection ν t) ∘ evolution c t :=
    funext (frequencyEvolution_eq_correction c ν t)
  rw [he, Set.image_comp, evolution_image_attractor c ht, frequencyCorrection_image_attractor]

theorem frequencyEvolution_mem_torus (c ν t : ℝ) {p : PhaseSpace} (hp : p ∈ torus) :
    frequencyEvolution c ν t p ∈ torus := by
  rw [frequencyEvolution_eq_correction, frequencyCorrection_mem_torus_iff]
  exact torus_invariant_all_real c t hp

/-- Uniform bounded-set attraction for the frequency-dependent evolution. -/
def FrequencyUniformlyAttractsBounded (c ν : ℝ) (C : Set PhaseSpace) : Prop :=
  ∀ B : Set PhaseSpace, Bornology.IsBounded B → ∀ ε : ℝ, 0 < ε →
    ∃ T : ℝ, 0 ≤ T ∧ ∀ t : ℝ, T ≤ t → ∀ p ∈ B,
      ∃ q ∈ C, dist (frequencyEvolution c ν t p) q < ε

theorem attractor_frequencyUniformlyAttractsBounded {c : ℝ} (hc : 0 < c) (ν : ℝ) :
    FrequencyUniformlyAttractsBounded c ν attractor := by
  intro B hB ε hε
  obtain ⟨T, hT₀, hT⟩ := attractor_uniformlyAttractsBounded hc B hB ε hε
  refine ⟨T, hT₀, ?_⟩
  intro t ht p hp
  obtain ⟨q, hq, hd⟩ := hT t ht p hp
  refine ⟨frequencyCorrection ν t q, (frequencyCorrection_mem_attractor_iff ν t q).2 hq, ?_⟩
  rw [frequencyEvolution_eq_correction, (frequencyCorrection ν t).dist_map]
  exact hd

/-- The compact global-attractor property for the changed ODE. -/
def IsFrequencyGlobalAttractor (c ν : ℝ) (K : Set PhaseSpace) : Prop :=
  K.Nonempty ∧ IsCompact K ∧ (∀ t : ℝ, 0 ≤ t → frequencyEvolution c ν t '' K = K) ∧
    FrequencyUniformlyAttractsBounded c ν K

/-- A is the compact global attractor for every real frequency and c>0. -/
theorem attractor_isFrequencyGlobalAttractor {c : ℝ} (hc : 0 < c) (ν : ℝ) :
    IsFrequencyGlobalAttractor c ν attractor :=
  ⟨attractor_nonempty, isCompact_attractor, fun _ ht => frequencyEvolution_image_attractor c ν ht,
    attractor_frequencyUniformlyAttractsBounded hc ν⟩

theorem frequencyUniformlyAttractsBounded_nonempty {c ν : ℝ} {C : Set PhaseSpace}
    (hC : FrequencyUniformlyAttractsBounded c ν C) : C.Nonempty := by
  obtain ⟨T, _, hT⟩ := hC {0} isCompact_singleton.isBounded 1 (by norm_num)
  obtain ⟨q, hq, _⟩ := hT T le_rfl 0 (by simp)
  exact ⟨q, hq⟩

/-- The attractor is contained in every closed set uniformly attracting bounded sets. -/
theorem frequency_attractor_minimal {c ν : ℝ} {C : Set PhaseSpace}
    (hclosed : IsClosed C) (hC : FrequencyUniformlyAttractsBounded c ν C) : attractor ⊆ C := by
  intro p hp
  apply (hclosed.mem_iff_infDist_zero (frequencyUniformlyAttractsBounded_nonempty hC)).2
  apply le_antisymm _ Metric.infDist_nonneg
  apply le_of_forall_pos_lt_add
  intro ε hε
  obtain ⟨T, hT₀, hT⟩ := hC attractor isCompact_attractor.isBounded ε hε
  have himage := frequencyEvolution_image_attractor c ν hT₀
  obtain ⟨q, hq, hqp⟩ := (show p ∈ frequencyEvolution c ν T '' attractor by rw [himage]; exact hp)
  obtain ⟨r, hr, hpr⟩ := hT T le_rfl q hq
  rw [hqp] at hpr
  simpa only [zero_add] using (Metric.infDist_le_dist_of_mem hr).trans_lt hpr

end Eden
