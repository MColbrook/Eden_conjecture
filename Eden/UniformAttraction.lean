import Eden.PhysicalRadius
import Eden.AttractorDistance
import Eden.StrictInvariance

/-!
# Uniform attraction of every bounded ambient set

The estimate is the manuscript's common-radius bound, with the exact Euclidean
squared distance and exponential fifth-coordinate term. Attraction is expressed
by the existence of nearby points in the target set. Minimality uses strict
invariance and closedness, through Mathlib's distance-to-set characterisation of
closure.
-/

noncomputable section
open Set Filter
open scoped Topology
namespace Eden

/-- Common squared-distance bound when both initial radii are at most `M ≥ sqrt(2)`,
the initial fifth coordinate has absolute value at most `W`, and `t ≥ 0`. It
tends to zero for `c > 0` and `M > sqrt(2)`. -/
def attractionBound (c M W t : ℝ) : ℝ :=
  2 * (radiusEvolution t M - Real.sqrt 2) ^ 2 + W ^ 2 * Real.exp (-2 * c * t)

theorem radial_excess_le {t r M : ℝ} (ht : 0 ≤ t) (hr : 0 ≤ r)
    (hrM : r ≤ M) (hM : Real.sqrt 2 ≤ M) :
    max (radiusEvolution t r - Real.sqrt 2) 0 ≤ radiusEvolution t M - Real.sqrt 2 := by
  apply max_le
  · linarith [radiusEvolution_mono ht hr hrM]
  · linarith [radiusEvolution_ge_sqrt_two ht hM]

theorem dist_projection_evolution_sq_le (c : ℝ) {M W t : ℝ} (ht : 0 ≤ t)
    (hM : Real.sqrt 2 ≤ M) {p : PhaseSpace}
    (h₁ : Real.sqrt (radiusSq₁ p) ≤ M) (h₂ : Real.sqrt (radiusSq₂ p) ≤ M)
    (hw : |p 4| ≤ W) :
    dist (evolution c t p) (attractorProjection (evolution c t p)) ^ 2 ≤
      attractionBound c M W t := by
  rw [dist_attractorProjection_sq, radius₁_evolution c ht, radius₂_evolution c ht]
  have hb₁ := radial_excess_le ht (Real.sqrt_nonneg _) h₁ hM
  have hb₂ := radial_excess_le ht (Real.sqrt_nonneg _) h₂ hM
  have hb₀ : 0 ≤ radiusEvolution t M - Real.sqrt 2 := by
    linarith [radiusEvolution_ge_sqrt_two ht hM]
  have he : (Real.exp (-c * t)) ^ 2 = Real.exp (-2 * c * t) := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have hw₂ : p 4 ^ 2 ≤ W ^ 2 := by nlinarith [sq_abs (p 4), abs_nonneg (p 4)]
  have hwbound := mul_le_mul_of_nonneg_left hw₂ (Real.exp_pos (-2 * c * t)).le
  have hwformula : evolution c t p 4 ^ 2 = Real.exp (-2 * c * t) * p 4 ^ 2 := by
    change (Real.exp (-c * t) * p 4) ^ 2 = _
    rw [mul_pow, he]
  rw [hwformula]
  unfold attractionBound
  nlinarith [le_max_right (radiusEvolution t (Real.sqrt (radiusSq₁ p)) - Real.sqrt 2) 0,
    le_max_right (radiusEvolution t (Real.sqrt (radiusSq₂ p)) - Real.sqrt 2) 0]

theorem infDist_evolution_attractor_sq_le (c : ℝ) {M W t : ℝ} (ht : 0 ≤ t)
    (hM : Real.sqrt 2 ≤ M) {p : PhaseSpace}
    (h₁ : Real.sqrt (radiusSq₁ p) ≤ M) (h₂ : Real.sqrt (radiusSq₂ p) ≤ M)
    (hw : |p 4| ≤ W) :
    Metric.infDist (evolution c t p) attractor ^ 2 ≤ attractionBound c M W t := by
  have hd := Metric.infDist_le_dist_of_mem (x := evolution c t p)
    (attractorProjection_mem (evolution c t p))
  have hn : 0 ≤ Metric.infDist (evolution c t p) attractor := Metric.infDist_nonneg
  have hb := dist_projection_evolution_sq_le c ht hM h₁ h₂ hw
  nlinarith

theorem tendsto_attractionBound {c M : ℝ} (hc : 0 < c) (hM : Real.sqrt 2 < M) (W : ℝ) :
    Tendsto (fun t => attractionBound c M W t) atTop (𝓝 0) := by
  have hM₁ : 1 < M := by
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    have hn := Real.sqrt_nonneg (2 : ℝ)
    nlinarith
  have hr := ((tendsto_radiusEvolution_of_one_lt hM₁).sub_const (Real.sqrt 2)).pow 2
  have he := Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (tendsto_id.const_mul_atTop (show 0 < 2 * c by positivity))
  have he' : Tendsto (fun t : ℝ => Real.exp (-2 * c * t)) atTop (𝓝 0) := by
    convert he using 1
    simp [Function.comp_def, neg_mul, mul_assoc]
  have h := (hr.const_mul 2).add (he'.const_mul (W ^ 2))
  simpa only [attractionBound, sub_self, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero] using h

theorem radius₁_le_norm (p : PhaseSpace) : Real.sqrt (radiusSq₁ p) ≤ ‖p‖ := by
  have hn := norm_sq_phaseSpace p
  have hs := Real.sq_sqrt (radiusSq₁_nonneg p)
  nlinarith [radiusSq₂_nonneg p, sq_nonneg (p 4), norm_nonneg p, Real.sqrt_nonneg (radiusSq₁ p)]

theorem radius₂_le_norm (p : PhaseSpace) : Real.sqrt (radiusSq₂ p) ≤ ‖p‖ := by
  have hn := norm_sq_phaseSpace p
  have hs := Real.sq_sqrt (radiusSq₂_nonneg p)
  nlinarith [radiusSq₁_nonneg p, sq_nonneg (p 4), norm_nonneg p, Real.sqrt_nonneg (radiusSq₂ p)]

theorem bounded_set_radius_bounds {B : Set PhaseSpace} (hB : Bornology.IsBounded B) :
    ∃ M W : ℝ, Real.sqrt 2 < M ∧ 0 ≤ W ∧ ∀ p ∈ B,
      Real.sqrt (radiusSq₁ p) ≤ M ∧ Real.sqrt (radiusSq₂ p) ≤ M ∧ |p 4| ≤ W := by
  obtain ⟨C, hC⟩ := hB.exists_norm_le
  refine ⟨|C| + Real.sqrt 2 + 1, |C|, by linarith [abs_nonneg C], abs_nonneg C, ?_⟩
  intro p hp
  have hCp := (hC p hp).trans (le_abs_self C)
  have hw : |p 4| ≤ ‖p‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le p 4
  refine ⟨?_, ?_, hw.trans hCp⟩
  · linarith [radius₁_le_norm p, Real.sqrt_nonneg (2 : ℝ)]
  · linarith [radius₂_le_norm p, Real.sqrt_nonneg (2 : ℝ)]

/-- Uniform attraction of bounded sets through nearby points in the target set. -/
def UniformlyAttractsBounded (c : ℝ) (C : Set PhaseSpace) : Prop :=
  ∀ B : Set PhaseSpace, Bornology.IsBounded B → ∀ ε : ℝ, 0 < ε →
    ∃ T : ℝ, 0 ≤ T ∧ ∀ t : ℝ, T ≤ t → ∀ p ∈ B,
      ∃ q ∈ C, dist (evolution c t p) q < ε

theorem attractor_uniformlyAttractsBounded {c : ℝ} (hc : 0 < c) :
    UniformlyAttractsBounded c attractor := by
  intro B hB ε hε
  obtain ⟨M, W, hM, _, hMW⟩ := bounded_set_radius_bounds hB
  have hevent := (tendsto_attractionBound hc hM W).eventually
    (Iio_mem_nhds (sq_pos_of_pos hε))
  obtain ⟨T, hT⟩ := eventually_atTop.1 hevent
  refine ⟨max T 0, le_max_right _ _, ?_⟩
  intro t ht p hp
  have ht₀ : 0 ≤ t := (le_max_right _ _).trans ht
  have htT : T ≤ t := (le_max_left _ _).trans ht
  obtain ⟨h₁, h₂, hw⟩ := hMW p hp
  refine ⟨attractorProjection (evolution c t p), attractorProjection_mem _, ?_⟩
  have hbound := dist_projection_evolution_sq_le c ht₀ hM.le h₁ h₂ hw
  have hsmall := hT t htT
  change attractionBound c M W t < ε ^ 2 at hsmall
  nlinarith [dist_nonneg (x := evolution c t p) (y := attractorProjection (evolution c t p))]

theorem uniformlyAttractsBounded_nonempty {c : ℝ} {C : Set PhaseSpace}
    (hC : UniformlyAttractsBounded c C) : C.Nonempty := by
  obtain ⟨T, _, hT⟩ := hC {0} (isCompact_singleton.isBounded) 1 (by norm_num)
  obtain ⟨q, hq, _⟩ := hT T le_rfl 0 (by simp)
  exact ⟨q, hq⟩

theorem attractor_subset_of_uniformlyAttractsBounded {c : ℝ} {C : Set PhaseSpace}
    (hclosed : IsClosed C) (hC : UniformlyAttractsBounded c C) : attractor ⊆ C := by
  intro p hp
  apply (hclosed.mem_iff_infDist_zero (uniformlyAttractsBounded_nonempty hC)).2
  apply le_antisymm _ Metric.infDist_nonneg
  apply le_of_forall_pos_lt_add
  intro ε hε
  obtain ⟨T, hT₀, hT⟩ := hC attractor isCompact_attractor.isBounded ε hε
  obtain ⟨q, hq, hqp⟩ := evolution_surjOn_attractor c hT₀ hp
  obtain ⟨r, hr, hpr⟩ := hT T le_rfl q hq
  rw [hqp] at hpr
  simpa only [zero_add] using (Metric.infDist_le_dist_of_mem hr).trans_lt hpr

/-- A compact global attractor for the evolution, with all real forward times. -/
def IsGlobalAttractor (c : ℝ) (K : Set PhaseSpace) : Prop :=
  K.Nonempty ∧ IsCompact K ∧ (∀ t : ℝ, 0 ≤ t → evolution c t '' K = K) ∧
    UniformlyAttractsBounded c K

/-- The product of discs is the compact global attractor for every `c > 0`. -/
theorem attractor_isGlobalAttractor {c : ℝ} (hc : 0 < c) : IsGlobalAttractor c attractor :=
  ⟨attractor_nonempty, isCompact_attractor, (fun _ ht => evolution_image_attractor c ht),
    attractor_uniformlyAttractsBounded hc⟩

theorem attractor_minimal {c : ℝ} {C : Set PhaseSpace} (hcompact : IsCompact C)
    (hC : UniformlyAttractsBounded c C) : attractor ⊆ C :=
  attractor_subset_of_uniformlyAttractsBounded hcompact.isClosed hC

theorem empty_not_uniformlyAttractsBounded (c : ℝ) :
    ¬UniformlyAttractsBounded c (∅ : Set PhaseSpace) := by
  intro h
  exact Set.not_nonempty_empty (uniformlyAttractsBounded_nonempty h)

end Eden
