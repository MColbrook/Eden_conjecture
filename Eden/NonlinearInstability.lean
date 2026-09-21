import Eden.InstabilityGeometry

/-!
# Nonlinear instability of the unit circles and torus

An inward radial perturbation converges to radius zero and consequently reaches
distance at least 1/2 from the unit-radius set. The initial point can be
arbitrarily close and always belongs to A. Distance to a set and its lower-bound
characterization are from Mathlib's HausdorffDistance library, by Sébastien
Gouëzel.
-/

noncomputable section
open Set Filter Topology
namespace Eden

/-- Set instability with perturbations restricted to B and nonnegative real time. -/
def UnstableRelativeTo (c : ℝ) (B K : Set PhaseSpace) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 < δ →
    ∃ p ∈ B, Metric.infDist p K < δ ∧
      ∃ t : ℝ, 0 ≤ t ∧ ε ≤ Metric.infDist (evolution c t p) K

/-- A set of unit planar radius is unstable if it contains the indicated radial
endpoint. -/
theorem unstableRelativeTo_of_unit_plane_in (c : ℝ) (j : Fin 2) {B K : Set PhaseSpace}
    {s : ℝ} (hB : ∀ r ∈ Icc (0 : ℝ) 1, radialPerturbation j r s ∈ B)
    (hend : radialPerturbation j 1 s ∈ K)
    (hunit : ∀ q ∈ K, ‖planeProjection j q‖ = 1) :
    UnstableRelativeTo c B K := by
  refine ⟨1 / 2, by norm_num, ?_⟩
  intro δ hδ
  let η : ℝ := min (δ / 2) (1 / 2)
  have hη : 0 < η := lt_min (by positivity) (by norm_num)
  have hηhalf : η ≤ 1 / 2 := min_le_right _ _
  have hηδ : η < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  let r : ℝ := 1 - η
  have hr : 0 ≤ r := by dsimp [r]; linarith
  have hr₁ : r < 1 := by dsimp [r]; linarith
  refine ⟨radialPerturbation j r s,
    hB r ⟨hr, hr₁.le⟩, ?_, ?_⟩
  · have hd : dist (radialPerturbation j r s) (radialPerturbation j 1 s) = η := by
      rw [dist_radialPerturbation, abs_of_nonpos (by linarith : r - 1 ≤ 0)]
      dsimp [r]
      ring
    exact (Metric.infDist_le_dist_of_mem hend).trans_lt (hd.trans_lt hηδ)
  · have hsmall : ∀ᶠ t : ℝ in atTop, radiusEvolution t r < 1 / 2 :=
      (tendsto_radiusEvolution_of_lt_one hr hr₁).eventually
        (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
    obtain ⟨t, ht, htr⟩ := ((eventually_ge_atTop (0 : ℝ)).and hsmall).exists
    refine ⟨t, ht, ?_⟩
    have hdist := one_sub_plane_radius_le_infDist j ⟨_, hend⟩ hunit
      (evolution c t (radialPerturbation j r s))
    rw [plane_radius_evolution_radialPerturbation c j ht hr] at hdist
    linarith

theorem unstableRelativeTo_of_unit_plane (c : ℝ) (j : Fin 2) {K : Set PhaseSpace}
    {s : ℝ} (hs : s ∈ Icc 0 1) (hend : radialPerturbation j 1 s ∈ K)
    (hunit : ∀ q ∈ K, ‖planeProjection j q‖ = 1) :
    UnstableRelativeTo c attractor K :=
  unstableRelativeTo_of_unit_plane_in c j
    (fun _ hr => radialPerturbation_mem_attractor j hr hs) hend hunit

/-- The coordinate plane, with the other planar block and w equal to zero. -/
def coordinatePlane (j : Fin 2) : Set PhaseSpace :=
  {p | (if j = 0 then radiusSq₂ p else radiusSq₁ p) = 0 ∧ p 4 = 0}

theorem radialPerturbation_mem_coordinatePlane (j : Fin 2) (r : ℝ) :
    radialPerturbation j r 0 ∈ coordinatePlane j := by
  fin_cases j <;> simp [radialPerturbation, coordinatePlane, radiusSq₁, radiusSq₂]

/-- Instability of the first circle with perturbations in its own planar subsystem. -/
theorem firstCircle_unstableInPlane (c : ℝ) :
    UnstableRelativeTo c (attractor ∩ coordinatePlane 0) (firstCircle 1) := by
  apply unstableRelativeTo_of_unit_plane_in c 0 (s := 0)
  · intro r hr
    exact ⟨radialPerturbation_mem_attractor 0 hr (by norm_num),
      radialPerturbation_mem_coordinatePlane 0 r⟩
  · simp [radialPerturbation, firstCircle, radiusSq₁, radiusSq₂]
  · intro q hq
    simp [norm_planeProjection, hq.1]

/-- Instability of the second circle with perturbations in its own planar subsystem. -/
theorem secondCircle_unstableInPlane (c : ℝ) :
    UnstableRelativeTo c (attractor ∩ coordinatePlane 1) (secondCircle 1) := by
  apply unstableRelativeTo_of_unit_plane_in c 1 (s := 0)
  · intro r hr
    exact ⟨radialPerturbation_mem_attractor 1 hr (by norm_num),
      radialPerturbation_mem_coordinatePlane 1 r⟩
  · simp [radialPerturbation, secondCircle, radiusSq₁, radiusSq₂]
  · intro q hq
    simp [norm_planeProjection, hq.2.1]

/-- The first planar unit circle is nonlinearly unstable, even relative to A. -/
theorem firstCircle_unstableRelativeTo (c : ℝ) :
    UnstableRelativeTo c attractor (firstCircle 1) := by
  apply unstableRelativeTo_of_unit_plane c 0 (s := 0) (by norm_num)
  · simp [radialPerturbation, firstCircle, radiusSq₁, radiusSq₂]
  · intro q hq
    rw [norm_planeProjection]
    simp only [ite_true, hq.1, Real.sqrt_one]

/-- The second planar unit circle is nonlinearly unstable, even relative to A. -/
theorem secondCircle_unstableRelativeTo (c : ℝ) :
    UnstableRelativeTo c attractor (secondCircle 1) := by
  apply unstableRelativeTo_of_unit_plane c 1 (s := 0) (by norm_num)
  · simp [radialPerturbation, secondCircle, radiusSq₁, radiusSq₂]
  · intro q hq
    rw [norm_planeProjection]
    simp only [show (1 : Fin 2) ≠ 0 by decide, ite_false, hq.2.1, Real.sqrt_one]

/-- The maximising torus is nonlinearly unstable within the attractor. -/
theorem torus_unstableRelativeTo (c : ℝ) : UnstableRelativeTo c attractor torus := by
  apply unstableRelativeTo_of_unit_plane c 0 (s := 1) (by norm_num)
  · simp [radialPerturbation, torus, radiusSq₁, radiusSq₂]
  · intro q hq
    rw [norm_planeProjection]
    simp only [ite_true, hq.1, Real.sqrt_one]

theorem unstableRelativeTo_mono (c : ℝ) {B C K : Set PhaseSpace}
    (hBC : B ⊆ C) (h : UnstableRelativeTo c B K) : UnstableRelativeTo c C K := by
  obtain ⟨ε, hε, h⟩ := h
  refine ⟨ε, hε, fun δ hδ => ?_⟩
  obtain ⟨p, hp, hclose, t, ht, hfar⟩ := h δ hδ
  exact ⟨p, hBC hp, hclose, t, ht, hfar⟩

/-- Strict invariance of the stationary-radius sets used in the instability
statements. -/
theorem evolution_image_stationary_radii (c : ℝ) {t a b : ℝ} (ht : 0 ≤ t)
    (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) :
    evolution c t '' {p | radiusSq₁ p = a ∧ radiusSq₂ p = b ∧ p 4 = 0} =
      {p | radiusSq₁ p = a ∧ radiusSq₂ p = b ∧ p 4 = 0} := by
  have hSa : squaredRadiusEvolution t a = a := by rcases ha with rfl | rfl <;> simp
  have hSb : squaredRadiusEvolution t b = b := by rcases hb with rfl | rfl <;> simp
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [radiusSq₁_evolution c ht, hp.1, hSa]
    · rw [radiusSq₂_evolution c ht, hp.2.1, hSb]
    · simp [evolution, hp.2.2]
  · intro hq
    have hqA : q ∈ attractor := by
      refine ⟨?_, ?_, hq.2.2⟩
      · rw [hq.1]; rcases ha with rfl | rfl <;> norm_num
      · rw [hq.2.1]; rcases hb with rfl | rfl <;> norm_num
    obtain ⟨p, hp, he⟩ := evolution_surjOn_attractor c ht hqA
    refine ⟨p, ⟨?_, ?_, hp.2.2⟩, he⟩
    · apply (strictMono_squaredRadiusEvolution ht).injective
      rw [hSa, ← radiusSq₁_evolution c ht, he, hq.1]
    · apply (strictMono_squaredRadiusEvolution ht).injective
      rw [hSb, ← radiusSq₂_evolution c ht, he, hq.2.1]

/-- All three invariant sets are strictly invariant and unstable relative to A. -/
theorem unit_sets_invariant_and_unstable (c : ℝ)
    {K : Set PhaseSpace} (hK : K = firstCircle 1 ∨ K = secondCircle 1 ∨ K = torus) :
    (∀ t : ℝ, 0 ≤ t → evolution c t '' K = K) ∧
      UnstableRelativeTo c attractor K ∧ UnstableRelativeTo c univ K := by
  have hu : UnstableRelativeTo c attractor K := by
    rcases hK with rfl | rfl | rfl
    · exact firstCircle_unstableRelativeTo c
    · exact secondCircle_unstableRelativeTo c
    · exact torus_unstableRelativeTo c
  refine ⟨?_, hu, unstableRelativeTo_mono c (subset_univ _) hu⟩
  intro t ht
  rcases hK with rfl | rfl | rfl
  · exact evolution_image_stationary_radii c ht (Or.inr rfl) (Or.inl rfl)
  · exact evolution_image_stationary_radii c ht (Or.inl rfl) (Or.inr rfl)
  · exact evolution_image_stationary_radii c ht (Or.inr rfl) (Or.inr rfl)

end Eden
