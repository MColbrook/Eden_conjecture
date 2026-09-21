import Eden.PeriodicOrbits
import Eden.StrictInvariance

/-!
# Invariant radial regions and failure of transitivity

The two relatively open regions in the attractor are defined by inequalities for
the first squared radius. Strict invariance follows from surjectivity on A and
preservation of the radial threshold. Closed half-regions exclude dense orbits,
including those starting at the intervening unit-radius level.

Closure arguments use Mathlib's topology library, whose Closure module credits
Johannes Hoelzl, Mario Carneiro and Jeremy Avigad.
-/

noncomputable section
open Set
namespace Eden

/-- The region in A with first ordinary radius less than one. -/
def innerRadialRegion : Set PhaseSpace := {p | p ∈ attractor ∧ radiusSq₁ p < 1}

/-- The region in A with first ordinary radius greater than one. -/
def outerRadialRegion : Set PhaseSpace := {p | p ∈ attractor ∧ 1 < radiusSq₁ p}

/-- The intervening unit-radius level in A. -/
def unitRadialLevel : Set PhaseSpace := {p | p ∈ attractor ∧ radiusSq₁ p = 1}

theorem mem_innerRadialRegion_iff_radius (p : PhaseSpace) :
    p ∈ innerRadialRegion ↔ p ∈ attractor ∧ Real.sqrt (radiusSq₁ p) < 1 := by
  simp [innerRadialRegion, Real.sqrt_lt (radiusSq₁_nonneg p) (show (0 : ℝ) ≤ 1 by norm_num)]

theorem mem_outerRadialRegion_iff_radius (p : PhaseSpace) :
    p ∈ outerRadialRegion ↔ p ∈ attractor ∧ 1 < Real.sqrt (radiusSq₁ p) := by
  simp [outerRadialRegion, Real.lt_sqrt (show (0 : ℝ) ≤ 1 by norm_num)]

theorem mem_unitRadialLevel_iff_radius (p : PhaseSpace) :
    p ∈ unitRadialLevel ↔ p ∈ attractor ∧ Real.sqrt (radiusSq₁ p) = 1 := by
  simp [unitRadialLevel]

theorem innerRadialRegion_nonempty : innerRadialRegion.Nonempty := by
  refine ⟨0, ?_⟩
  norm_num [innerRadialRegion, attractor, radiusSq₁, radiusSq₂]

theorem outerRadialRegion_nonempty : outerRadialRegion.Nonempty := by
  obtain ⟨p, hp⟩ := firstCircle_nonempty (show (0 : ℝ) ≤ 2 by norm_num)
  refine ⟨p, ⟨?_, ?_⟩⟩
  · exact ⟨hp.1.le, by rw [hp.2.1]; norm_num, hp.2.2⟩
  · rw [hp.1]; norm_num

theorem radialRegions_disjoint : Disjoint innerRadialRegion outerRadialRegion := by
  rw [Set.disjoint_left]
  intro p hp hq
  exact (not_lt_of_ge hp.2.le) hq.2

/-- Openness is in the subspace topology of the attractor. -/
theorem isOpen_innerRadialRegion :
    IsOpen {p : attractor | (p : PhaseSpace) ∈ innerRadialRegion} := by
  have h : IsOpen {p : attractor | radiusSq₁ p.val < 1} :=
    isOpen_lt (continuous_radiusSq₁.comp continuous_subtype_val) continuous_const
  simpa [innerRadialRegion] using h

theorem isOpen_outerRadialRegion :
    IsOpen {p : attractor | (p : PhaseSpace) ∈ outerRadialRegion} := by
  have h : IsOpen {p : attractor | 1 < radiusSq₁ p.val} :=
    isOpen_lt continuous_const (continuous_radiusSq₁.comp continuous_subtype_val)
  simpa [outerRadialRegion] using h

theorem radiusSq₁_evolution_lt_one_iff (c : ℝ) {t : ℝ} (ht : 0 ≤ t) (p : PhaseSpace) :
    radiusSq₁ (evolution c t p) < 1 ↔ radiusSq₁ p < 1 := by
  rw [radiusSq₁_evolution c ht, squaredRadiusEvolution_lt_one_iff ht]

theorem one_lt_radiusSq₁_evolution_iff (c : ℝ) {t : ℝ} (ht : 0 ≤ t) (p : PhaseSpace) :
    1 < radiusSq₁ (evolution c t p) ↔ 1 < radiusSq₁ p := by
  rw [radiusSq₁_evolution c ht, one_lt_squaredRadiusEvolution_iff ht]

theorem radiusSq₁_evolution_eq_one_iff (c : ℝ) {t : ℝ} (ht : 0 ≤ t) (p : PhaseSpace) :
    radiusSq₁ (evolution c t p) = 1 ↔ radiusSq₁ p = 1 := by
  rw [radiusSq₁_evolution c ht]
  simpa using (strictMono_squaredRadiusEvolution ht).injective.eq_iff
    (a := radiusSq₁ p) (b := 1)

private theorem evolution_image_radialRegion (c : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (P : PhaseSpace → Prop) (hP : ∀ p, P (evolution c t p) ↔ P p) :
    evolution c t '' {p | p ∈ attractor ∧ P p} = {p | p ∈ attractor ∧ P p} := by
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨evolution_mem_attractor c ht hp.1, (hP p).mpr hp.2⟩
  · intro hq
    obtain ⟨p, hp, he⟩ := evolution_surjOn_attractor c ht hq.1
    refine ⟨p, ⟨hp, ?_⟩, he⟩
    exact (hP p).mp (he ▸ hq.2)

theorem evolution_image_innerRadialRegion (c : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    evolution c t '' innerRadialRegion = innerRadialRegion :=
  evolution_image_radialRegion c ht _ (radiusSq₁_evolution_lt_one_iff c ht)

theorem evolution_image_outerRadialRegion (c : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    evolution c t '' outerRadialRegion = outerRadialRegion :=
  evolution_image_radialRegion c ht _ (one_lt_radiusSq₁_evolution_iff c ht)

theorem evolution_image_unitRadialLevel (c : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    evolution c t '' unitRadialLevel = unitRadialLevel :=
  evolution_image_radialRegion c ht _ (radiusSq₁_evolution_eq_one_iff c ht)

theorem evolution_inner_disjoint_outer (c : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    Disjoint (evolution c t '' innerRadialRegion) outerRadialRegion := by
  rw [evolution_image_innerRadialRegion c ht]
  exact radialRegions_disjoint

/-- No forward orbit can have the whole attractor in its closure. The statement also
permits ambient initial points outside A. -/
theorem attractor_not_subset_closure_forwardOrbit (c : ℝ) (p : PhaseSpace) :
    ¬ attractor ⊆ closure (forwardOrbit c p) := by
  intro hd
  by_cases hp : radiusSq₁ p ≤ 1
  · have hcl : closure (forwardOrbit c p) ⊆ {q | radiusSq₁ q ≤ 1} := by
      apply closure_minimal _ (isClosed_le continuous_radiusSq₁ continuous_const)
      rintro q ⟨t, ht, rfl⟩
      change radiusSq₁ (evolution c t p) ≤ 1
      by_contra h
      exact (not_lt_of_ge hp) ((one_lt_radiusSq₁_evolution_iff c ht p).mp (lt_of_not_ge h))
    obtain ⟨q, hq⟩ := outerRadialRegion_nonempty
    exact (not_lt_of_ge (hcl (hd hq.1))) hq.2
  · have hcl : closure (forwardOrbit c p) ⊆ {q | 1 ≤ radiusSq₁ q} := by
      apply closure_minimal _ (isClosed_le continuous_const continuous_radiusSq₁)
      rintro q ⟨t, ht, rfl⟩
      exact ((one_lt_radiusSq₁_evolution_iff c ht p).mpr (lt_of_not_ge hp)).le
    obtain ⟨q, hq⟩ := innerRadialRegion_nonempty
    exact (not_lt_of_ge (hcl (hd hq.1))) hq.2

/-- Evolution restricted to A, with its subspace topology. -/
def attractorEvolution (c : ℝ) {t : ℝ} (ht : 0 ≤ t) (p : attractor) : attractor :=
  ⟨evolution c t p.val, evolution_mem_attractor c ht p.property⟩

/-- Failure of the open-set formulation of topological transitivity, with all
nonnegative real times allowed. -/
theorem not_openSet_transitive_attractor (c : ℝ) :
    ¬ (∀ U V : Set attractor, IsOpen U → IsOpen V → U.Nonempty → V.Nonempty →
      ∃ (t : ℝ) (ht : 0 ≤ t) (p : attractor), p ∈ U ∧ attractorEvolution c ht p ∈ V) := by
  intro htrans
  obtain ⟨p, hp⟩ := innerRadialRegion_nonempty
  obtain ⟨q, hq⟩ := outerRadialRegion_nonempty
  obtain ⟨t, ht, r, hr, hs⟩ := htrans
    {p : attractor | (p : PhaseSpace) ∈ innerRadialRegion}
    {p : attractor | (p : PhaseSpace) ∈ outerRadialRegion}
    isOpen_innerRadialRegion isOpen_outerRadialRegion
    ⟨⟨p, hp.1⟩, hp⟩ ⟨⟨q, hq.1⟩, hq⟩
  have hlt : radiusSq₁ r.val < 1 := hr.2
  have hgt : 1 < radiusSq₁ (evolution c t r.val) := hs.2
  exact (not_lt_of_ge hlt.le) ((one_lt_radiusSq₁_evolution_iff c ht r.val).mp hgt)

end Eden
