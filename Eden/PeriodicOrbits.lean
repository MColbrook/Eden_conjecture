import Eden.CircleOrbits
import Mathlib.Data.Set.Card

/-!
# Exactly four nonconstant geometric periodic orbits

The orbit collection consists of forward-orbit sets through returning points
that are not equilibria. Its four members are nonempty and distinct.
-/

noncomputable section
open Set
namespace Eden

/-- The geometric orbits of nonconstant periodic solutions. -/
def geometricPeriodicOrbits (c : ℝ) : Set (Set PhaseSpace) :=
  {O | ∃ p : PhaseSpace, p ∈ positiveReturnSet c ∧ p ∉ equilibriumSet c ∧ forwardOrbit c p = O}

theorem firstCircle_nonempty {s : ℝ} (hs : 0 ≤ s) : (firstCircle s).Nonempty := by
  refine ⟨!₂[Real.sqrt s, 0, 0, 0, 0], ?_⟩
  simp [firstCircle, radiusSq₁, radiusSq₂, Real.sq_sqrt hs]

theorem secondCircle_nonempty {s : ℝ} (hs : 0 ≤ s) : (secondCircle s).Nonempty := by
  refine ⟨!₂[0, 0, Real.sqrt s, 0, 0], ?_⟩
  simp [secondCircle, radiusSq₁, radiusSq₂, Real.sq_sqrt hs]

theorem firstCircle_ne_firstCircle {s u : ℝ} (hs : 0 ≤ s) (hsu : s ≠ u) :
    firstCircle s ≠ firstCircle u := by
  intro heq
  obtain ⟨p, hp⟩ := firstCircle_nonempty hs
  have hq : p ∈ firstCircle u := heq ▸ hp
  exact hsu (hp.1.symm.trans hq.1)

theorem secondCircle_ne_secondCircle {s u : ℝ} (hs : 0 ≤ s) (hsu : s ≠ u) :
    secondCircle s ≠ secondCircle u := by
  intro heq
  obtain ⟨p, hp⟩ := secondCircle_nonempty hs
  have hq : p ∈ secondCircle u := heq ▸ hp
  exact hsu (hp.2.1.symm.trans hq.2.1)

theorem firstCircle_ne_secondCircle {s u : ℝ} (hs : 0 < s) :
    firstCircle s ≠ secondCircle u := by
  intro heq
  obtain ⟨p, hp⟩ := firstCircle_nonempty hs.le
  have hq : p ∈ secondCircle u := heq ▸ hp
  linarith [hp.1, hq.1]

theorem firstCircle_mem_geometricPeriodicOrbits {c s : ℝ} (hc : 0 < c)
    (hs : s = 1 ∨ s = 2) : firstCircle s ∈ geometricPeriodicOrbits c := by
  have hs₀ : 0 < s := by rcases hs with rfl | rfl <;> norm_num
  obtain ⟨p, hp⟩ := firstCircle_nonempty hs₀.le
  refine ⟨p, ⟨2 * Real.pi, by positivity, first_plane_return c ?_ hp.2.1 hp.2.2⟩,
    ?_, forwardOrbit_eq_firstCircle c hs hp⟩
  · exact hs.imp (hp.1.trans ·) (hp.1.trans ·)
  · intro heq
    have hz := (vectorField_eq_zero_iff (ne_of_gt hc) p).mp heq
    have hr : radiusSq₁ p = 0 := by simp [hz, radiusSq₁]
    linarith [hp.1]

theorem secondCircle_mem_geometricPeriodicOrbits {c s : ℝ} (hc : 0 < c)
    (hs : s = 1 ∨ s = 2) : secondCircle s ∈ geometricPeriodicOrbits c := by
  have hs₀ : 0 < s := by rcases hs with rfl | rfl <;> norm_num
  obtain ⟨p, hp⟩ := secondCircle_nonempty hs₀.le
  refine ⟨p, ⟨2 * Real.pi / Real.sqrt 2, by positivity,
    second_plane_return c hp.1 ?_ hp.2.2⟩, ?_, forwardOrbit_eq_secondCircle c hs hp⟩
  · exact hs.imp (hp.2.1.trans ·) (hp.2.1.trans ·)
  · intro heq
    have hz := (vectorField_eq_zero_iff (ne_of_gt hc) p).mp heq
    have hr : radiusSq₂ p = 0 := by simp [hz, radiusSq₂]
    linarith [hp.2.1]

/-- The complete geometric-orbit classification for every c>0. -/
theorem geometricPeriodicOrbits_eq {c : ℝ} (hc : 0 < c) :
    geometricPeriodicOrbits c = {firstCircle 1, firstCircle 2, secondCircle 1, secondCircle 2} := by
  ext O
  constructor
  · rintro ⟨p, hp, hne, hO⟩
    rcases (mem_positiveReturnSet_iff hc p).mp hp with rfl | h | h | h | h
    · exact False.elim (hne ((vectorField_eq_zero_iff (ne_of_gt hc) 0).mpr rfl))
    · have hcircle := hO.symm.trans (forwardOrbit_eq_firstCircle c (Or.inl rfl) h)
      simp [hcircle]
    · have hcircle := hO.symm.trans (forwardOrbit_eq_firstCircle c (Or.inr rfl) h)
      simp [hcircle]
    · have hcircle := hO.symm.trans (forwardOrbit_eq_secondCircle c (Or.inl rfl) h)
      simp [hcircle]
    · have hcircle := hO.symm.trans (forwardOrbit_eq_secondCircle c (Or.inr rfl) h)
      simp [hcircle]
  · intro h
    simp only [mem_insert_iff, mem_singleton_iff] at h
    rcases h with rfl | rfl | rfl | rfl
    · exact firstCircle_mem_geometricPeriodicOrbits hc (Or.inl rfl)
    · exact firstCircle_mem_geometricPeriodicOrbits hc (Or.inr rfl)
    · exact secondCircle_mem_geometricPeriodicOrbits hc (Or.inl rfl)
    · exact secondCircle_mem_geometricPeriodicOrbits hc (Or.inr rfl)

/-- There are exactly four nonconstant geometric periodic orbits. -/
theorem geometricPeriodicOrbits_encard {c : ℝ} (hc : 0 < c) :
    (geometricPeriodicOrbits c).encard = 4 := by
  apply Set.encard_eq_four.mpr
  refine ⟨firstCircle 1, firstCircle 2, secondCircle 1, secondCircle 2, ?_, ?_, ?_, ?_, ?_, ?_,
    geometricPeriodicOrbits_eq hc⟩
  · exact firstCircle_ne_firstCircle (by norm_num) (by norm_num)
  · exact firstCircle_ne_secondCircle (by norm_num)
  · exact firstCircle_ne_secondCircle (by norm_num)
  · exact firstCircle_ne_secondCircle (by norm_num)
  · exact firstCircle_ne_secondCircle (by norm_num)
  · exact secondCircle_ne_secondCircle (by norm_num) (by norm_num)

end Eden
