import Eden.UniformAttraction
import Eden.PeriodicOrbits

/-!
# Radial perturbations and distance from invariant circles

The planar coordinate projections are contractions for the ambient Euclidean
norm. The reverse triangle inequality therefore converts radial departure
into distance from any set with a fixed unit planar radius. All perturbations
used below remain in A. The norm inequalities use Mathlib's normed-group
library (Patrick Massot, Johannes Hölzl and Yaël Dillies).
-/

noncomputable section
open Set
namespace Eden

/-- The first or second Euclidean coordinate plane, indexed by Fin 2. -/
def planeProjection (j : Fin 2) (p : PhaseSpace) : EuclideanSpace ℝ (Fin 2) :=
  if j = 0 then !₂[p 0, p 1] else !₂[p 2, p 3]

theorem norm_planeProjection (j : Fin 2) (p : PhaseSpace) :
    ‖planeProjection j p‖ = Real.sqrt (if j = 0 then radiusSq₁ p else radiusSq₂ p) := by
  have h : ‖planeProjection j p‖ ^ 2 =
      (if j = 0 then radiusSq₁ p else radiusSq₂ p) := by
    fin_cases j <;> simp [planeProjection, EuclideanSpace.real_norm_sq_eq,
      Fin.sum_univ_succ, radiusSq₁, radiusSq₂]
  rw [← h, Real.sqrt_sq (norm_nonneg _)]

theorem norm_planeProjection_le (j : Fin 2) (p : PhaseSpace) :
    ‖planeProjection j p‖ ≤ ‖p‖ := by
  rw [norm_planeProjection]
  fin_cases j
  · exact radius₁_le_norm p
  · exact radius₂_le_norm p

theorem planeProjection_sub (j : Fin 2) (p q : PhaseSpace) :
    planeProjection j (p - q) = planeProjection j p - planeProjection j q := by
  fin_cases j <;> ext i <;> fin_cases i <;> simp [planeProjection]

theorem plane_radius_sub_le_dist (j : Fin 2) (p q : PhaseSpace) :
    ‖planeProjection j q‖ - ‖planeProjection j p‖ ≤ dist p q := by
  calc
    _ ≤ ‖planeProjection j q - planeProjection j p‖ := norm_sub_norm_le _ _
    _ = ‖planeProjection j (q - p)‖ := by rw [planeProjection_sub]
    _ ≤ ‖q - p‖ := norm_planeProjection_le j (q - p)
    _ = dist p q := by rw [← dist_eq_norm, dist_comm]

theorem one_sub_plane_radius_le_infDist (j : Fin 2) {K : Set PhaseSpace}
    (hK : K.Nonempty) (hunit : ∀ q ∈ K, ‖planeProjection j q‖ = 1)
    (p : PhaseSpace) : 1 - ‖planeProjection j p‖ ≤ Metric.infDist p K := by
  apply (Metric.le_infDist hK).2
  intro q hq
  simpa only [hunit q hq] using plane_radius_sub_le_dist j p q

/-- Radial coordinate coefficients r and s, with planar radii |r| and |s|. -/
def radialPerturbation (j : Fin 2) (r s : ℝ) : PhaseSpace :=
  if j = 0 then !₂[r, 0, s, 0, 0] else !₂[s, 0, r, 0, 0]

theorem norm_planeProjection_radialPerturbation (j : Fin 2) (r s : ℝ) :
    ‖planeProjection j (radialPerturbation j r s)‖ = |r| := by
  rw [norm_planeProjection]
  fin_cases j <;> simp [radialPerturbation, radiusSq₁, radiusSq₂, Real.sqrt_sq_eq_abs]

theorem radialPerturbation_mem_attractor (j : Fin 2) {r s : ℝ}
    (hr : r ∈ Icc 0 1) (hs : s ∈ Icc 0 1) : radialPerturbation j r s ∈ attractor := by
  have hr' : r ^ 2 ≤ 2 := by nlinarith [hr.1, hr.2]
  have hs' : s ^ 2 ≤ 2 := by nlinarith [hs.1, hs.2]
  fin_cases j
  · simpa [radialPerturbation, attractor, radiusSq₁, radiusSq₂] using And.intro hr' hs'
  · simpa [radialPerturbation, attractor, radiusSq₁, radiusSq₂] using And.intro hs' hr'

theorem dist_radialPerturbation (j : Fin 2) (r u s : ℝ) :
    dist (radialPerturbation j r s) (radialPerturbation j u s) = |r - u| := by
  apply (sq_eq_sq₀ dist_nonneg (abs_nonneg _)).mp
  rw [sq_abs, dist_eq_norm, norm_sq_phaseSpace]
  fin_cases j <;> simp [radialPerturbation, radiusSq₁, radiusSq₂]

theorem plane_radius_evolution_radialPerturbation (c : ℝ) (j : Fin 2)
    {t r : ℝ} (ht : 0 ≤ t) (hr : 0 ≤ r) (s : ℝ) :
    ‖planeProjection j (evolution c t (radialPerturbation j r s))‖ = radiusEvolution t r := by
  rw [norm_planeProjection]
  fin_cases j
  · change Real.sqrt (radiusSq₁ (evolution c t (radialPerturbation 0 r s))) = _
    rw [radius₁_evolution c ht]
    simp [radialPerturbation, radiusSq₁, Real.sqrt_sq hr]
  · change Real.sqrt (radiusSq₂ (evolution c t (radialPerturbation 1 r s))) = _
    rw [radius₂_evolution c ht]
    simp [radialPerturbation, radiusSq₂, Real.sqrt_sq hr]

end Eden
