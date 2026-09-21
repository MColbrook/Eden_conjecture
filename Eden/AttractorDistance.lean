import Eden.InvariantSets
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# An explicit distance bound to the product of discs

Each planar coordinate is projected radially onto the closed disc of radius
sqrt(2), and the fifth coordinate is set to zero. The Euclidean distance to
this point is computed exactly, then bounds Mathlib's distance to the set.
The construction includes zero coordinates and does not require a polar angle.
-/

noncomputable section
namespace Eden

/-- Scale for projection onto the closed disc of radius sqrt(2). -/
def discScale (r : ℝ) : ℝ := if r ≤ Real.sqrt 2 then 1 else Real.sqrt 2 / r

theorem discScale_radius_bound (x y : ℝ) :
    (discScale (Real.sqrt (x ^ 2 + y ^ 2)) * x) ^ 2 +
      (discScale (Real.sqrt (x ^ 2 + y ^ 2)) * y) ^ 2 ≤ 2 := by
  have hs : 0 ≤ x ^ 2 + y ^ 2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hsq := Real.sq_sqrt hs
  have ha := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hn := Real.sqrt_nonneg (x ^ 2 + y ^ 2)
  have han := Real.sqrt_nonneg (2 : ℝ)
  by_cases h : Real.sqrt (x ^ 2 + y ^ 2) ≤ Real.sqrt 2
  · simp only [discScale, if_pos h, one_mul]
    nlinarith
  · have hp : 0 < Real.sqrt (x ^ 2 + y ^ 2) := by
      have := lt_of_not_ge h
      linarith
    simp only [discScale, if_neg h]
    have heq : (Real.sqrt 2 / Real.sqrt (x ^ 2 + y ^ 2) * x) ^ 2 +
        (Real.sqrt 2 / Real.sqrt (x ^ 2 + y ^ 2) * y) ^ 2 = 2 := by
      field_simp
      nlinarith [congrArg (fun z : ℝ => z * (x ^ 2 + y ^ 2)) ha]
    exact heq.le

theorem discScale_distance_sq (x y : ℝ) :
    (x - discScale (Real.sqrt (x ^ 2 + y ^ 2)) * x) ^ 2 +
      (y - discScale (Real.sqrt (x ^ 2 + y ^ 2)) * y) ^ 2 =
      max (Real.sqrt (x ^ 2 + y ^ 2) - Real.sqrt 2) 0 ^ 2 := by
  have hs : 0 ≤ x ^ 2 + y ^ 2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hsq := Real.sq_sqrt hs
  have han := Real.sqrt_nonneg (2 : ℝ)
  by_cases h : Real.sqrt (x ^ 2 + y ^ 2) ≤ Real.sqrt 2
  · simp [discScale, h]
  · have hp : 0 < Real.sqrt (x ^ 2 + y ^ 2) := by
      have := lt_of_not_ge h
      linarith
    rw [max_eq_left (by linarith : 0 ≤ Real.sqrt (x ^ 2 + y ^ 2) - Real.sqrt 2)]
    simp only [discScale, if_neg h]
    calc
      _ = (1 - Real.sqrt 2 / Real.sqrt (x ^ 2 + y ^ 2)) ^ 2 * (x ^ 2 + y ^ 2) := by ring
      _ = (Real.sqrt (x ^ 2 + y ^ 2) - Real.sqrt 2) ^ 2 := by
        conv_lhs => arg 2; rw [← hsq]
        field_simp

/-- Radial projection onto the product of discs in the plane w=0. -/
def attractorProjection (p : PhaseSpace) : PhaseSpace :=
  !₂[discScale (Real.sqrt (radiusSq₁ p)) * p 0,
     discScale (Real.sqrt (radiusSq₁ p)) * p 1,
     discScale (Real.sqrt (radiusSq₂ p)) * p 2,
     discScale (Real.sqrt (radiusSq₂ p)) * p 3, 0]

theorem attractorProjection_mem (p : PhaseSpace) : attractorProjection p ∈ attractor := by
  refine ⟨discScale_radius_bound (p 0) (p 1), discScale_radius_bound (p 2) (p 3), rfl⟩

theorem dist_attractorProjection_sq (p : PhaseSpace) :
    dist p (attractorProjection p) ^ 2 =
      max (Real.sqrt (radiusSq₁ p) - Real.sqrt 2) 0 ^ 2 +
      max (Real.sqrt (radiusSq₂ p) - Real.sqrt 2) 0 ^ 2 + p 4 ^ 2 := by
  rw [dist_eq_norm, norm_sq_phaseSpace]
  change ((p 0 - discScale (Real.sqrt (radiusSq₁ p)) * p 0) ^ 2 +
    (p 1 - discScale (Real.sqrt (radiusSq₁ p)) * p 1) ^ 2) +
    ((p 2 - discScale (Real.sqrt (radiusSq₂ p)) * p 2) ^ 2 +
    (p 3 - discScale (Real.sqrt (radiusSq₂ p)) * p 3) ^ 2) + (p 4 - 0) ^ 2 = _
  dsimp only [radiusSq₁, radiusSq₂]
  rw [discScale_distance_sq (p 0) (p 1), discScale_distance_sq (p 2) (p 3), sub_zero]

theorem infDist_attractor_sq_le (p : PhaseSpace) :
    Metric.infDist p attractor ^ 2 ≤
      max (Real.sqrt (radiusSq₁ p) - Real.sqrt 2) 0 ^ 2 +
      max (Real.sqrt (radiusSq₂ p) - Real.sqrt 2) 0 ^ 2 + p 4 ^ 2 := by
  have hle := Metric.infDist_le_dist_of_mem (x := p) (attractorProjection_mem p)
  have heq := dist_attractorProjection_sq p
  have hn : 0 ≤ Metric.infDist p attractor := Metric.infDist_nonneg
  nlinarith

end Eden
