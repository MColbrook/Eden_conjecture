import Eden.InvariantSets
import Eden.GrowthRates

/-!
# Ordinary radii of the evolution

The square-root formulas are connected to the two Euclidean planar radii. All
statements include zero initial radius where appropriate. The limits use
Mathlib's continuity of square root, and time monotonicity uses its mean value
theorem on a convex interval.
-/

noncomputable section
open Filter Set
open scoped Topology
namespace Eden

/-- The ordinary-radius formula, interpreted for initial radius `r ≥ 0`. It gives a
forward solution for every such radius; complete solutions on `[0,sqrt(2)]` are
established separately in `CompleteTrajectories`. -/
def radiusEvolution (t r : ℝ) : ℝ := Real.sqrt (squaredRadiusEvolution t (r ^ 2))

theorem radiusEvolution_nonneg (t r : ℝ) : 0 ≤ radiusEvolution t r := Real.sqrt_nonneg _

theorem radiusEvolution_sq {t : ℝ} (ht : 0 ≤ t) (r : ℝ) :
    radiusEvolution t r ^ 2 = squaredRadiusEvolution t (r ^ 2) :=
  Real.sq_sqrt (squaredRadiusEvolution_nonneg ht (sq_nonneg r))

@[simp] theorem radiusEvolution_zero_time {r : ℝ} (hr : 0 ≤ r) :
    radiusEvolution 0 r = r := by simp [radiusEvolution, Real.sqrt_sq hr]

@[simp] theorem radiusEvolution_at_zero (t : ℝ) : radiusEvolution t 0 = 0 := by
  simp [radiusEvolution]

@[simp] theorem radiusEvolution_at_one (t : ℝ) : radiusEvolution t 1 = 1 := by
  simp [radiusEvolution]

@[simp] theorem radiusEvolution_at_sqrt_two (t : ℝ) :
    radiusEvolution t (Real.sqrt 2) = Real.sqrt 2 := by
  simp [radiusEvolution]

theorem radiusEvolution_pos {t r : ℝ} (ht : 0 ≤ t) (hr : 0 < r) :
    0 < radiusEvolution t r :=
  Real.sqrt_pos.2 ((squaredRadiusEvolution_pos_iff ht).2 (sq_pos_of_pos hr))

theorem radiusEvolution_mono {t r R : ℝ} (ht : 0 ≤ t) (hr : 0 ≤ r) (hrR : r ≤ R) :
    radiusEvolution t r ≤ radiusEvolution t R := by
  apply Real.sqrt_le_sqrt
  exact (strictMono_squaredRadiusEvolution ht).monotone (by nlinarith)

theorem radiusEvolution_le_max {t r : ℝ} (ht : 0 ≤ t) (hr : 0 ≤ r) :
    radiusEvolution t r ≤ max r (Real.sqrt 2) := by
  rcases le_total r (Real.sqrt 2) with h | h
  · exact (radiusEvolution_mono ht hr h).trans (by simp)
  · have hs : 2 ≤ r ^ 2 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg (2 : ℝ)]
    have hle := Real.sqrt_le_sqrt (squaredRadiusEvolution_le_initial ht hs)
    simpa only [radiusEvolution, Real.sqrt_sq hr, max_eq_left h] using hle

theorem radiusEvolution_ge_sqrt_two {t R : ℝ} (ht : 0 ≤ t) (hR : Real.sqrt 2 ≤ R) :
    Real.sqrt 2 ≤ radiusEvolution t R := by
  simpa using radiusEvolution_mono ht (Real.sqrt_nonneg (2 : ℝ)) hR

theorem hasDerivAt_radiusEvolution {t r : ℝ} (ht : 0 ≤ t) (hr : 0 ≤ r) :
    HasDerivAt (fun τ => radiusEvolution τ r) (radialField (radiusEvolution t r)) t := by
  rcases eq_or_lt_of_le hr with hr | hr
  · subst r
    simpa [radialField] using hasDerivAt_const t (0 : ℝ)
  have hpos := (squaredRadiusEvolution_pos_iff ht).2 (sq_pos_of_pos hr)
  have hR := radiusEvolution_pos ht hr
  have hsq := radiusEvolution_sq ht r
  apply ((hasDerivAt_squaredRadiusEvolution ht (r ^ 2)).sqrt hpos.ne').congr_deriv
  change (-2 * squaredRadiusEvolution t (r ^ 2) *
      (squaredRadiusEvolution t (r ^ 2) - 1) *
      (squaredRadiusEvolution t (r ^ 2) - 2)) /
      (2 * radiusEvolution t r) = radialField (radiusEvolution t r)
  rw [← hsq]
  unfold radialField
  field_simp

theorem radiusEvolution_antitoneOn {R : ℝ} (hR : Real.sqrt 2 ≤ R) :
    AntitoneOn (fun t => radiusEvolution t R) (Ici 0) := by
  have hR₀ : 0 ≤ R := (Real.sqrt_nonneg _).trans hR
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
    (fun t ht => (hasDerivAt_radiusEvolution ht hR₀).continuousAt.continuousWithinAt)
    (fun t ht => (hasDerivAt_radiusEvolution (interior_subset ht) hR₀).hasDerivWithinAt)
  intro t ht
  have hRt := radiusEvolution_ge_sqrt_two (interior_subset ht) hR
  have hRn := radiusEvolution_nonneg t R
  have hsq : 2 ≤ radiusEvolution t R ^ 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg (2 : ℝ)]
  unfold radialField
  exact mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hRn) (by linarith)) (by linarith)

theorem tendsto_radiusEvolution_of_lt_one {r : ℝ} (hr : 0 ≤ r) (hr₁ : r < 1) :
    Tendsto (fun t => radiusEvolution t r) atTop (𝓝 0) := by
  simpa only [radiusEvolution, Real.sqrt_zero] using
    (tendsto_squaredRadiusEvolution_of_lt_one (s := r ^ 2) (by nlinarith)).sqrt

theorem tendsto_radiusEvolution_of_one_lt {r : ℝ} (hr : 1 < r) :
    Tendsto (fun t => radiusEvolution t r) atTop (𝓝 (Real.sqrt 2)) :=
  (tendsto_squaredRadiusEvolution_of_one_lt (s := r ^ 2) (by nlinarith)).sqrt

theorem radius₁_evolution (c : ℝ) {t : ℝ} (ht : 0 ≤ t) (p : PhaseSpace) :
    Real.sqrt (radiusSq₁ (evolution c t p)) = radiusEvolution t (Real.sqrt (radiusSq₁ p)) := by
  rw [radiusSq₁_evolution c ht]
  simp only [radiusEvolution, Real.sq_sqrt (radiusSq₁_nonneg p)]

theorem radius₂_evolution (c : ℝ) {t : ℝ} (ht : 0 ≤ t) (p : PhaseSpace) :
    Real.sqrt (radiusSq₂ (evolution c t p)) = radiusEvolution t (Real.sqrt (radiusSq₂ p)) := by
  rw [radiusSq₂_evolution c ht]
  simp only [radiusEvolution, Real.sq_sqrt (radiusSq₂_nonneg p)]

theorem abs_fifth_evolution (c t : ℝ) (p : PhaseSpace) :
    |evolution c t p 4| = Real.exp (-c * t) * |p 4| := by
  simp [evolution, abs_mul, abs_of_pos (Real.exp_pos _)]

end Eden
