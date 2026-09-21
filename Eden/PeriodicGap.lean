import Eden.PeriodicDimensions
import Eden.PeriodicOrbits

/-!
# The attained periodic dimension maxima and the strict gap

Both maxima are over the entire union of equilibria and periodic points in the
attractor. A unit-circle point attains three at every positive real time;
outer-circle points have dimension one and the origin has zero.
-/

noncomputable section
open Set
namespace Eden

/-- The largest limiting Kaplan--Yorke dimension over all periodic points and
equilibria in the attractor is three, attained on a unit circle. -/
theorem asymptoticDimension_periodic_isGreatest {c : ℝ} (hc : 4 < c) :
    IsGreatest (asymptoticDimension c '' periodicEquilibriumSet c) 3 := by
  constructor
  · obtain ⟨p, hp⟩ := firstCircle_nonempty (show (0 : ℝ) ≤ 1 by norm_num)
    refine ⟨p, ?_, asymptoticDimension_first_unit_circle hc hp⟩
    rw [periodicEquilibriumSet_eq_positiveReturnSet (show 0 < c by linarith)]
    exact (mem_positiveReturnSet_iff (by linarith) p).mpr (Or.inr (Or.inl hp))
  · rintro d ⟨p, hp, rfl⟩
    exact asymptoticDimension_periodic_le_three hc hp

/-- For every positive real time the largest local dimension on the full
periodic/equilibrium set is exactly three and is attained. -/
theorem finiteTimeDimension_periodic_isGreatest {c t : ℝ} (hc : 4 < c) (ht : 0 < t) :
    IsGreatest (finiteTimeDimension c t '' periodicEquilibriumSet c) 3 := by
  constructor
  · obtain ⟨p, hp, hdim⟩ := (asymptoticDimension_periodic_isGreatest hc).1
    exact ⟨p, hp, (finiteTimeDimension_eq_asymptotic_on_periodic (by linarith) ht hp).trans hdim⟩
  · rintro d ⟨p, hp, rfl⟩
    rw [finiteTimeDimension_eq_asymptotic_on_periodic (by linarith) ht hp]
    exact asymptoticDimension_periodic_le_three hc hp

theorem supremum_asymptoticDimension_periodic {c : ℝ} (hc : 4 < c) :
    sSup (asymptoticDimension c '' periodicEquilibriumSet c) = 3 :=
  (asymptoticDimension_periodic_isGreatest hc).csSup_eq

theorem supremum_finiteTimeDimension_periodic {c t : ℝ} (hc : 4 < c) (ht : 0 < t) :
    sSup (finiteTimeDimension c t '' periodicEquilibriumSet c) = 3 :=
  (finiteTimeDimension_periodic_isGreatest hc ht).csSup_eq

theorem periodic_asymptotic_dimension_gap {c : ℝ} (hc : 4 < c) :
    sSup (asymptoticDimension c '' periodicEquilibriumSet c) <
      globalLyapunovDimension c attractor := by
  rw [supremum_asymptoticDimension_periodic hc, globalLyapunovDimension_attractor hc]
  have := (targetDimension_bounds hc).1
  change 4 < 4 + 4 / c at this
  linarith

theorem periodic_finiteTime_dimension_gap {c t : ℝ} (hc : 4 < c) (ht : 0 < t) :
    sSup (finiteTimeDimension c t '' periodicEquilibriumSet c) <
      globalLyapunovDimension c attractor := by
  rw [supremum_finiteTimeDimension_periodic hc ht, globalLyapunovDimension_attractor hc]
  have := (targetDimension_bounds hc).1
  change 4 < 4 + 4 / c at this
  linarith

/-- The exact specialization c=8, retaining attainment of both periodic maxima and
the separately defined global Lyapunov dimension. -/
theorem dimension_gap_eight {t : ℝ} (ht : 0 < t) :
    globalLyapunovDimension 8 attractor = 9 / 2 ∧
      IsGreatest (asymptoticDimension 8 '' periodicEquilibriumSet 8) 3 ∧
      IsGreatest (finiteTimeDimension 8 t '' periodicEquilibriumSet 8) 3 :=
  ⟨globalLyapunovDimension_attractor_eight,
    asymptoticDimension_periodic_isGreatest (by norm_num),
    finiteTimeDimension_periodic_isGreatest (by norm_num) ht⟩

end Eden
