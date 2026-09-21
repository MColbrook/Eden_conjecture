import Eden.SingularValueFunction
import Eden.VolumeGrowth

/-!
# Exact finite-time and global Lyapunov dimensions

The fifth singular value and sharp four-value product determine the
singular-value function on [4,5]. The maximal dimension is 4+4/c, with equality
precisely on the torus. Taking the infimum over positive real times gives
the global Lyapunov dimension.
-/

noncomputable section
open Set
namespace Eden

theorem singularValueFunction_evolution_on_four_five {c t d : ℝ}
    (hc : 4 ≤ c) (ht : 0 ≤ t) {p : PhaseSpace} (hp : p ∈ attractor)
    (hd₄ : 4 ≤ d) (hd₅ : d ≤ 5) :
    singularValueFunction (fderiv ℝ (evolution c t) p).toLinearMap d =
      Real.exp (4 * t - 6 * volumeDefect t p - c * t * (d - 4)) := by
  have h := singularValueFunction_interpolate (fderiv ℝ (evolution c t) p).toLinearMap
    (k := 4) (by norm_num) (α := d - 4) (by linarith) (by linarith)
  norm_num only [Nat.cast_ofNat] at h
  rw [show (4 : ℝ) + (d - 4) = d by ring] at h
  rw [h, singularValues_fderiv_evolution_fifth hc ht hp]
  have hprod := singularValues_fderiv_evolution_prod_four hc ht hp
  rw [Fin.prod_univ_eq_prod_range] at hprod
  rw [hprod, ← Real.exp_mul, ← Real.exp_add]
  congr 1
  ring

theorem singularValueFunction_evolution_at_target {c t : ℝ}
    (hc : 4 < c) (ht : 0 ≤ t) {p : PhaseSpace} (hp : p ∈ attractor) :
    singularValueFunction (fderiv ℝ (evolution c t) p).toLinearMap (targetDimension c) =
      Real.exp (-6 * volumeDefect t p) := by
  have hd := targetDimension_bounds hc
  rw [singularValueFunction_evolution_on_four_five hc.le ht hp hd.1.le hd.2.le]
  congr 1
  unfold targetDimension
  have hcn : c ≠ 0 := by linarith
  field_simp
  ring

theorem singularValueFunction_evolution_above_target {c t d : ℝ}
    (hc : 4 < c) (ht : 0 < t) {p : PhaseSpace} (hp : p ∈ attractor)
    (hd : targetDimension c < d) (hd₅ : d ≤ 5) :
    singularValueFunction (fderiv ℝ (evolution c t) p).toLinearMap d =
      Real.exp (-6 * volumeDefect t p - c * t * (d - targetDimension c)) := by
  rw [singularValueFunction_evolution_on_four_five hc.le ht.le hp
    ((targetDimension_bounds hc).1.trans hd).le hd₅]
  congr 1
  unfold targetDimension
  have hcn : c ≠ 0 := by linarith
  field_simp
  ring

theorem singularValueFunction_evolution_above_target_lt_one {c t d : ℝ}
    (hc : 4 < c) (ht : 0 < t) {p : PhaseSpace} (hp : p ∈ attractor)
    (hd : targetDimension c < d) (hd₅ : d ≤ 5) :
    singularValueFunction (fderiv ℝ (evolution c t) p).toLinearMap d < 1 := by
  rw [singularValueFunction_evolution_above_target hc ht hp hd hd₅, Real.exp_lt_one_iff]
  have hpos : 0 < c * t * (d - targetDimension c) :=
    mul_pos (mul_pos (by linarith) ht) (sub_pos.mpr hd)
  linarith [volumeDefect_nonneg ht.le p]

theorem finiteTimeDimension_le_target {c t : ℝ} (hc : 4 < c) (ht : 0 < t)
    {p : PhaseSpace} (hp : p ∈ attractor) : finiteTimeDimension c t p ≤ targetDimension c := by
  have hmax := finiteTimeDimension_isGreatest c ht.le p
  by_contra h
  have hlt := singularValueFunction_evolution_above_target_lt_one hc ht hp
    (lt_of_not_ge h) hmax.1.1.2
  exact (not_lt_of_ge hmax.1.2) hlt

theorem finiteTimeDimension_eq_target_iff {c t : ℝ} (hc : 4 < c) (ht : 0 < t)
    {p : PhaseSpace} (hp : p ∈ attractor) :
    finiteTimeDimension c t p = targetDimension c ↔ p ∈ torus := by
  constructor
  · intro heq
    have hmem := (finiteTimeDimension_isGreatest c ht.le p).1.2
    rw [heq, singularValueFunction_evolution_at_target hc ht.le hp] at hmem
    have hlog : 0 ≤ -6 * volumeDefect t p := Real.one_le_exp_iff.mp hmem
    exact (volumeDefect_eq_zero_iff ht hp).1 (by linarith [volumeDefect_nonneg ht.le p])
  · intro hT
    apply le_antisymm (finiteTimeDimension_le_target hc ht hp)
    apply (finiteTimeDimension_isGreatest c ht.le p).2
    refine ⟨⟨by linarith [(targetDimension_bounds hc).1], (targetDimension_bounds hc).2.le⟩, ?_⟩
    rw [singularValueFunction_evolution_at_target hc ht.le hp,
      (volumeDefect_eq_zero_iff ht hp).2 hT]
    simp

theorem finiteTimeDimension_lt_target_of_not_mem_torus {c t : ℝ}
    (hc : 4 < c) (ht : 0 < t) {p : PhaseSpace} (hp : p ∈ attractor) (hT : p ∉ torus) :
    finiteTimeDimension c t p < targetDimension c :=
  lt_of_le_of_ne (finiteTimeDimension_le_target hc ht hp)
    (fun heq => hT ((finiteTimeDimension_eq_target_iff hc ht hp).1 heq))

theorem finiteTimeDimension_on_torus {c t : ℝ} (hc : 4 < c) (ht : 0 < t)
    {p : PhaseSpace} (hp : p ∈ torus) : finiteTimeDimension c t p = 4 + 4 / c :=
  (finiteTimeDimension_eq_target_iff hc ht (torus_subset_attractor hp)).2 hp

theorem finiteTimeDimension_attractor_isGreatest {c t : ℝ} (hc : 4 < c) (ht : 0 < t) :
    IsGreatest (finiteTimeDimension c t '' attractor) (targetDimension c) := by
  constructor
  · obtain ⟨p, hp⟩ := torus_nonempty
    exact ⟨p, torus_subset_attractor hp,
      (finiteTimeDimension_eq_target_iff hc ht (torus_subset_attractor hp)).2 hp⟩
  · rintro d ⟨p, hp, rfl⟩
    exact finiteTimeDimension_le_target hc ht hp

theorem supremum_finiteTimeDimension_attractor {c t : ℝ} (hc : 4 < c) (ht : 0 < t) :
    sSup (finiteTimeDimension c t '' attractor) = targetDimension c :=
  (finiteTimeDimension_attractor_isGreatest hc ht).csSup_eq

/-- The global infimum over all real positive times equals the same attained
finite-time maximum. This is the Lyapunov dimension of the attractor. -/
theorem globalLyapunovDimension_attractor {c : ℝ} (hc : 4 < c) :
    globalLyapunovDimension c attractor = 4 + 4 / c := by
  have heq : {v : ℝ | ∃ t : ℝ, 0 < t ∧ v = sSup (finiteTimeDimension c t '' attractor)} =
      {targetDimension c} := by
    ext v
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact (supremum_finiteTimeDimension_attractor hc ht)
    · intro hv
      have hv' : v = targetDimension c := hv
      refine ⟨1, by norm_num, ?_⟩
      rw [supremum_finiteTimeDimension_attractor hc (by norm_num), hv']
  unfold globalLyapunovDimension
  rw [heq, csInf_singleton]
  rfl

theorem globalLyapunovDimension_attractor_eight :
    globalLyapunovDimension 8 attractor = 9 / 2 := by
  rw [globalLyapunovDimension_attractor (by norm_num)]
  norm_num

end Eden
