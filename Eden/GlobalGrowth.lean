import Eden.IntegerGrowthBounds

/-!
# Globally maximised integer growth

The supremum is over the derivative products on A before any
logarithm or time limit. Explicit positive lower and finite upper bounds
justify each real supremum. The derivative cocycle, invariance of A and
the exterior operator inequality give submultiplicativity. Taking logarithms
then proves the subadditivity and a two-sided linear time bound.
-/

noncomputable section
open Set
namespace Eden

/-- Values of the integer singular-value function over the full attractor. -/
def integerGrowthValues (c : ℝ) (k : ℕ) (t : ℝ) : Set ℝ :=
  (fun p => singularValueFunction (fderiv ℝ (evolution c t) p).toLinearMap k) '' attractor

/-- The spatial supremum, before taking the logarithm. -/
def supremumSingularProduct (c : ℝ) (k : ℕ) (t : ℝ) : ℝ := sSup (integerGrowthValues c k t)

/-- The function G_k(t), defined from the supremum over A. -/
def globalLogGrowth (c : ℝ) (k : ℕ) (t : ℝ) : ℝ := Real.log (supremumSingularProduct c k t)

theorem integerGrowthValues_nonempty (c : ℝ) (k : ℕ) (t : ℝ) :
    (integerGrowthValues c k t).Nonempty := attractor_nonempty.image _

theorem integerGrowthValues_bddAbove {k : ℕ} (hk : k ≤ 5) {c t : ℝ}
    (hc : 4 ≤ c) (ht : 0 ≤ t) : BddAbove (integerGrowthValues c k t) := by
  refine ⟨Real.exp ((k : ℝ) * (3 * t)), ?_⟩
  rintro x ⟨p, hp, rfl⟩
  exact (singularValueFunction_integer_evolution_bounds hk hc ht hp).2

theorem supremumSingularProduct_bounds {k : ℕ} (hk : k ≤ 5) {c t : ℝ}
    (hc : 4 ≤ c) (ht : 0 ≤ t) :
    Real.exp ((k : ℝ) * (-c * t)) ≤ supremumSingularProduct c k t ∧
      supremumSingularProduct c k t ≤ Real.exp ((k : ℝ) * (3 * t)) := by
  constructor
  · obtain ⟨p, hp⟩ := attractor_nonempty
    exact (singularValueFunction_integer_evolution_bounds hk hc ht hp).1.trans
      (le_csSup (integerGrowthValues_bddAbove hk hc ht) ⟨p, hp, rfl⟩)
  · apply csSup_le (integerGrowthValues_nonempty c k t)
    rintro x ⟨p, hp, rfl⟩
    exact (singularValueFunction_integer_evolution_bounds hk hc ht hp).2

theorem supremumSingularProduct_pos {k : ℕ} (hk : k ≤ 5) {c t : ℝ}
    (hc : 4 ≤ c) (ht : 0 ≤ t) : 0 < supremumSingularProduct c k t :=
  (Real.exp_pos _).trans_le (supremumSingularProduct_bounds hk hc ht).1

theorem singularValueFunction_le_supremum {k : ℕ} (hk : k ≤ 5) {c t : ℝ}
    (hc : 4 ≤ c) (ht : 0 ≤ t) {p : PhaseSpace} (hp : p ∈ attractor) :
    singularValueFunction (fderiv ℝ (evolution c t) p).toLinearMap k ≤ supremumSingularProduct c k t :=
  le_csSup (integerGrowthValues_bddAbove hk hc ht) ⟨p, hp, rfl⟩

theorem supremumSingularProduct_zero {k : ℕ} (hk : k ≤ 5) {c : ℝ} (hc : 4 ≤ c) :
    supremumSingularProduct c k 0 = 1 := by
  have h := supremumSingularProduct_bounds hk hc (le_refl (0 : ℝ))
  simp only [mul_zero, Real.exp_zero] at h
  exact le_antisymm h.2 h.1

theorem globalLogGrowth_zero {k : ℕ} (hk : k ≤ 5) {c : ℝ} (hc : 4 ≤ c) :
    globalLogGrowth c k 0 = 0 := by
  simp [globalLogGrowth, supremumSingularProduct_zero hk hc]

/-- Spatial suprema remain over A at the intermediate base point of the cocycle. -/
theorem supremumSingularProduct_add_le {k : ℕ} (hk : k ≤ 5) {c s t : ℝ}
    (hc : 4 ≤ c) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    supremumSingularProduct c k (s + t) ≤ supremumSingularProduct c k s * supremumSingularProduct c k t := by
  apply csSup_le (integerGrowthValues_nonempty c k (s + t))
  rintro x ⟨p, hp, rfl⟩
  apply (singularValueFunction_evolution_add_le hk c hs ht p).trans
  calc
    _ ≤ supremumSingularProduct c k t * supremumSingularProduct c k s := by
      exact mul_le_mul
        (singularValueFunction_le_supremum hk hc ht (evolution_mem_attractor c hs hp))
        (singularValueFunction_le_supremum hk hc hs hp)
        (singularValueFunction_integer_evolution_pos hk c hs p).le
        (supremumSingularProduct_pos hk hc ht).le
    _ = _ := mul_comm _ _

/-- The function G_k is subadditive through all nonnegative real times. -/
theorem globalLogGrowth_subadditive {k : ℕ} (hk : k ≤ 5) {c s t : ℝ}
    (hc : 4 ≤ c) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    globalLogGrowth c k (s + t) ≤ globalLogGrowth c k s + globalLogGrowth c k t := by
  have h := Real.log_le_log (supremumSingularProduct_pos hk hc (add_nonneg hs ht))
    (supremumSingularProduct_add_le hk hc hs ht)
  rw [Real.log_mul (ne_of_gt (supremumSingularProduct_pos hk hc hs))
    (ne_of_gt (supremumSingularProduct_pos hk hc ht))] at h
  exact h

theorem globalLogGrowth_bounds {k : ℕ} (hk : k ≤ 5) {c t : ℝ}
    (hc : 4 ≤ c) (ht : 0 ≤ t) :
    (k : ℝ) * (-c * t) ≤ globalLogGrowth c k t ∧ globalLogGrowth c k t ≤ (k : ℝ) * (3 * t) := by
  have hp := supremumSingularProduct_bounds hk hc ht
  have hl := Real.log_le_log (Real.exp_pos _) hp.1
  have hu := Real.log_le_log (supremumSingularProduct_pos hk hc ht) hp.2
  rw [Real.log_exp] at hl hu
  exact ⟨hl, hu⟩

theorem abs_globalLogGrowth_le {k : ℕ} (hk : k ≤ 5) {c t : ℝ}
    (hc : 4 ≤ c) (ht : 0 ≤ t) : |globalLogGrowth c k t| ≤ ((k : ℝ) * c) * t := by
  have h := globalLogGrowth_bounds hk hc ht
  have hkt : 0 ≤ (k : ℝ) * t := mul_nonneg (Nat.cast_nonneg _) ht
  rw [abs_le]
  constructor <;> nlinarith

/-- An explicit finite constant works uniformly for every nonnegative real time. -/
theorem exists_globalLogGrowth_linear_bound {k : ℕ} (hk : k ≤ 5) {c : ℝ} (hc : 4 ≤ c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t → |globalLogGrowth c k t| ≤ C * t := by
  exact ⟨(k : ℝ) * c, mul_nonneg (Nat.cast_nonneg _) (by linarith),
    fun t ht => abs_globalLogGrowth_le hk hc ht⟩

end Eden
