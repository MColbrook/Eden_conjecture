import Eden.SingularValues
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Order.Compact

/-!
# The singular-value function on the full dimension interval

Continuous truncated weights give the usual product with one fractional power on
each unit interval. The equivalence below includes both endpoints. For a
five-dimensional endomorphism, the value at dimension five equals the absolute
determinant by Mathlib's norm-determinant theorem (Weiyi Wang). Continuity of
real powers and compact order extrema use Mathlib's analysis library, including
the compact-extremum API of Patrick Massot and Yury Kudryashov.
-/

noncomputable section
open Set
namespace Eden

/-- The weight of singular value with zero-based index `i` at dimension `d`. -/
def singularWeight (i : ℕ) (d : ℝ) : ℝ := min 1 (max 0 (d - i))

theorem continuous_singularWeight (i : ℕ) : Continuous (singularWeight i) := by
  unfold singularWeight
  fun_prop

theorem singularWeight_eq_one {i k : ℕ} (hik : i < k) {α : ℝ} (hα : 0 ≤ α) :
    singularWeight i ((k : ℝ) + α) = 1 := by
  have hi : (i : ℝ) + 1 ≤ k := by exact_mod_cast hik
  unfold singularWeight
  rw [max_eq_right (by linarith), min_eq_left (by linarith)]

theorem singularWeight_eq_fraction (k : ℕ) {α : ℝ} (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) :
    singularWeight k ((k : ℝ) + α) = α := by
  simp only [singularWeight, add_sub_cancel_left, max_eq_right hα₀, min_eq_right hα₁]

theorem singularWeight_eq_zero {i k : ℕ} (hki : k < i) {α : ℝ} (hα : α ≤ 1) :
    singularWeight i ((k : ℝ) + α) = 0 := by
  have hi : (k : ℝ) + 1 ≤ i := by exact_mod_cast hki
  unfold singularWeight
  rw [max_eq_left (by linarith)]
  norm_num

/-- Weighted product of the first `n` entries of a spectrum. It is continuous in
dimension when these entries are nonzero, as proved below. -/
def spectralProduct (n : ℕ) (a : ℕ → ℝ) (d : ℝ) : ℝ :=
  ∏ i ∈ Finset.range n, a i ^ singularWeight i d

theorem spectralProduct_interpolate (a : ℕ → ℝ) {n k : ℕ} (hk : k < n)
    {α : ℝ} (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) :
    spectralProduct n a ((k : ℝ) + α) =
      (∏ i ∈ Finset.range k, a i) * a k ^ α := by
  unfold spectralProduct
  have htrunc : (∏ i ∈ Finset.range (k + 1), a i ^ singularWeight i ((k : ℝ) + α)) =
      ∏ i ∈ Finset.range n, a i ^ singularWeight i ((k : ℝ) + α) := by
    apply Finset.prod_subset (Finset.range_mono (by omega))
    intro i hi hnot
    have hki : k < i := by simp only [Finset.mem_range] at hnot; omega
    rw [singularWeight_eq_zero hki hα₁, Real.rpow_zero]
  rw [← htrunc, Finset.prod_range_succ, singularWeight_eq_fraction k hα₀ hα₁]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  rw [singularWeight_eq_one (Finset.mem_range.mp hi) hα₀, Real.rpow_one]

@[simp] theorem spectralProduct_zero (n : ℕ) (a : ℕ → ℝ) : spectralProduct n a 0 = 1 := by
  unfold spectralProduct
  apply Finset.prod_eq_one
  intro i hi
  have hw : singularWeight i 0 = 0 := by
    simp [singularWeight]
  rw [hw, Real.rpow_zero]

theorem spectralProduct_top (n : ℕ) (a : ℕ → ℝ) :
    spectralProduct n a n = ∏ i ∈ Finset.range n, a i := by
  apply Finset.prod_congr rfl
  intro i hi
  have hw := singularWeight_eq_one (Finset.mem_range.mp hi) (le_refl (0 : ℝ))
  simp only [add_zero] at hw
  rw [hw, Real.rpow_one]

theorem continuous_spectralProduct {n : ℕ} {a : ℕ → ℝ}
    (ha : ∀ i < n, a i ≠ 0) : Continuous (spectralProduct n a) := by
  unfold spectralProduct
  apply continuous_finsetProd
  intro i hi
  exact (Real.continuous_const_rpow (ha i (Finset.mem_range.mp hi))).comp
    (continuous_singularWeight i)

/-- Singular-value function of an ambient Euclidean endomorphism, with its
definition on the entire closed interval `[0,5]`. -/
def singularValueFunction (A : PhaseSpace →ₗ[ℝ] PhaseSpace) (d : ℝ) : ℝ :=
  spectralProduct 5 A.singularValues d

@[simp] theorem singularValueFunction_zero (A : PhaseSpace →ₗ[ℝ] PhaseSpace) :
    singularValueFunction A 0 = 1 := spectralProduct_zero _ _

theorem singularValueFunction_interpolate (A : PhaseSpace →ₗ[ℝ] PhaseSpace)
    {k : ℕ} (hk : k < 5) {α : ℝ} (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) :
    singularValueFunction A ((k : ℝ) + α) =
      (∏ i ∈ Finset.range k, A.singularValues i) * A.singularValues k ^ α :=
  spectralProduct_interpolate _ hk hα₀ hα₁

theorem singularValueFunction_five (A : PhaseSpace →ₗ[ℝ] PhaseSpace) :
    singularValueFunction A 5 = |A.det| := by
  change spectralProduct 5 (fun i => A.singularValues i) (5 : ℕ) = _
  rw [spectralProduct_top]
  have h := A.normDet_eq_prod_singularValues
  rw [finrank_euclideanSpace_fin] at h
  exact h.symm.trans A.normDet_eq_abs_det

theorem continuous_singularValueFunction {A : PhaseSpace →ₗ[ℝ] PhaseSpace}
    (hA : Function.Injective A) : Continuous (singularValueFunction A) := by
  apply continuous_spectralProduct
  intro i hi
  have hpos := A.injective_iff_forall_lt_finrank_singularValues_pos.mp hA i
    (by simpa only [finrank_euclideanSpace_fin] using hi)
  exact ne_of_gt hpos

/-- All admissible dimensions, including the integer and ambient endpoints. -/
def admissibleDimensions (A : PhaseSpace →ₗ[ℝ] PhaseSpace) : Set ℝ :=
  {d | d ∈ Icc 0 5 ∧ 1 ≤ singularValueFunction A d}

theorem admissibleDimensions_nonempty (A : PhaseSpace →ₗ[ℝ] PhaseSpace) :
    (admissibleDimensions A).Nonempty := by
  refine ⟨0, ⟨by norm_num, ?_⟩⟩
  simp

theorem isCompact_admissibleDimensions {A : PhaseSpace →ₗ[ℝ] PhaseSpace}
    (hA : Function.Injective A) : IsCompact (admissibleDimensions A) :=
  isCompact_Icc.inter_right (isClosed_le continuous_const (continuous_singularValueFunction hA))

/-- The supremum of admissible dimensions, proved attained for injective maps. -/
def mapLyapunovDimension (A : PhaseSpace →ₗ[ℝ] PhaseSpace) : ℝ := sSup (admissibleDimensions A)

theorem mapLyapunovDimension_isGreatest {A : PhaseSpace →ₗ[ℝ] PhaseSpace}
    (hA : Function.Injective A) : IsGreatest (admissibleDimensions A) (mapLyapunovDimension A) :=
  (isCompact_admissibleDimensions hA).isGreatest_sSup (admissibleDimensions_nonempty A)

/-- Finite-time Lyapunov dimension of the ambient derivative. Its interpretation as
the paper's attained maximum is proved for every `t > 0`. -/
def finiteTimeDimension (c t : ℝ) (p : PhaseSpace) : ℝ :=
  mapLyapunovDimension (fderiv ℝ (evolution c t) p).toLinearMap

theorem finiteTimeDimension_isGreatest (c : ℝ) {t : ℝ} (ht : 0 ≤ t) (p : PhaseSpace) :
    IsGreatest (admissibleDimensions (fderiv ℝ (evolution c t) p).toLinearMap)
      (finiteTimeDimension c t p) :=
  mapLyapunovDimension_isGreatest (fderiv_evolution_bijective c ht p).injective

theorem finiteTimeDimension_mem_interval (c : ℝ) {t : ℝ} (ht : 0 ≤ t) (p : PhaseSpace) :
    finiteTimeDimension c t p ∈ Icc 0 5 := (finiteTimeDimension_isGreatest c ht p).1.1

/-- Global Lyapunov dimension with the paper's order of operations: the infimum over
all real positive times of the pointwise supremum over `K`. -/
def globalLyapunovDimension (c : ℝ) (K : Set PhaseSpace) : ℝ :=
  sInf {v : ℝ | ∃ t : ℝ, 0 < t ∧ v = sSup (finiteTimeDimension c t '' K)}

end Eden
