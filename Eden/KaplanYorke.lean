import Eden.LyapunovExponents
import Mathlib.Data.Finset.Max

/-!
# Kaplan--Yorke dimension

The index is the largest integer k in {0,...,5} whose partial sum is
nonnegative. Thus zero partial sums, including neutral directions, remain
admissible. The middle branch uses the next exponent, whose strict negativity
is proved from maximality.

The finite maximum is Mathlib's Finset.max', with its membership and
greatest-element characterisations, developed by Mario Carneiro.
-/

noncomputable section
namespace Eden

/-- Extend a five-entry spectrum by zero, only to simplify finite sums. -/
def spectrumEntry (a : Fin 5 → ℝ) (i : ℕ) : ℝ :=
  if h : i < 5 then a ⟨i, h⟩ else 0

/-- Sum of the first k entries. -/
def spectrumPartialSum (a : Fin 5 → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range k, spectrumEntry a i

@[simp] theorem spectrumPartialSum_zero (a : Fin 5 → ℝ) :
    spectrumPartialSum a 0 = 0 := by simp [spectrumPartialSum]

theorem spectrumPartialSum_succ (a : Fin 5 → ℝ) (k : ℕ) :
    spectrumPartialSum a (k + 1) = spectrumPartialSum a k + spectrumEntry a k :=
  Finset.sum_range_succ _ _

/-- Indices with nonnegative partial sums. -/
def nonnegativeSumIndices (a : Fin 5 → ℝ) : Finset ℕ :=
  (Finset.range 6).filter (fun k => 0 ≤ spectrumPartialSum a k)

theorem nonnegativeSumIndices_nonempty (a : Fin 5 → ℝ) :
    (nonnegativeSumIndices a).Nonempty := by
  refine ⟨0, ?_⟩
  simp [nonnegativeSumIndices]

/-- Largest admissible index, with zero always available. -/
def kaplanYorkeIndex (a : Fin 5 → ℝ) : ℕ :=
  (nonnegativeSumIndices a).max' (nonnegativeSumIndices_nonempty a)

theorem kaplanYorkeIndex_mem (a : Fin 5 → ℝ) :
    kaplanYorkeIndex a ≤ 5 ∧ 0 ≤ spectrumPartialSum a (kaplanYorkeIndex a) := by
  have h := Finset.max'_mem (nonnegativeSumIndices a) (nonnegativeSumIndices_nonempty a)
  change kaplanYorkeIndex a ∈ nonnegativeSumIndices a at h
  simpa only [nonnegativeSumIndices, Finset.mem_filter, Finset.mem_range,
    Nat.lt_succ_iff] using h

theorem le_kaplanYorkeIndex {a : Fin 5 → ℝ} {k : ℕ} (hk : k ≤ 5)
    (hs : 0 ≤ spectrumPartialSum a k) : k ≤ kaplanYorkeIndex a := by
  exact Finset.le_max' _ _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hs⟩)

theorem kaplanYorkeIndex_eq {a : Fin 5 → ℝ} {j : ℕ} (hj : j ≤ 5)
    (hs : 0 ≤ spectrumPartialSum a j)
    (hafter : ∀ k, j < k → k ≤ 5 → spectrumPartialSum a k < 0) :
    kaplanYorkeIndex a = j := by
  apply le_antisymm
  · by_contra h
    have hi := kaplanYorkeIndex_mem a
    exact (not_lt_of_ge hi.2) (hafter _ (lt_of_not_ge h) hi.1)
  · exact le_kaplanYorkeIndex hj hs

theorem spectrumPartialSum_after_index_neg {a : Fin 5 → ℝ} {k : ℕ}
    (hk : kaplanYorkeIndex a < k) (hk₅ : k ≤ 5) : spectrumPartialSum a k < 0 := by
  by_contra h
  exact (not_le_of_gt hk) (le_kaplanYorkeIndex hk₅ (le_of_not_gt h))

/-- The next exponent is strictly negative whenever the index is below five. -/
theorem spectrumEntry_at_kaplanYorkeIndex_neg {a : Fin 5 → ℝ}
    (hj : kaplanYorkeIndex a < 5) : spectrumEntry a (kaplanYorkeIndex a) < 0 := by
  have hsum := spectrumPartialSum_after_index_neg
    (show kaplanYorkeIndex a < kaplanYorkeIndex a + 1 by omega) (by omega)
  rw [spectrumPartialSum_succ] at hsum
  have := (kaplanYorkeIndex_mem a).2
  linarith

/-- The Kaplan--Yorke formula, including both endpoint branches. -/
def kaplanYorkeDimension (a : Fin 5 → ℝ) : ℝ :=
  if kaplanYorkeIndex a = 0 then 0
  else if kaplanYorkeIndex a = 5 then 5
  else (kaplanYorkeIndex a : ℝ) +
    spectrumPartialSum a (kaplanYorkeIndex a) / |spectrumEntry a (kaplanYorkeIndex a)|

/-- Kaplan--Yorke dimension of the ordered Lyapunov exponents. -/
def asymptoticDimension (c : ℝ) (p : PhaseSpace) : ℝ :=
  kaplanYorkeDimension (lyapunovExponent c p)

theorem kaplanYorkeDimension_of_index_zero {a : Fin 5 → ℝ}
    (hj : kaplanYorkeIndex a = 0) : kaplanYorkeDimension a = 0 := by
  simp [kaplanYorkeDimension, hj]

theorem kaplanYorkeDimension_of_index_five {a : Fin 5 → ℝ}
    (hj : kaplanYorkeIndex a = 5) : kaplanYorkeDimension a = 5 := by
  simp [kaplanYorkeDimension, hj]

theorem kaplanYorkeDimension_of_index_between {a : Fin 5 → ℝ} {j : ℕ}
    (hj : kaplanYorkeIndex a = j) (hj₀ : 0 < j) (hj₅ : j < 5) :
    kaplanYorkeDimension a = (j : ℝ) + spectrumPartialSum a j / |spectrumEntry a j| := by
  simp [kaplanYorkeDimension, hj, ne_of_gt hj₀, ne_of_lt hj₅]

/-- In the middle branch the dimension lies in the unit interval beginning
at the largest nonnegative partial-sum index, with a strict upper endpoint. -/
theorem kaplanYorkeDimension_between_index {a : Fin 5 → ℝ}
    (hj₀ : 0 < kaplanYorkeIndex a) (hj₅ : kaplanYorkeIndex a < 5) :
    (kaplanYorkeIndex a : ℝ) ≤ kaplanYorkeDimension a ∧
      kaplanYorkeDimension a < (kaplanYorkeIndex a : ℝ) + 1 := by
  have hneg := spectrumEntry_at_kaplanYorkeIndex_neg hj₅
  have hsum := spectrumPartialSum_after_index_neg
    (show kaplanYorkeIndex a < kaplanYorkeIndex a + 1 by omega) (by omega)
  rw [spectrumPartialSum_succ] at hsum
  rw [kaplanYorkeDimension_of_index_between rfl hj₀ hj₅, abs_of_neg hneg]
  have hlo : 0 ≤ spectrumPartialSum a (kaplanYorkeIndex a) /
      -spectrumEntry a (kaplanYorkeIndex a) :=
    div_nonneg (kaplanYorkeIndex_mem a).2 (by linarith)
  have hhi : spectrumPartialSum a (kaplanYorkeIndex a) /
      -spectrumEntry a (kaplanYorkeIndex a) < 1 :=
    (div_lt_one (show 0 < -spectrumEntry a (kaplanYorkeIndex a) by linarith)).mpr
      (by linarith)
  constructor <;> linarith

theorem kaplanYorkeDimension_mem_interval (a : Fin 5 → ℝ) :
    kaplanYorkeDimension a ∈ Set.Icc 0 5 := by
  by_cases h₀ : kaplanYorkeIndex a = 0
  · rw [kaplanYorkeDimension_of_index_zero h₀]
    norm_num
  by_cases h₅ : kaplanYorkeIndex a = 5
  · rw [kaplanYorkeDimension_of_index_five h₅]
    norm_num
  have hj₀ : 0 < kaplanYorkeIndex a := by omega
  have hj₅ : kaplanYorkeIndex a < 5 := lt_of_le_of_ne (kaplanYorkeIndex_mem a).1 h₅
  have h := kaplanYorkeDimension_between_index hj₀ hj₅
  have hj : (kaplanYorkeIndex a : ℝ) + 1 ≤ 5 := by exact_mod_cast hj₅
  constructor
  · exact (Nat.cast_nonneg _).trans h.1
  · exact h.2.le.trans hj

end Eden
