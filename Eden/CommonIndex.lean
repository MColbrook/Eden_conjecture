import Eden.ExponentSums

/-!
# The common-index convention

The index is the least k in {0,...,4} for which the supremum of S_(k+1)
is negative. Its definition uses the exponents and the full
attractor. The index is shared by all points, including periodic points;
it is not the pointwise Kaplan--Yorke index.
-/

noncomputable section
open Set
namespace Eden

/-- Globally admissible indices; nonemptiness and the minimum are proved for c>4. -/
def commonIndexCandidates (c : ℝ) : Set ℕ :=
  {k | k ≤ 4 ∧ supremumExponentSum c (k + 1) < 0}

/-- The least globally admissible index. For c>4 this index is four. -/
def commonIndex (c : ℝ) : ℕ := sInf (commonIndexCandidates c)

theorem commonIndexCandidates_isLeast {c : ℝ} (hc : 4 < c) :
    IsLeast (commonIndexCandidates c) 4 := by
  constructor
  · change 4 ≤ 4 ∧ supremumExponentSum c 5 < 0
    rw [supremumExponentSum_five hc]
    constructor <;> linarith
  · intro k hk
    by_contra h
    have hk₄ : k + 1 ≤ 4 := by omega
    exact (not_lt_of_ge (supremumExponentSum_nonneg hc hk₄)) hk.2

theorem commonIndex_eq_four {c : ℝ} (hc : 4 < c) : commonIndex c = 4 :=
  (commonIndexCandidates_isLeast hc).csInf_eq

/-- The point-dependent quotient inside the common-index supremum. -/
def commonIndexRatio (c : ℝ) (p : PhaseSpace) : ℝ :=
  spectrumPartialSum (lyapunovExponent c p) (commonIndex c) /
    (-spectrumEntry (lyapunovExponent c p) (commonIndex c))

/-- The pointwise expression with the global index fixed, used for c>4. -/
def commonIndexLocalDimension (c : ℝ) (p : PhaseSpace) : ℝ :=
  (commonIndex c : ℝ) + commonIndexRatio c p

/-- The index is selected globally before the quotient is maximised. -/
def commonIndexDimension (c : ℝ) : ℝ :=
  (commonIndex c : ℝ) + sSup (commonIndexRatio c '' attractor)

theorem commonIndexRatio_eq {c : ℝ} (hc : 4 < c) (p : PhaseSpace) :
    commonIndexRatio c p = spectrumPartialSum (lyapunovExponent c p) 4 / c := by
  simp [commonIndexRatio, commonIndex_eq_four hc, spectrumEntry, lyapunovExponent_fifth hc]

theorem commonIndexLocalDimension_eq {c : ℝ} (hc : 4 < c) (p : PhaseSpace) :
    commonIndexLocalDimension c p = 4 + spectrumPartialSum (lyapunovExponent c p) 4 / c := by
  simp [commonIndexLocalDimension, commonIndex_eq_four hc, commonIndexRatio_eq hc]

theorem commonIndexRatio_isGreatest {c : ℝ} (hc : 4 < c) :
    IsGreatest (commonIndexRatio c '' attractor) (4 / c) := by
  constructor
  · obtain ⟨p, hp, he⟩ := (exponentSum_four_isGreatest hc).1
    dsimp only at he
    exact ⟨p, hp, by rw [commonIndexRatio_eq hc, he]⟩
  · rintro x ⟨p, hp, rfl⟩
    rw [commonIndexRatio_eq hc]
    exact div_le_div_of_nonneg_right (exponentSum_four_bound_and_eq hc p).1 (by linarith)

/-- The common-index dimension on the full attractor is exactly 4+4/c. -/
theorem commonIndexDimension_eq_target {c : ℝ} (hc : 4 < c) :
    commonIndexDimension c = 4 + 4 / c := by
  rw [commonIndexDimension, commonIndex_eq_four hc, (commonIndexRatio_isGreatest hc).csSup_eq]
  norm_num

theorem commonIndexLocalDimension_eq_target_iff {c : ℝ} (hc : 4 < c)
    {p : PhaseSpace} (hp : p ∈ attractor) :
    commonIndexLocalDimension c p = 4 + 4 / c ↔ p ∈ torus := by
  rw [commonIndexLocalDimension_eq hc, add_right_inj,
    div_left_inj' (show c ≠ 0 by linarith), exponentSum_four_eq_iff hc hp]

theorem commonIndexLocalDimension_isGreatest {c : ℝ} (hc : 4 < c) :
    IsGreatest (commonIndexLocalDimension c '' attractor) (4 + 4 / c) := by
  constructor
  · obtain ⟨p, hp, he⟩ := (commonIndexRatio_isGreatest hc).1
    exact ⟨p, hp, by simp [commonIndexLocalDimension, commonIndex_eq_four hc, he]⟩
  · rintro x ⟨p, hp, rfl⟩
    simp only [commonIndexLocalDimension, commonIndex_eq_four hc, Nat.cast_ofNat]
    linarith [(commonIndexRatio_isGreatest hc).2 ⟨p, hp, rfl⟩]

end Eden
