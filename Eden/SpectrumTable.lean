import Eden.KaplanYorke

/-!
# The six limiting spectrum types

The auxiliary block-order vector uses the two limiting squared radii. Its
connection to the Lyapunov exponents is proved first. Equality of multisets and
descending rearrangement give the six ordered spectra. Swapping the two planes
leaves the resulting ordered spectrum unchanged.
-/

noncomputable section
namespace Eden

/-- Block-order rates at two specified limiting squared radii. -/
def radiusPairSpectrum (c s₁ s₂ : ℝ) : Fin 5 → ℝ :=
  ![radialRate s₁, tangentialRate s₁, radialRate s₂, tangentialRate s₂, -c]

theorem lyapunovExponent_eq_radiusPairSpectrum (c : ℝ) (p : PhaseSpace) :
    lyapunovExponent c p = descending (radiusPairSpectrum c
      (limitingSquaredRadius (radiusSq₁ p)) (limitingSquaredRadius (radiusSq₂ p))) := by
  funext i
  exact lyapunovExponent_eq_descending c p i

theorem limitingSquaredRadius_cases (s : ℝ) :
    limitingSquaredRadius s = 0 ∨ limitingSquaredRadius s = 1 ∨ limitingSquaredRadius s = 2 := by
  by_cases h : s < 1
  · simp [limitingSquaredRadius, h]
  · by_cases he : s = 1 <;> simp [limitingSquaredRadius, h, he]

theorem limitingSquaredRadius_eq_one_iff (s : ℝ) : limitingSquaredRadius s = 1 ↔ s = 1 := by
  by_cases h : s < 1
  · simp [limitingSquaredRadius, h, ne_of_lt h]
  · by_cases he : s = 1 <;> simp [limitingSquaredRadius, h, he]

theorem descending_radiusPairSpectrum_swap (c s₁ s₂ : ℝ) :
    descending (radiusPairSpectrum c s₁ s₂) = descending (radiusPairSpectrum c s₂ s₁) := by
  apply antitone_eq_of_multiset_eq (descending_antitone _) (descending_antitone _)
  rw [multiset_descending, multiset_descending]
  simp only [radiusPairSpectrum, Fin.univ_val_map, List.ofFn_succ, List.ofFn_zero,
    Matrix.cons_val_zero, Matrix.cons_val_succ, ← Multiset.cons_coe, ← Multiset.singleton_add]
  ac_rfl

private theorem descending_eq_of_antitone_and_multiset {f g : Fin 5 → ℝ}
    (hg : Antitone g) (hm : Finset.univ.val.map f = Finset.univ.val.map g) :
    descending f = g :=
  antitone_eq_of_multiset_eq (descending_antitone _) hg ((multiset_descending _).trans hm)

/-- Either ordering of the two limiting squared radii determines the same ordered
spectrum. Squared radius two corresponds to ordinary radius sqrt(2). -/
theorem lyapunovExponent_eq_of_limiting_radii (c : ℝ) (p : PhaseSpace) {s₁ s₂ : ℝ}
    (h : (limitingSquaredRadius (radiusSq₁ p) = s₁ ∧
        limitingSquaredRadius (radiusSq₂ p) = s₂) ∨
      (limitingSquaredRadius (radiusSq₁ p) = s₂ ∧
        limitingSquaredRadius (radiusSq₂ p) = s₁)) :
    lyapunovExponent c p = descending (radiusPairSpectrum c s₁ s₂) := by
  rw [lyapunovExponent_eq_radiusPairSpectrum]
  rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · rw [h₁, h₂]
  · rw [h₁, h₂, descending_radiusPairSpectrum_swap c s₂ s₁]

theorem descending_radiusPairSpectrum_zero_zero {c : ℝ} (hc : 4 < c) :
    descending (radiusPairSpectrum c 0 0) = ![-2, -2, -2, -2, -c] := by
  apply descending_eq_of_antitone_and_multiset
  · rw [Fin.antitone_iff_succ_le]
    intro i
    fin_cases i <;> simp
    all_goals linarith
  · norm_num [radiusPairSpectrum, radialRate, tangentialRate]

theorem descending_radiusPairSpectrum_zero_one {c : ℝ} (hc : 4 < c) :
    descending (radiusPairSpectrum c 0 1) = ![2, 0, -2, -2, -c] := by
  apply descending_eq_of_antitone_and_multiset
  · rw [Fin.antitone_iff_succ_le]
    intro i
    fin_cases i <;> simp
    all_goals linarith
  · norm_num [radiusPairSpectrum, radialRate, tangentialRate, Fin.univ_val_map,
      List.ofFn_succ, List.ofFn_zero, ← Multiset.cons_coe, ← Multiset.singleton_add]
    ac_rfl

theorem descending_radiusPairSpectrum_zero_two {c : ℝ} (hc : 4 < c) :
    descending (radiusPairSpectrum c 0 2) = ![0, -2, -2, -4, -c] := by
  apply descending_eq_of_antitone_and_multiset
  · rw [Fin.antitone_iff_succ_le]
    intro i
    fin_cases i <;> simp
    all_goals linarith
  · norm_num [radiusPairSpectrum, radialRate, tangentialRate, Fin.univ_val_map,
      List.ofFn_succ, List.ofFn_zero, ← Multiset.cons_coe, ← Multiset.singleton_add]
    ac_rfl

theorem descending_radiusPairSpectrum_one_one {c : ℝ} (hc : 4 < c) :
    descending (radiusPairSpectrum c 1 1) = ![2, 2, 0, 0, -c] := by
  apply descending_eq_of_antitone_and_multiset
  · rw [Fin.antitone_iff_succ_le]
    intro i
    fin_cases i <;> simp
    all_goals linarith
  · norm_num [radiusPairSpectrum, radialRate, tangentialRate, Fin.univ_val_map,
      List.ofFn_succ, List.ofFn_zero, ← Multiset.cons_coe, ← Multiset.singleton_add]
    ac_rfl

theorem descending_radiusPairSpectrum_one_two {c : ℝ} (hc : 4 < c) :
    descending (radiusPairSpectrum c 1 2) = ![2, 0, 0, -4, -c] := by
  apply descending_eq_of_antitone_and_multiset
  · rw [Fin.antitone_iff_succ_le]
    intro i
    fin_cases i <;> simp
    all_goals linarith
  · norm_num [radiusPairSpectrum, radialRate, tangentialRate, Fin.univ_val_map,
      List.ofFn_succ, List.ofFn_zero, ← Multiset.cons_coe, ← Multiset.singleton_add]
    ac_rfl

theorem descending_radiusPairSpectrum_two_two {c : ℝ} (hc : 4 < c) :
    descending (radiusPairSpectrum c 2 2) = ![0, 0, -4, -4, -c] := by
  apply descending_eq_of_antitone_and_multiset
  · rw [Fin.antitone_iff_succ_le]
    intro i
    fin_cases i <;> simp
    all_goals linarith
  · norm_num [radiusPairSpectrum, radialRate, tangentialRate, Fin.univ_val_map,
      List.ofFn_succ, List.ofFn_zero, ← Multiset.cons_coe, ← Multiset.singleton_add]
    ac_rfl

end Eden
