import Eden.DimensionConvergence

/-!
# Eventual signs and dimension formulas

The dimension eventually vanishes for the contracting spectrum. For the
two spectra with leading zero exponents, eventual sign conditions give an
exact quotient formula.
-/

noncomputable section
open Set Filter
open scoped Topology
namespace Eden

theorem spectrumInterpolation_kaplanYorke_eq_zero {a : Fin 5 → ℝ}
    (hj : kaplanYorkeIndex a < 5) :
    spectrumInterpolation a (kaplanYorkeDimension a) = 0 := by
  have hα₀ : 0 ≤ kaplanYorkeDimension a - kaplanYorkeIndex a :=
    sub_nonneg.mpr (kaplanYorkeIndex_le_dimension a)
  have hα₁ : kaplanYorkeDimension a - kaplanYorkeIndex a ≤ 1 := by
    linarith [kaplanYorkeDimension_lt_succ_index hj]
  calc
    _ = spectrumPartialSum a (kaplanYorkeIndex a) +
        (kaplanYorkeDimension a - kaplanYorkeIndex a) *
          spectrumEntry a (kaplanYorkeIndex a) := by
      have h := spectrumInterpolation_interpolate a hj hα₀ hα₁
      have heq : (kaplanYorkeIndex a : ℝ) +
          (kaplanYorkeDimension a - kaplanYorkeIndex a) = kaplanYorkeDimension a := by ring
      rw [heq] at h
      exact h
    _ = 0 := by
      rw [kaplanYorkeDimension_formula_of_index_lt_five hj]
      have hn := ne_of_lt (spectrumEntry_at_kaplanYorkeIndex_neg hj)
      field_simp [hn]
      ring

theorem tendsto_spectrumPartialSum_normalized (c : ℝ) (p : PhaseSpace) (k : ℕ) :
    Tendsto (fun t => spectrumPartialSum (normalizedLogSingularValues c t p) k)
      atTop (𝓝 (spectrumPartialSum (lyapunovExponent c p) k)) := by
  unfold spectrumPartialSum
  apply tendsto_finsetSum
  intro i hi
  unfold spectrumEntry
  split_ifs with h
  · exact tendsto_lyapunovExponent c p ⟨i, h⟩
  · exact tendsto_const_nhds

theorem kaplanYorkeIndex_eq_of_adjacent_signs {a : Fin 5 → ℝ} (ha : Antitone a)
    {k : ℕ} (hk : k < 5) (h₀ : 0 ≤ spectrumPartialSum a k)
    (h₁ : spectrumPartialSum a (k + 1) < 0) : kaplanYorkeIndex a = k := by
  apply le_antisymm
  · by_contra h
    have hle : k + 1 ≤ kaplanYorkeIndex a := by omega
    exact (not_le_of_gt h₁) (spectrumPartialSum_nonneg_of_le ha hle
      (kaplanYorkeIndex_mem a).1 (kaplanYorkeIndex_mem a).2)
  · exact le_kaplanYorkeIndex hk.le h₀

theorem eventually_dimension_zero_of_first_exponent_neg (c : ℝ) (p : PhaseSpace)
    (hlim : lyapunovExponent c p 0 < 0) :
    ∀ᶠ t in atTop, (∀ i, normalizedLogSingularValues c t p i < 0) ∧
      finiteTimeDimension c t p = 0 := by
  have he := (tendsto_lyapunovExponent c p 0).eventually (Iio_mem_nhds hlim)
  filter_upwards [he, eventually_gt_atTop (0 : ℝ)] with t ht₀ ht
  have ha := normalizedLogSingularValues_antitone c ht p
  have hneg : ∀ i, normalizedLogSingularValues c t p i < 0 :=
    fun i => (ha (show (0 : Fin 5) ≤ i from Fin.zero_le i)).trans_lt ht₀
  refine ⟨hneg, ?_⟩
  rw [finiteTimeDimension_eq_kaplanYorke c ht p]
  apply kaplanYorkeDimension_of_index_zero
  apply kaplanYorkeIndex_eq_of_adjacent_signs ha (by omega) (by simp)
  simpa [spectrumPartialSum, spectrumEntry] using hneg 0

/-- For `c > 4`, if both limiting squared radii vanish, all five normalized
singular-value logarithms are eventually negative and the finite-time
dimension is eventually exactly zero. This holds at every ambient point
satisfying the radius conditions, without an attractor assumption. -/
theorem eventually_dimension_zero_of_limiting_radii {c : ℝ} (hc : 4 < c)
    (p : PhaseSpace) (h₁ : limitingSquaredRadius (radiusSq₁ p) = 0)
    (h₂ : limitingSquaredRadius (radiusSq₂ p) = 0) :
    ∀ᶠ t in atTop, (∀ i, normalizedLogSingularValues c t p i < 0) ∧
      finiteTimeDimension c t p = 0 := by
  apply eventually_dimension_zero_of_first_exponent_neg c p
  rw [lyapunovExponent_eq_radiusPairSpectrum c p, h₁, h₂,
    descending_radiusPairSpectrum_zero_zero hc]
  norm_num

theorem normalized_nonneg_of_factor_subset (c : ℝ) {t : ℝ} (ht : 0 < t)
    (p : PhaseSpace) (s : Finset (Fin 5))
    (hs : ∀ j ∈ s, 0 ≤ Real.log (derivativeFactors c t p j))
    (i : Fin 5) (hi : i.val < s.card) : 0 ≤ normalizedLogSingularValues c t p i := by
  classical
  have hm : Finset.univ.val.map (normalizedLogSingularValues c t p) =
      Finset.univ.val.map (fun j => Real.log (derivativeFactors c t p j) / t) := by
    rw [normalizedLogSingularValues_eq_descending c ht p]
    exact multiset_descending _
  apply nonneg_of_card_nonneg (normalizedLogSingularValues_antitone c ht p) hm i
  apply hi.trans_le
  apply Finset.card_le_card
  intro j hj
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, div_nonneg (hs j hj) ht.le⟩

theorem normalized_first_nonneg_of_radius (c : ℝ) {t : ℝ} (ht : 0 < t)
    {p : PhaseSpace} (hp : p ∈ attractor)
    (hs : 1 ≤ radiusSq₁ p ∨ 1 ≤ radiusSq₂ p) :
    0 ≤ normalizedLogSingularValues c t p 0 := by
  rcases hs with hs | hs
  · apply normalized_nonneg_of_factor_subset c ht p {1}
    · intro j hj
      have : j = 1 := Finset.mem_singleton.mp hj
      subst j
      exact log_planarAmplitude_nonneg ht.le hs hp.1
    · simp
  · apply normalized_nonneg_of_factor_subset c ht p {3}
    · intro j hj
      have : j = 3 := Finset.mem_singleton.mp hj
      subst j
      exact log_planarAmplitude_nonneg ht.le hs hp.2.1
    · simp

theorem normalized_first_two_nonneg_of_radii (c : ℝ) {t : ℝ} (ht : 0 < t)
    {p : PhaseSpace} (hp : p ∈ attractor) (hs₁ : 1 ≤ radiusSq₁ p)
    (hs₂ : 1 ≤ radiusSq₂ p) (i : Fin 5) (hi : i.val < 2) :
    0 ≤ normalizedLogSingularValues c t p i := by
  apply normalized_nonneg_of_factor_subset c ht p {1, 3}
  · intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl
    · exact log_planarAmplitude_nonneg ht.le hs₁ hp.1
    · exact log_planarAmplitude_nonneg ht.le hs₂ hp.2.1
  · simpa using hi

theorem eventually_dimension_formula_of_neutral_prefix (c : ℝ) (p : PhaseSpace)
    {k : ℕ} (hk : k < 5)
    (hlim₀ : ∀ i : Fin 5, i.val < k → lyapunovExponent c p i = 0)
    (hlim₁ : lyapunovExponent c p ⟨k, hk⟩ < 0)
    (hfinite : ∀ᶠ t in atTop, ∀ i : Fin 5, i.val < k →
      0 ≤ normalizedLogSingularValues c t p i) :
    ∀ᶠ t in atTop,
      (∀ i : Fin 5, i.val < k → 0 ≤ normalizedLogSingularValues c t p i) ∧
      spectrumPartialSum (normalizedLogSingularValues c t p) (k + 1) < 0 ∧
      normalizedLogSingularValues c t p ⟨k, hk⟩ < 0 ∧
      finiteTimeDimension c t p = (k : ℝ) +
        spectrumPartialSum (normalizedLogSingularValues c t p) k /
          -normalizedLogSingularValues c t p ⟨k, hk⟩ := by
  have hsum₀ : spectrumPartialSum (lyapunovExponent c p) k = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hi₅ := lt_trans (Finset.mem_range.mp hi) hk
    rw [spectrumEntry, dif_pos hi₅, hlim₀ ⟨i, hi₅⟩ (Finset.mem_range.mp hi)]
  have hsum₁ : spectrumPartialSum (lyapunovExponent c p) (k + 1) < 0 := by
    rw [spectrumPartialSum_succ, hsum₀, zero_add, spectrumEntry, dif_pos hk]
    exact hlim₁
  have he := (tendsto_spectrumPartialSum_normalized c p (k + 1)).eventually
    (Iio_mem_nhds hsum₁)
  filter_upwards [he, hfinite, eventually_gt_atTop (0 : ℝ)] with t hnext hnonneg ht
  have hsum : 0 ≤ spectrumPartialSum (normalizedLogSingularValues c t p) k := by
    apply Finset.sum_nonneg
    intro i hi
    have hi₅ := lt_trans (Finset.mem_range.mp hi) hk
    rw [spectrumEntry, dif_pos hi₅]
    exact hnonneg ⟨i, hi₅⟩ (Finset.mem_range.mp hi)
  have hindex := kaplanYorkeIndex_eq_of_adjacent_signs
    (normalizedLogSingularValues_antitone c ht p) hk hsum hnext
  have hj : kaplanYorkeIndex (normalizedLogSingularValues c t p) < 5 := by
    rw [hindex]; exact hk
  have hneg := spectrumEntry_at_kaplanYorkeIndex_neg hj
  rw [hindex, spectrumEntry, dif_pos hk] at hneg
  refine ⟨hnonneg, hnext, hneg, ?_⟩
  rw [finiteTimeDimension_eq_kaplanYorke c ht p,
    kaplanYorkeDimension_formula_of_index_lt_five hj, hindex, spectrumEntry, dif_pos hk]

theorem tangentialRate_along_nonneg {s t : ℝ} (hs₁ : 1 ≤ s) (hs₂ : s ≤ 2)
    (ht : 0 ≤ t) : 0 ≤ tangentialRate (squaredRadiusEvolution t s) := by
  apply tangentialRate_nonneg
  · have h := (strictMono_squaredRadiusEvolution ht).monotone hs₁
    simpa using h
  · exact (squaredRadiusEvolution_le_two_iff ht).mpr hs₂

theorem finiteTimeDimension_of_limiting_unit_radii {c t : ℝ} (hc : 4 < c)
    (ht : 0 < t) {p : PhaseSpace} (hp : p ∈ attractor)
    (h₁ : limitingSquaredRadius (radiusSq₁ p) = 1)
    (h₂ : limitingSquaredRadius (radiusSq₂ p) = 1) :
    finiteTimeDimension c t p = targetDimension c := by
  apply (finiteTimeDimension_eq_target_iff hc ht hp).mpr
  exact ⟨(limitingSquaredRadius_eq_one_iff _).mp h₁,
    (limitingSquaredRadius_eq_one_iff _).mp h₂, hp.2.2⟩

/-- The eventual quotient and all signs for the row with one neutral exponent,
allowing either order of the two planar radii. -/
theorem eventually_dimension_formula_zero_two {c : ℝ} (hc : 4 < c)
    {p : PhaseSpace} (hp : p ∈ attractor)
    (hpair : (limitingSquaredRadius (radiusSq₁ p) = 0 ∧
        limitingSquaredRadius (radiusSq₂ p) = 2) ∨
      (limitingSquaredRadius (radiusSq₁ p) = 2 ∧
        limitingSquaredRadius (radiusSq₂ p) = 0)) :
    ∀ᶠ t in atTop, 0 ≤ normalizedLogSingularValues c t p 0 ∧
      spectrumPartialSum (normalizedLogSingularValues c t p) 2 < 0 ∧
      normalizedLogSingularValues c t p 1 < 0 ∧
      finiteTimeDimension c t p = 1 +
        spectrumPartialSum (normalizedLogSingularValues c t p) 1 /
          -normalizedLogSingularValues c t p 1 := by
  have ha := (lyapunovExponent_eq_of_limiting_radii c p hpair).trans
    (descending_radiusPairSpectrum_zero_two hc)
  have hfinite : ∀ᶠ t in atTop, ∀ i : Fin 5, i.val < 1 →
      0 ≤ normalizedLogSingularValues c t p i := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht i hi
    have hi₀ : i = 0 := Fin.ext (by omega)
    subst i
    apply normalized_first_nonneg_of_radius c ht hp
    rcases hpair with h | h
    · exact Or.inr (one_lt_of_limitingSquaredRadius_eq_two h.2).le
    · exact Or.inl (one_lt_of_limitingSquaredRadius_eq_two h.1).le
  have he := eventually_dimension_formula_of_neutral_prefix c p (k := 1) (by omega)
    (by intro i hi; rw [ha]; have : i = 0 := Fin.ext (by omega); subst i; norm_num)
    (by rw [ha]; norm_num) hfinite
  filter_upwards [he] with t ht
  exact ⟨ht.1 0 (by norm_num), ht.2.1, ht.2.2.1, by simpa using ht.2.2.2⟩

/-- The eventual quotient and all signs for the row with two neutral exponents. -/
theorem eventually_dimension_formula_two_two {c : ℝ} (hc : 4 < c)
    {p : PhaseSpace} (hp : p ∈ attractor)
    (h₁ : limitingSquaredRadius (radiusSq₁ p) = 2)
    (h₂ : limitingSquaredRadius (radiusSq₂ p) = 2) :
    ∀ᶠ t in atTop,
      (∀ i : Fin 5, i.val < 2 → 0 ≤ normalizedLogSingularValues c t p i) ∧
      spectrumPartialSum (normalizedLogSingularValues c t p) 3 < 0 ∧
      normalizedLogSingularValues c t p 2 < 0 ∧
      finiteTimeDimension c t p = 2 +
        spectrumPartialSum (normalizedLogSingularValues c t p) 2 /
          -normalizedLogSingularValues c t p 2 := by
  have ha := lyapunovExponent_eq_radiusPairSpectrum c p
  rw [h₁, h₂, descending_radiusPairSpectrum_two_two hc] at ha
  apply eventually_dimension_formula_of_neutral_prefix c p (k := 2) (by omega)
  · intro i hi
    rw [ha]
    fin_cases i <;> norm_num at *
  · rw [ha]; norm_num
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht i hi
    exact normalized_first_two_nonneg_of_radii c ht hp
      (one_lt_of_limitingSquaredRadius_eq_two h₁).le
      (one_lt_of_limitingSquaredRadius_eq_two h₂).le i hi

end Eden
