import Eden.FiniteTimeKaplanYorke
import Eden.FactorBounds

/-!
# Lower dimension bounds from neutral tangential factors

Counting nonnegative factor logarithms retains multiplicities when the factors
are rearranged into the ordered singular-value spectrum. This supplies the lower
bounds needed at limiting zero plateaus.
-/

noncomputable section
open Set
namespace Eden

theorem nonneg_of_card_nonneg {n : ℕ} {a f : Fin n → ℝ} (ha : Antitone a)
    (hm : Finset.univ.val.map a = Finset.univ.val.map f) (i : Fin n)
    (hi : i.val < (Finset.univ.filter (fun j => 0 ≤ f j)).card) : 0 ≤ a i := by
  classical
  by_contra h
  have hcard : (Finset.univ.filter (fun j => 0 ≤ a j)).card ≤ i.val := by
    calc
      _ ≤ (Finset.Iio i).card := Finset.card_le_card (by
        intro j hj
        apply Finset.mem_Iio.mpr
        by_contra hji
        have hle := ha (le_of_not_gt hji)
        exact h ((Finset.mem_filter.mp hj).2.trans hle))
      _ = i.val := Fin.card_Iio i
  rw [card_filter_eq_of_multiset_eq hm (fun x => 0 ≤ x)] at hcard
  omega

theorem finiteTimeDimension_ge_of_nonneg_factor_count (c : ℝ) {t : ℝ} (ht : 0 < t)
    (p : PhaseSpace) {k : ℕ} (hk : k ≤ 5)
    (hcount : k ≤ (Finset.univ.filter
      (fun i : Fin 5 => 0 ≤ Real.log (derivativeFactors c t p i) / t)).card) :
    (k : ℝ) ≤ finiteTimeDimension c t p := by
  classical
  have hm : Finset.univ.val.map (normalizedLogSingularValues c t p) =
      Finset.univ.val.map (fun i => Real.log (derivativeFactors c t p i) / t) := by
    rw [normalizedLogSingularValues_eq_descending c ht p]
    exact multiset_descending _
  have hsum : 0 ≤ spectrumPartialSum (normalizedLogSingularValues c t p) k := by
    apply Finset.sum_nonneg
    intro i hi
    have hi₅ : i < 5 := lt_of_lt_of_le (Finset.mem_range.mp hi) hk
    rw [spectrumEntry, dif_pos hi₅]
    exact nonneg_of_card_nonneg (normalizedLogSingularValues_antitone c ht p)
      hm ⟨i, hi₅⟩ (lt_of_lt_of_le (Finset.mem_range.mp hi) hcount)
  rw [finiteTimeDimension_eq_kaplanYorke c ht p]
  exact (show (k : ℝ) ≤ kaplanYorkeIndex (normalizedLogSingularValues c t p) by
    exact_mod_cast le_kaplanYorkeIndex hk hsum).trans (kaplanYorkeIndex_le_dimension _)

theorem finiteTimeDimension_ge_one_of_tangential_factor (c : ℝ) {t : ℝ} (ht : 0 < t)
    (p : PhaseSpace) (i : Fin 5) (hi : 0 ≤ Real.log (derivativeFactors c t p i)) :
    1 ≤ finiteTimeDimension c t p := by
  classical
  have hbound := finiteTimeDimension_ge_of_nonneg_factor_count c ht p (k := 1) (by omega)
  simp only [Nat.cast_one] at hbound
  apply hbound
  have hsub : ({i} : Finset (Fin 5)) ⊆ Finset.univ.filter
      (fun j => 0 ≤ Real.log (derivativeFactors c t p j) / t) := by
    intro j hj
    have : j = i := Finset.mem_singleton.mp hj
    subst j
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, div_nonneg hi ht.le⟩
  simpa only [Finset.card_singleton] using Finset.card_le_card hsub

theorem finiteTimeDimension_ge_one_of_first_radius (c : ℝ) {t : ℝ} (ht : 0 < t)
    {p : PhaseSpace} (hp : p ∈ attractor) (hs : 1 ≤ radiusSq₁ p) :
    1 ≤ finiteTimeDimension c t p :=
  finiteTimeDimension_ge_one_of_tangential_factor c ht p 1
    (log_planarAmplitude_nonneg ht.le hs hp.1)

theorem finiteTimeDimension_ge_one_of_second_radius (c : ℝ) {t : ℝ} (ht : 0 < t)
    {p : PhaseSpace} (hp : p ∈ attractor) (hs : 1 ≤ radiusSq₂ p) :
    1 ≤ finiteTimeDimension c t p :=
  finiteTimeDimension_ge_one_of_tangential_factor c ht p 3
    (log_planarAmplitude_nonneg ht.le hs hp.2.1)

theorem finiteTimeDimension_ge_two_of_radii (c : ℝ) {t : ℝ} (ht : 0 < t)
    {p : PhaseSpace} (hp : p ∈ attractor)
    (hs₁ : 1 ≤ radiusSq₁ p) (hs₂ : 1 ≤ radiusSq₂ p) :
    2 ≤ finiteTimeDimension c t p := by
  classical
  apply finiteTimeDimension_ge_of_nonneg_factor_count c ht p (k := 2) (by omega)
  have hsub : ({1, 3} : Finset (Fin 5)) ⊆ Finset.univ.filter
      (fun j => 0 ≤ Real.log (derivativeFactors c t p j) / t) := by
    intro j hj
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, div_nonneg ?_ ht.le⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl
    · exact log_planarAmplitude_nonneg ht.le hs₁ hp.1
    · exact log_planarAmplitude_nonneg ht.le hs₂ hp.2.1
  have hcard := Finset.card_le_card hsub
  exact hcard

end Eden
