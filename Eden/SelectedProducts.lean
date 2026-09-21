import Eden.SelectedSums

/-!
# The greatest product of a fixed number of nonnegative entries

The increasing enumeration and equal-multiset permutation from SelectedSums also
apply to products. Direct multiplication of the ordered inequalities avoids
logarithms and retains zero entries and repeated values.
-/

noncomputable section
namespace Eden

theorem prod_antitone_embedding_le {k n : ℕ} (hk : k ≤ n) {a : Fin n → ℝ}
    (ha : Antitone a) (hpos : ∀ i, 0 ≤ a i) (e : Fin k ↪ Fin n) :
    (∏ i : Fin k, a (e i)) ≤ ∏ i : Fin k, a (Fin.castLE hk i) := by
  classical
  let s := Finset.univ.image e
  have hs : s.card = k := by simp [s, Finset.card_image_of_injective _ e.injective]
  let o := s.orderEmbOfFin hs
  have hprod : (∏ i : Fin k, a (e i)) = ∏ i : Fin k, a (o i) := by
    calc
      (∏ i : Fin k, a (e i)) = ∏ j ∈ s, a j := by
        simp [s, Finset.prod_image, e.injective.injOn]
      _ = ∏ i : Fin k, a (o i) := by
        rw [← Finset.image_orderEmbOfFin_univ s hs,
          Finset.prod_image (fun _ _ _ _ h => (s.orderEmbOfFin hs).injective h)]
  rw [hprod]
  exact Finset.prod_le_prod (fun i _ => hpos (o i))
    (fun i _ => ha (orderEmbedding_fin_val_le o i))

/-- The first k entries attain the largest k-fold product of any permutation of a
descending nonnegative vector, including ties and zero entries. -/
theorem isGreatest_selected_prod {k n : ℕ} (hk : k ≤ n) {a b : Fin n → ℝ}
    (ha : Antitone a) (hpos : ∀ i, 0 ≤ a i)
    (hm : Finset.univ.val.map a = Finset.univ.val.map b) :
    IsGreatest {r : ℝ | ∃ s : Set.powersetCard (Fin n) k, r = ∏ j ∈ s.val, b j}
      (∏ i : Fin k, a (Fin.castLE hk i)) := by
  classical
  obtain ⟨e, he⟩ := exists_equiv_of_multiset_eq hm
  constructor
  · let f : Fin k ↪ Fin n := (Fin.castLEEmb hk).trans e.toEmbedding
    let s := Finset.univ.image f
    have hs : s.card = k := by simp [s, Finset.card_image_of_injective _ f.injective]
    refine ⟨⟨s, hs⟩, ?_⟩
    change (∏ i : Fin k, a (Fin.castLE hk i)) = ∏ j ∈ s, b j
    simp [s, Finset.prod_image, f.injective.injOn, f, he]
  · rintro r ⟨s, rfl⟩
    let f : Fin k ↪ Fin n := (Set.powersetCard.ofFinEmbEquiv.symm s).toEmbedding
    have hprod : (∏ j ∈ s.val, b j) = ∏ i : Fin k, b (f i) := by
      change (∏ j ∈ s.val, b j) = ∏ i : Fin k, b (s.val.orderEmbOfFin s.property i)
      conv_lhs => rw [← Finset.image_orderEmbOfFin_univ s.val s.property]
      rw [Finset.prod_image (fun _ _ _ _ h => (s.val.orderEmbOfFin s.property).injective h)]
    rw [hprod]
    have he' (j : Fin n) : b j = a (e.symm j) := by simpa using he (e.symm j)
    simp_rw [he']
    exact prod_antitone_embedding_le hk ha hpos (f.trans e.symm.toEmbedding)

end Eden
