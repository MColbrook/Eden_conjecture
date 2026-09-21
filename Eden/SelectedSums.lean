import Eden.Sorting
import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Order.Hom.PowersetCard

/-!
# The greatest sum of a fixed number of entries

Equal multisets give a permutation by matching equal-value fibres, retaining all
repeated values. For an antitone vector, the first k entries dominate any
selection of k distinct indices. These facts use Mathlib's finite cardinality
equivalences and increasing enumeration of finite sets.
-/

noncomputable section
namespace Eden

theorem exists_equiv_of_multiset_eq {n : ℕ} {a b : Fin n → ℝ}
    (h : Finset.univ.val.map a = Finset.univ.val.map b) :
    ∃ e : Fin n ≃ Fin n, ∀ i, b (e i) = a i := by
  classical
  have hc (r : ℝ) : Fintype.card {i // a i = r} = Fintype.card {i // b i = r} := by
    simpa only [Fintype.card_subtype] using card_filter_eq_of_multiset_eq h (fun x => x = r)
  let e := fun r => Fintype.equivOfCardEq (hc r)
  exact ⟨Equiv.ofFiberEquiv e, Equiv.ofFiberEquiv_map e⟩

theorem orderEmbedding_fin_val_le {k n : ℕ} (e : Fin k ↪o Fin n) (i : Fin k) :
    i.val ≤ (e i).val := by
  cases k with
  | zero => exact Fin.elim0 i
  | succ k =>
    induction i using Fin.induction with
    | zero => exact Nat.zero_le _
    | succ i ih =>
      have h : (e i.castSucc).val < (e i.succ).val := e.strictMono Fin.castSucc_lt_succ
      exact Nat.succ_le_of_lt (lt_of_le_of_lt ih h)

theorem sum_antitone_embedding_le {k n : ℕ} (hk : k ≤ n) {a : Fin n → ℝ}
    (ha : Antitone a) (e : Fin k ↪ Fin n) :
    (∑ i : Fin k, a (e i)) ≤ ∑ i : Fin k, a (Fin.castLE hk i) := by
  classical
  let s := Finset.univ.image e
  have hs : s.card = k := by simp [s, Finset.card_image_of_injective _ e.injective]
  let o := s.orderEmbOfFin hs
  have hsum : (∑ i : Fin k, a (e i)) = ∑ i : Fin k, a (o i) := by
    calc
      (∑ i : Fin k, a (e i)) = ∑ j ∈ s, a j := by
        simp [s, Finset.sum_image, e.injective.injOn]
      _ = ∑ i : Fin k, a (o i) := by
        rw [← Finset.image_orderEmbOfFin_univ s hs,
          Finset.sum_image (fun _ _ _ _ h => (s.orderEmbOfFin hs).injective h)]
  rw [hsum]
  exact Finset.sum_le_sum (fun i _ => ha (orderEmbedding_fin_val_le o i))

/-- Among all k-element selections, the sum of the first k entries of any descending
rearrangement is the attained maximum. -/
theorem isGreatest_selected_sum {k n : ℕ} (hk : k ≤ n) {a b : Fin n → ℝ}
    (ha : Antitone a) (hm : Finset.univ.val.map a = Finset.univ.val.map b) :
    IsGreatest {r : ℝ | ∃ s : Set.powersetCard (Fin n) k, r = ∑ j ∈ s.val, b j}
      (∑ i : Fin k, a (Fin.castLE hk i)) := by
  classical
  obtain ⟨e, he⟩ := exists_equiv_of_multiset_eq hm
  constructor
  · let f : Fin k ↪ Fin n := (Fin.castLEEmb hk).trans e.toEmbedding
    let s := Finset.univ.image f
    have hs : s.card = k := by simp [s, Finset.card_image_of_injective _ f.injective]
    refine ⟨⟨s, hs⟩, ?_⟩
    change (∑ i : Fin k, a (Fin.castLE hk i)) = ∑ j ∈ s, b j
    simp [s, Finset.sum_image, f.injective.injOn, f, he]
  · rintro r ⟨s, rfl⟩
    let f : Fin k ↪ Fin n := (Set.powersetCard.ofFinEmbEquiv.symm s).toEmbedding
    have hsum : (∑ j ∈ s.val, b j) = ∑ i : Fin k, b (f i) := by
      change (∑ j ∈ s.val, b j) = ∑ i : Fin k, b (s.val.orderEmbOfFin s.property i)
      conv_lhs => rw [← Finset.image_orderEmbOfFin_univ s.val s.property]
      rw [Finset.sum_image (fun _ _ _ _ h => (s.val.orderEmbOfFin s.property).injective h)]
    rw [hsum]
    have he' (j : Fin n) : b j = a (e.symm j) := by simpa using he (e.symm j)
    simp_rw [he']
    exact sum_antitone_embedding_le hk ha (f.trans e.symm.toEmbedding)

end Eden
