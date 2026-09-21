import Eden.OrderedStationarySpectrum
import Mathlib.Data.Multiset.Sort
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Stability of descending rearrangement

Threshold counts compare corresponding entries of descending lists. The argument
counts indices, so equal values retain their full multiplicity. It proves the
maximum-norm bound with constant one for every finite length.

The construction reuses Mathlib's multiset sorting API by Mario Carneiro, its
sorted-list uniqueness theorem and finite interval cardinalities.
-/

noncomputable section
open Set Filter
open scoped Topology
namespace Eden

theorem card_filter_eq_of_multiset_eq {n : ℕ} {f g : Fin n → ℝ}
    (hm : Finset.univ.val.map f = Finset.univ.val.map g) (p : ℝ → Prop)
    [DecidablePred p] :
    (Finset.univ.filter (fun i => p (f i))).card =
      (Finset.univ.filter (fun i => p (g i))).card := by
  have h := congrArg (Multiset.countP p) hm
  simpa only [Multiset.countP_map, Finset.card, Finset.filter_val] using h

/-- Pointwise upper bounds survive descending rearrangement. -/
theorem antitone_le_of_matched_le {n : ℕ} {a b f g : Fin n → ℝ} {δ : ℝ}
    (ha : Antitone a) (hb : Antitone b)
    (haf : Finset.univ.val.map a = Finset.univ.val.map f)
    (hbg : Finset.univ.val.map b = Finset.univ.val.map g)
    (hfg : ∀ j, f j ≤ g j + δ) (i : Fin n) : a i ≤ b i + δ := by
  classical
  by_contra h
  have hlt : b i + δ < a i := lt_of_not_ge h
  have hleft : i.val + 1 ≤ (Finset.univ.filter (fun j => a i ≤ a j)).card := by
    calc
      i.val + 1 = (Finset.Iic i).card := (Fin.card_Iic i).symm
      _ ≤ _ := Finset.card_le_card (by
        intro j hj
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, ha (Finset.mem_Iic.mp hj)⟩)
  have hright : (Finset.univ.filter (fun j => b i < b j)).card ≤ i.val := by
    calc
      _ ≤ (Finset.Iio i).card := Finset.card_le_card (by
        intro j hj
        apply Finset.mem_Iio.mpr
        by_contra hji
        exact (not_lt_of_ge (hb (le_of_not_gt hji))) (Finset.mem_filter.mp hj).2)
      _ = i.val := Fin.card_Iio i
  have hmiddle : (Finset.univ.filter (fun j => a i ≤ f j)).card ≤
      (Finset.univ.filter (fun j => b i < g j)).card := by
    apply Finset.card_le_card
    intro j hj
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ j, ?_⟩
    have hj' := (Finset.mem_filter.mp hj).2
    have := hfg j
    linarith
  rw [card_filter_eq_of_multiset_eq haf (fun x => a i ≤ x)] at hleft
  rw [card_filter_eq_of_multiset_eq hbg (fun x => b i < x)] at hright
  omega

theorem antitone_dist_le_of_matched_dist_le {n : ℕ} {a b f g : Fin n → ℝ} {δ : ℝ}
    (ha : Antitone a) (hb : Antitone b)
    (haf : Finset.univ.val.map a = Finset.univ.val.map f)
    (hbg : Finset.univ.val.map b = Finset.univ.val.map g)
    (hfg : ∀ j, dist (f j) (g j) ≤ δ) (i : Fin n) : dist (a i) (b i) ≤ δ := by
  have hf : ∀ j, f j ≤ g j + δ := by
    intro j
    have := (abs_le.mp (show |f j - g j| ≤ δ by simpa [Real.dist_eq] using hfg j)).2
    linarith
  have hg : ∀ j, g j ≤ f j + δ := by
    intro j
    have := (abs_le.mp (show |f j - g j| ≤ δ by simpa [Real.dist_eq] using hfg j)).1
    linarith
  rw [Real.dist_eq, abs_le]
  constructor
  · have := antitone_le_of_matched_le hb ha hbg haf hg i
    linarith
  · have := antitone_le_of_matched_le ha hb haf hbg hf i
    linarith

/-- Descending rearrangement of a finite real vector, retaining duplicates. -/
def descending {n : ℕ} (f : Fin n → ℝ) (i : Fin n) : ℝ :=
  ((Finset.univ.val.map f).sort (· ≥ ·)).get
    ⟨i.val, by simp⟩

theorem descending_antitone {n : ℕ} (f : Fin n → ℝ) : Antitone (descending f) := by
  intro i j hij
  exact (Multiset.pairwise_sort (Finset.univ.val.map f) (· ≥ ·)).sortedGE.antitone_get
    (show (⟨i.val, by simp⟩ : Fin ((Finset.univ.val.map f).sort (· ≥ ·)).length) ≤
      ⟨j.val, by simp⟩ from hij)

theorem ofFn_descending {n : ℕ} (f : Fin n → ℝ) :
    List.ofFn (descending f) = (Finset.univ.val.map f).sort (· ≥ ·) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp [descending]

theorem multiset_descending {n : ℕ} (f : Fin n → ℝ) :
    Finset.univ.val.map (descending f) = Finset.univ.val.map f := by
  rw [Fin.univ_val_map, ofFn_descending, Multiset.sort_eq]

/-- Descending sorting is 1-Lipschitz for the maximum metric on finite vectors. -/
theorem lipschitzWith_descending (n : ℕ) :
    LipschitzWith 1 (descending : (Fin n → ℝ) → (Fin n → ℝ)) := by
  apply LipschitzWith.of_dist_le_mul
  intro f g
  simp only [NNReal.coe_one, one_mul]
  apply (dist_pi_le_iff dist_nonneg).mpr
  exact antitone_dist_le_of_matched_dist_le
    (descending_antitone f) (descending_antitone g)
    (multiset_descending f) (multiset_descending g) (dist_le_pi_dist f g)

theorem continuous_descending (n : ℕ) :
    Continuous (descending : (Fin n → ℝ) → (Fin n → ℝ)) :=
  (lipschitzWith_descending n).continuous

theorem tendsto_descending {n : ℕ} {f : ℝ → Fin n → ℝ} {a : Fin n → ℝ}
    (h : ∀ i, Tendsto (fun t => f t i) atTop (𝓝 (a i))) :
    Tendsto (fun t => descending (f t)) atTop (𝓝 (descending a)) :=
  (continuous_descending n).continuousAt.tendsto.comp (tendsto_pi_nhds.mpr h)

end Eden
