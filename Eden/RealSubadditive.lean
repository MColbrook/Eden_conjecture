import Eden.GlobalGrowth
import Mathlib.Analysis.Subadditive
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# A real-time subadditive limit

The induction and infimum argument follow Sébastien Gouëzel's discrete Fekete
proof in Mathlib.Analysis.Subadditive (Apache 2.0). The remainder estimate below
extends the argument to every nonnegative real time.
-/

noncomputable section
open Set Filter Topology
namespace Eden

theorem real_subadditive_mul_add_le {f : ℝ → ℝ}
    (hsub : ∀ s t, 0 ≤ s → 0 ≤ t → f (s + t) ≤ f s + f t)
    {T r : ℝ} (hT : 0 ≤ T) (hr : 0 ≤ r) (m : ℕ) :
    f ((m : ℝ) * T + r) ≤ (m : ℝ) * f T + f r := by
  induction m with
  | zero => simp
  | succ m ih =>
    calc
      f (((m + 1 : ℕ) : ℝ) * T + r) = f (T + ((m : ℝ) * T + r)) := by
        congr 1
        push_cast
        ring
      _ ≤ f T + f ((m : ℝ) * T + r) :=
        hsub _ _ hT (add_nonneg (mul_nonneg (Nat.cast_nonneg _) hT) hr)
      _ ≤ f T + ((m : ℝ) * f T + f r) := by linarith
      _ = _ := by push_cast; ring

/-- The comparison estimate covers all positive real times, including t<T. -/
theorem real_subadditive_div_le {f : ℝ → ℝ} {C : ℝ}
    (hsub : ∀ s t, 0 ≤ s → 0 ≤ t → f (s + t) ≤ f s + f t)
    (hC : 0 ≤ C) (hbound : ∀ t, 0 ≤ t → |f t| ≤ C * t)
    {T t : ℝ} (hT : 0 < T) (ht : 0 < t) :
    f t / t ≤ f T / T + (C + |f T / T|) * T / t := by
  let m : ℕ := ⌊t / T⌋₊
  let r : ℝ := t - (m : ℝ) * T
  have hm : (m : ℝ) * T ≤ t :=
    (le_div_iff₀ hT).mp (Nat.floor_le (div_nonneg ht.le hT.le))
  have hmt : t < ((m : ℝ) + 1) * T :=
    (div_lt_iff₀ hT).mp (Nat.lt_floor_add_one (t / T))
  have hr : 0 ≤ r := sub_nonneg.mpr hm
  have hrT : r ≤ T := by dsimp [r]; linarith
  have heq : (m : ℝ) * T + r = t := by dsimp [r]; ring
  have hs := real_subadditive_mul_add_le hsub hT.le hr m
  rw [heq] at hs
  have hb : f r ≤ C * r := (le_abs_self _).trans (hbound r hr)
  have ha : T * (f T / T) = f T := mul_div_cancel₀ _ hT.ne'
  have he : r * (C - f T / T) ≤ T * (C + |f T / T|) := by
    calc
      _ ≤ r * (C + |f T / T|) :=
        mul_le_mul_of_nonneg_left (by linarith [neg_le_abs (f T / T)]) hr
      _ ≤ _ := mul_le_mul_of_nonneg_right hrT (add_nonneg hC (abs_nonneg _))
  apply (div_le_iff₀ ht).2
  have hcancel : ((C + |f T / T|) * T / t) * t =
      (C + |f T / T|) * T := div_mul_cancel₀ _ ht.ne'
  have hmul := congrArg (fun x : ℝ => (m : ℝ) * x) ha
  dsimp only [r] at hs hb he
  nlinarith

theorem real_subadditive_eventually_div_lt {f : ℝ → ℝ} {C : ℝ}
    (hsub : ∀ s t, 0 ≤ s → 0 ≤ t → f (s + t) ≤ f s + f t)
    (hC : 0 ≤ C) (hbound : ∀ t, 0 ≤ t → |f t| ≤ C * t)
    {T L : ℝ} (hT : 0 < T) (hL : f T / T < L) :
    ∀ᶠ t : ℝ in atTop, f t / t < L := by
  have hlim : Tendsto (fun t : ℝ => f T / T + (C + |f T / T|) * T / t)
      atTop (𝓝 (f T / T)) := by
    simpa only [add_zero] using
      (tendsto_const_nhds.add (tendsto_const_nhds.div_atTop tendsto_id) :
        Tendsto (fun t : ℝ => f T / T + (C + |f T / T|) * T / t)
          atTop (𝓝 (f T / T + 0)))
  filter_upwards [hlim.eventually (gt_mem_nhds hL), eventually_gt_atTop (0 : ℝ)]
    with t ht hpos
  exact (real_subadditive_div_le hsub hC hbound hT hpos).trans_lt ht

/-- Fekete's formula through all real times, with an explicit linear bound. -/
theorem tendsto_real_subadditive_div {f : ℝ → ℝ} {C : ℝ}
    (hsub : ∀ s t, 0 ≤ s → 0 ≤ t → f (s + t) ≤ f s + f t)
    (hC : 0 ≤ C) (hbound : ∀ t, 0 ≤ t → |f t| ≤ C * t) :
    Tendsto (fun t : ℝ => f t / t) atTop
      (𝓝 (sInf ((fun T : ℝ => f T / T) '' Ioi 0))) := by
  have hne : ((fun T : ℝ => f T / T) '' Ioi 0).Nonempty :=
    ⟨f 1 / 1, 1, (show (1 : ℝ) ∈ Ioi 0 by norm_num), rfl⟩
  have hbelow : BddBelow ((fun T : ℝ => f T / T) '' Ioi 0) := by
    refine ⟨-C, ?_⟩
    rintro x ⟨T, hT, rfl⟩
    apply (le_div_iff₀ hT).2
    have hb := (abs_le.mp (hbound T hT.le)).1
    linarith
  refine tendsto_order.2 ⟨fun l hl => ?_, fun L hL => ?_⟩
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    exact hl.trans_le (csInf_le hbelow ⟨t, ht, rfl⟩)
  · obtain ⟨x, ⟨T, hT, rfl⟩, hx⟩ := exists_lt_of_csInf_lt hne hL
    exact real_subadditive_eventually_div_lt hsub hC hbound hT hx

end Eden
