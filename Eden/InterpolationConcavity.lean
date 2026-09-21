import Eden.LogarithmicInterpolation
import Mathlib.Analysis.Convex.Function

/-!
# Concavity of the partial-sum interpolants

On the complete dimension interval `[0,5]`, a descending spectrum has a
concave partial-sum interpolant. The proof expresses it as a linear function
plus nonnegative multiples of the concave functions `min d k`. Equal entries
and zero entries require no additional assumptions.

The argument reuses `ConcaveOn.inf`, `ConcaveOn.smul`, `ConcaveOn.add` and
`ConcaveOn.congr` from Mathlib's `Analysis.Convex.Function`, authored by
Alexander Bentkamp and François Dupuis. The logarithmic identification and
the ordering of the singular values and Lyapunov exponents come from
the preceding modules of this formalisation.
-/

noncomputable section
open Set
namespace Eden

private theorem singularWeight_eq_min_sub (d : ℝ) (i : ℕ) :
    singularWeight i d = min d (i + 1) - min d i := by
  unfold singularWeight
  by_cases hdi : d ≤ i
  · rw [max_eq_left (by linarith), min_eq_left hdi,
      min_eq_left (show d ≤ (i : ℝ) + 1 by linarith)]
    norm_num
  · have hid : (i : ℝ) ≤ d := le_of_lt (lt_of_not_ge hdi)
    rw [max_eq_right (by linarith), min_eq_right hid]
    by_cases hdi' : d ≤ (i : ℝ) + 1
    · rw [min_eq_left hdi', min_eq_right (show d - (i : ℝ) ≤ 1 by linarith)]
    · rw [min_eq_right (le_of_lt (lt_of_not_ge hdi')),
        min_eq_left (show 1 ≤ d - (i : ℝ) by linarith)]
      ring

/-- A finite summation-by-parts identity on the full dimension interval. -/
theorem spectrumInterpolation_eq_min_sum (a : Fin 5 → ℝ) {d : ℝ}
    (hd : d ∈ Icc 0 5) :
    spectrumInterpolation a d = a 4 * d +
      (a 0 - a 1) * min d 1 + (a 1 - a 2) * min d 2 +
      (a 2 - a 3) * min d 3 + (a 3 - a 4) * min d 4 := by
  unfold spectrumInterpolation
  simp only [singularWeight_eq_min_sub]
  norm_num [Fin.sum_univ_succ, min_eq_right hd.1, min_eq_left hd.2]
  simp only [show Fin.succ (2 : Fin 4) = (3 : Fin 5) from rfl,
    show (Fin.succ (2 : Fin 3)).succ = (4 : Fin 5) from rfl]
  ring

private theorem concaveOn_min_dimension (k : ℝ) :
    ConcaveOn ℝ (Icc (0 : ℝ) 5) (fun d => min d k) := by
  exact (concaveOn_id (convex_Icc 0 5)).inf
    (concaveOn_const k (convex_Icc 0 5))

private theorem concaveOn_linear_dimension (a : ℝ) :
    ConcaveOn ℝ (Icc (0 : ℝ) 5) (fun d => a * d) := by
  refine ⟨convex_Icc 0 5, ?_⟩
  intro x hx y hy r s hr hs hrs
  simp only [smul_eq_mul]
  exact le_of_eq (by ring)

/-- Concavity includes both endpoints and allows repeated or zero slopes. -/
theorem concaveOn_spectrumInterpolation {a : Fin 5 → ℝ} (ha : Antitone a) :
    ConcaveOn ℝ (Icc (0 : ℝ) 5) (spectrumInterpolation a) := by
  have h01 : 0 ≤ a 0 - a 1 := sub_nonneg.mpr (ha (by decide))
  have h12 : 0 ≤ a 1 - a 2 := sub_nonneg.mpr (ha (by decide))
  have h23 : 0 ≤ a 2 - a 3 := sub_nonneg.mpr (ha (by decide))
  have h34 : 0 ≤ a 3 - a 4 := sub_nonneg.mpr (ha (by decide))
  have h := ((((concaveOn_linear_dimension (a 4)).add
    ((concaveOn_min_dimension 1).smul h01)).add
    ((concaveOn_min_dimension 2).smul h12)).add
    ((concaveOn_min_dimension 3).smul h23)).add
    ((concaveOn_min_dimension 4).smul h34)
  apply h.congr
  intro d hd
  simpa only [Pi.add_apply, smul_eq_mul] using
    (spectrumInterpolation_eq_min_sum a hd).symm

/-- Concavity of the finite-time logarithmic singular-value function. -/
theorem concaveOn_log_singularValueFunction (c : ℝ) {t : ℝ} (ht : 0 < t)
    (p : PhaseSpace) :
    ConcaveOn ℝ (Icc (0 : ℝ) 5) (fun d => Real.log
      (singularValueFunction (fderiv ℝ (evolution c t) p).toLinearMap d) / t) := by
  apply (concaveOn_spectrumInterpolation
    (normalizedLogSingularValues_antitone c ht p)).congr
  intro d hd
  exact (log_singularValueFunction_div_time c ht p d).symm

/-- Concavity of the partial-sum interpolant of the limiting exponents. -/
theorem concaveOn_lyapunovExponent_interpolation (c : ℝ) (p : PhaseSpace) :
    ConcaveOn ℝ (Icc (0 : ℝ) 5) (spectrumInterpolation (lyapunovExponent c p)) :=
  concaveOn_spectrumInterpolation (lyapunovExponent_antitone c p)

end Eden
