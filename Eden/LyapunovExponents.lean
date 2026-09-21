import Eden.FactorLimits
import Eden.Sorting

/-!
# Existence of the ordered Lyapunov exponents

The exponents are limits of logarithms of the ambient Euclidean
singular values. Positivity and descending order identify the finite-time
logarithmic spectrum with the descending rearrangement of the five proved
factor rates. Continuity of this rearrangement then gives every limit,
including repeated and zero exponents, at every ambient initial point.
The mathematical indices 1,...,5 correspond to Fin 5 indices 0,...,4.
-/

noncomputable section
open Set Filter
open scoped Topology
namespace Eden

/-- The logarithm of each ordered singular value divided by real time. -/
def normalizedLogSingularValues (c t : ℝ) (p : PhaseSpace) : Fin 5 → ℝ :=
  fun i => Real.log ((fderiv ℝ (evolution c t) p).toLinearMap.singularValues i) / t

theorem singularValues_evolution_pos (c : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (p : PhaseSpace) (i : Fin 5) :
    0 < (fderiv ℝ (evolution c t) p).toLinearMap.singularValues i := by
  exact (fderiv ℝ (evolution c t) p).toLinearMap.injective_iff_forall_lt_finrank_singularValues_pos.mp
    (fderiv_evolution_bijective c ht p).1 i
    (by simpa only [finrank_euclideanSpace_fin] using i.isLt)

theorem normalizedLogSingularValues_antitone (c : ℝ) {t : ℝ} (ht : 0 < t)
    (p : PhaseSpace) : Antitone (normalizedLogSingularValues c t p) := by
  intro i j hij
  exact div_le_div_of_nonneg_right
    (Real.log_le_log (singularValues_evolution_pos c ht.le p j)
      ((fderiv ℝ (evolution c t) p).toLinearMap.singularValues_antitone hij)) ht.le

theorem normalizedLogSingularValues_eq_descending (c : ℝ) {t : ℝ} (ht : 0 < t)
    (p : PhaseSpace) :
    normalizedLogSingularValues c t p =
      descending (fun i => Real.log (derivativeFactors c t p i) / t) := by
  apply antitone_eq_of_multiset_eq
    (normalizedLogSingularValues_antitone c ht p) (descending_antitone _)
  have h := congrArg (Multiset.map (fun x : ℝ => Real.log x / t))
    (singularValues_fderiv_evolution c ht.le p)
  have hm : Finset.univ.val.map (normalizedLogSingularValues c t p) =
      Finset.univ.val.map (fun i => Real.log (derivativeFactors c t p i) / t) := by
    change Finset.univ.val.map (fun i : Fin 5 => Real.log
      ((fderiv ℝ (evolution c t) p).toLinearMap.singularValues i) / t) = _
    simpa only [Multiset.map_map, Function.comp_def] using h
  exact hm.trans (multiset_descending _).symm

theorem tendsto_normalizedLogSingularValues (c : ℝ) (p : PhaseSpace) :
    Tendsto (fun t => normalizedLogSingularValues c t p) atTop
      (𝓝 (descending (factorExponents c p))) := by
  apply (tendsto_descending (tendsto_log_derivativeFactors_div c p)).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  exact (normalizedLogSingularValues_eq_descending c ht p).symm

/-- The real-time limit, with existence established in the next theorem. -/
def lyapunovExponent (c : ℝ) (p : PhaseSpace) (i : Fin 5) : ℝ :=
  limUnder atTop (fun t => normalizedLogSingularValues c t p i)

theorem lyapunovExponent_eq_descending (c : ℝ) (p : PhaseSpace) (i : Fin 5) :
    lyapunovExponent c p i = descending (factorExponents c p) i :=
  (tendsto_pi_nhds.mp (tendsto_normalizedLogSingularValues c p) i).limUnder_eq

/-- Every ordered singular-value exponent exists, for every ambient point. -/
theorem tendsto_lyapunovExponent (c : ℝ) (p : PhaseSpace) (i : Fin 5) :
    Tendsto (fun t => Real.log
      ((fderiv ℝ (evolution c t) p).toLinearMap.singularValues i) / t) atTop
      (𝓝 (lyapunovExponent c p i)) := by
  rw [lyapunovExponent_eq_descending]
  exact tendsto_pi_nhds.mp (tendsto_normalizedLogSingularValues c p) i

theorem lyapunovExponent_antitone (c : ℝ) (p : PhaseSpace) :
    Antitone (lyapunovExponent c p) := by
  intro i j hij
  rw [lyapunovExponent_eq_descending, lyapunovExponent_eq_descending]
  exact descending_antitone (factorExponents c p) hij

theorem multiset_lyapunovExponent (c : ℝ) (p : PhaseSpace) :
    Finset.univ.val.map (lyapunovExponent c p) = Finset.univ.val.map (factorExponents c p) := by
  have heq : lyapunovExponent c p = descending (factorExponents c p) :=
    funext (lyapunovExponent_eq_descending c p)
  rw [heq]
  exact multiset_descending (factorExponents c p)

end Eden
