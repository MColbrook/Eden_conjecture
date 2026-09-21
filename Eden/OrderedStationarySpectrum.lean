import Eden.StationaryFactors
import Eden.SingularValues
import Mathlib.Data.List.Sort
import Mathlib.Order.Fin.Basic

/-!
# Ordered stationary spectra

Mathlib's uniqueness of sorted lists identifies the descending spectrum from the
complete multiset, without discarding multiplicities or ties. The paper's
indices 1,...,5 correspond to the Fin 5 indices 0,...,4 below.
-/

noncomputable section
namespace Eden

theorem antitone_eq_of_multiset_eq {n : ℕ} {a b : Fin n → ℝ}
    (ha : Antitone a) (hb : Antitone b)
    (hm : Finset.univ.val.map a = Finset.univ.val.map b) : a = b := by
  rw [Fin.univ_val_map, Fin.univ_val_map] at hm
  apply List.ofFn_injective
  exact (Multiset.coe_eq_coe.mp hm).eq_of_sortedGE ha.sortedGE_ofFn hb.sortedGE_ofFn

theorem singularValues_on_torus {c t : ℝ} (hc : 0 ≤ c) (ht : 0 ≤ t)
    {p : PhaseSpace} (hp : p ∈ torus) :
    (fun i : Fin 5 => (fderiv ℝ (evolution c t) p).toLinearMap.singularValues i) =
      ![Real.exp (2 * t), Real.exp (2 * t), 1, 1, Real.exp (-c * t)] := by
  let A := (fderiv ℝ (evolution c t) p).toLinearMap
  have hhigh : 1 ≤ Real.exp (2 * t) := Real.one_le_exp_iff.mpr (by positivity)
  have hlow : Real.exp (-c * t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  apply antitone_eq_of_multiset_eq
  · exact fun i j hij => A.singularValues_antitone hij
  · rw [Fin.antitone_iff_succ_le]
    intro i
    fin_cases i <;> simp_all
  · rw [singularValues_fderiv_evolution c ht p, derivativeFactors_on_torus c ht hp]
    simp only [Fin.univ_val_map, List.ofFn_succ, List.ofFn_zero,
      Matrix.cons_val_zero, Matrix.cons_val_succ]
    apply Multiset.coe_eq_coe.mpr
    exact (List.Perm.swap _ _ _).cons _

theorem singularValues_at_origin {c t : ℝ} (hc : 2 ≤ c) (ht : 0 ≤ t) :
    (fun i : Fin 5 => (fderiv ℝ (evolution c t) 0).toLinearMap.singularValues i) =
      ![Real.exp (-2 * t), Real.exp (-2 * t), Real.exp (-2 * t),
        Real.exp (-2 * t), Real.exp (-c * t)] := by
  let A := (fderiv ℝ (evolution c t) 0).toLinearMap
  have hlow : Real.exp (-c * t) ≤ Real.exp (-2 * t) := Real.exp_le_exp.mpr (by nlinarith)
  apply antitone_eq_of_multiset_eq
  · exact fun i j hij => A.singularValues_antitone hij
  · rw [Fin.antitone_iff_succ_le]
    intro i
    fin_cases i <;> simp_all
  · rw [singularValues_fderiv_evolution c ht 0, derivativeFactors_at_origin c ht]

end Eden
