import Eden.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Tactic

/-!
# Polynomial coordinates and degree of the vector field

Evaluation of the five multivariate polynomials below gives the vector field on
real Euclidean space. Its degree is the maximum of their total degrees. The
upper bound follows from the degree operations; the coefficient of the fifth
power of the first coordinate supplies the lower bound.

The multivariate polynomial degree API is due to Johannes Hölzl, Johan Commelin
and Mario Carneiro in Mathlib.
-/

noncomputable section
namespace Eden
open MvPolynomial

/-- Polynomial squared radius of a pair of ambient coordinates. -/
def radiusPolynomial (i j : Fin 5) : MvPolynomial (Fin 5) ℝ := X i ^ 2 + X j ^ 2

/-- The polynomial radial multiplier in a pair of ambient coordinates. -/
def ratePolynomial (i j : Fin 5) : MvPolynomial (Fin 5) ℝ :=
  -(radiusPolynomial i j - C 1) * (radiusPolynomial i j - C 2)

/-- The five polynomial coordinates of the vector field. -/
def vectorFieldPolynomial (c : ℝ) : Fin 5 → MvPolynomial (Fin 5) ℝ :=
  ![ratePolynomial 0 1 * X 0 - X 1,
    ratePolynomial 0 1 * X 1 + X 0,
    ratePolynomial 2 3 * X 2 - C (Real.sqrt 2) * X 3,
    ratePolynomial 2 3 * X 3 + C (Real.sqrt 2) * X 2,
    C (-c) * X 4]

theorem eval_vectorFieldPolynomial (c : ℝ) (p : PhaseSpace) (i : Fin 5) :
    eval (fun j => p j) (vectorFieldPolynomial c i) = vectorField c p i := by
  fin_cases i <;>
    simp [vectorFieldPolynomial, ratePolynomial, radiusPolynomial, vectorField,
      radiusSq₁, radiusSq₂, q]

theorem totalDegree_radiusPolynomial_le (i j : Fin 5) :
    (radiusPolynomial i j).totalDegree ≤ 2 := by
  exact (totalDegree_add _ _).trans (by simp)

theorem totalDegree_ratePolynomial_le (i j : Fin 5) :
    (ratePolynomial i j).totalDegree ≤ 4 := by
  have h₁ := (totalDegree_sub_C_le (radiusPolynomial i j) (1 : ℝ)).trans
    (totalDegree_radiusPolynomial_le i j)
  have h₂ := (totalDegree_sub_C_le (radiusPolynomial i j) (2 : ℝ)).trans
    (totalDegree_radiusPolynomial_le i j)
  have h := totalDegree_mul (-(radiusPolynomial i j - C (1 : ℝ)))
    (radiusPolynomial i j - C (2 : ℝ))
  rw [totalDegree_neg] at h
  exact h.trans (by omega)

theorem totalDegree_vectorFieldPolynomial_le (c : ℝ) (i : Fin 5) :
    (vectorFieldPolynomial c i).totalDegree ≤ 5 := by
  have hr (i j k : Fin 5) : (ratePolynomial i j * X k).totalDegree ≤ 5 := by
    have h := totalDegree_mul (ratePolynomial i j) (X k)
    have h' := totalDegree_ratePolynomial_le i j
    simp only [totalDegree_X] at h
    omega
  have hl (a : ℝ) (i : Fin 5) : (C a * X i : MvPolynomial (Fin 5) ℝ).totalDegree ≤ 1 := by
    exact (totalDegree_mul _ _).trans (by simp)
  fin_cases i
  · exact (totalDegree_sub _ _).trans (max_le (hr 0 1 0) (by simp))
  · exact (totalDegree_add _ _).trans (max_le (hr 0 1 1) (by simp))
  · exact (totalDegree_sub _ _).trans (max_le (hr 2 3 2) ((hl _ _).trans (by omega)))
  · exact (totalDegree_add _ _).trans (max_le (hr 2 3 3) ((hl _ _).trans (by omega)))
  · exact (hl _ _).trans (by omega)

theorem coeff_vectorFieldPolynomial_first (c : ℝ) :
    (vectorFieldPolynomial c 0).coeff (Finsupp.single 0 5) = -1 := by
  have he : vectorFieldPolynomial c 0 =
      -(X 0 ^ 5) - C 2 * (X 0 ^ 3 * X 1 ^ 2) - X 0 * X 1 ^ 4 +
        C 3 * X 0 ^ 3 + C 3 * (X 0 * X 1 ^ 2) - C 2 * X 0 - X 1 := by
    norm_num [vectorFieldPolynomial, ratePolynomial, radiusPolynomial, map_ofNat]
    ring
  rw [he]
  simp only [coeff_sub, coeff_add, coeff_neg, coeff_C_mul]
  simp only [X_pow_eq_monomial]
  simp only [X, monomial_mul, coeff_monomial]
  norm_num [Finsupp.ext_iff, Fin.forall_fin_succ]

theorem totalDegree_vectorFieldPolynomial_first (c : ℝ) :
    (vectorFieldPolynomial c 0).totalDegree = 5 := by
  apply le_antisymm (totalDegree_vectorFieldPolynomial_le c 0)
  have h := le_totalDegree (mem_support_iff.mpr
    (show (vectorFieldPolynomial c 0).coeff (Finsupp.single 0 5) ≠ 0 by
      rw [coeff_vectorFieldPolynomial_first]; norm_num))
  simpa using h

/-- The degree of the polynomial vector field is exactly five, for every real value
of its parameter. -/
theorem vectorFieldPolynomial_degree (c : ℝ) :
    Finset.univ.sup (fun i => (vectorFieldPolynomial c i).totalDegree) = 5 := by
  apply le_antisymm
  · exact Finset.sup_le (fun i _ => totalDegree_vectorFieldPolynomial_le c i)
  · simpa only [totalDegree_vectorFieldPolynomial_first] using
      (Finset.le_sup (f := fun i => (vectorFieldPolynomial c i).totalDegree)
        (Finset.mem_univ (0 : Fin 5)))

end Eden
