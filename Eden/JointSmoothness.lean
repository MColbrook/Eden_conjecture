import Eden.InitialDerivative

/-!
# Joint smoothness in time and initial position

The explicit solution extends smoothly to a neighbourhood of every point
with nonnegative time. Positivity is checked at that point before applying
Mathlib's local square-root and division calculus. Thus the statement at
time zero includes a smooth local extension across the time boundary.
-/

noncomputable section
namespace Eden

theorem contDiffAt_amplitudeSq_joint {t s : ℝ} (hD : 0 < radialDiscriminant t s)
    (n : WithTop ℕ∞) :
    ContDiffAt ℝ n (fun u : ℝ × ℝ => amplitudeSq u.1 u.2) (t, s) := by
  have hd : ContDiffAt ℝ n (fun u : ℝ × ℝ => radialDiscriminant u.1 u.2) (t, s) := by
    unfold radialDiscriminant
    fun_prop
  have hr := hd.sqrt (ne_of_gt hD)
  have hR : Real.sqrt (radialDiscriminant t s) ≠ 0 := (Real.sqrt_pos.2 hD).ne'
  have hR1 : Real.sqrt (radialDiscriminant t s) + 1 ≠ 0 := by positivity
  unfold amplitudeSq
  apply ContDiffAt.div _ hr hR
  apply ContDiffAt.add contDiffAt_const
  apply ContDiffAt.div _ (hr.add contDiffAt_const) hR1
  fun_prop

theorem contDiffAt_planarAmplitude_joint {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s)
    (n : WithTop ℕ∞) :
    ContDiffAt ℝ n (fun u : ℝ × ℝ => planarAmplitude u.1 u.2) (t, s) :=
  (contDiffAt_amplitudeSq_joint (radialDiscriminant_pos ht s) n).sqrt
    (amplitudeSq_pos ht hs).ne'

/-- Smoothness in time and all five ambient coordinates jointly, at every
nonnegative time, with no restriction on the initial point or parameter. -/
theorem contDiffAt_evolution_joint (c : ℝ) {t : ℝ} (ht : 0 ≤ t) (p : PhaseSpace)
    (n : WithTop ℕ∞) :
    ContDiffAt ℝ n (fun u : ℝ × PhaseSpace => evolution c u.1 u.2) (t, p) := by
  have hamp (i j : Fin 5) : ContDiffAt ℝ n
      (fun u : ℝ × PhaseSpace => planarAmplitude u.1 (u.2 i ^ 2 + u.2 j ^ 2)) (t, p) := by
    have hr : ContDiffAt ℝ n
        (fun u : ℝ × PhaseSpace => (u.1, u.2 i ^ 2 + u.2 j ^ 2)) (t, p) := by
      fun_prop
    have h := (contDiffAt_planarAmplitude_joint ht
      (add_nonneg (sq_nonneg (p i)) (sq_nonneg (p j))) n).comp (t, p) hr
    exact h
  rw [contDiffAt_piLp]
  intro i
  fin_cases i <;> simp [evolution, planarX, planarY] <;> fun_prop

theorem contDiffOn_evolution_joint (c : ℝ) (n : WithTop ℕ∞) :
    ContDiffOn ℝ n (fun u : ℝ × PhaseSpace => evolution c u.1 u.2)
      {u | 0 ≤ u.1} := by
  intro u hu
  exact (contDiffAt_evolution_joint c hu u.2 n).contDiffWithinAt

end Eden
