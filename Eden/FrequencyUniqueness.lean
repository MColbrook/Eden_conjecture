import Eden.FrequencyEvolution
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Uniqueness and the evolution law for the frequency family

Each finite pair of solution arcs lies in a compact Euclidean ball, on which
the polynomial field is Lipschitz. Mathlib's Gronwall uniqueness theorem
`ODE_solution_unique_of_mem_Icc_right` then identifies the arcs.

The proof reuses Mathlib's ODE uniqueness development (Winston Yin, building
on Gronwall inequalities by Yury Kudryashov) and
its compact-domain Lipschitz consequence of continuous differentiability.
-/

noncomputable section
open Set
namespace Eden

/-- Two solution arcs with the same initial value agree on their whole
closed time interval. Right derivatives suffice at the initial endpoint. -/
theorem frequency_solution_unique_on_Icc (c ν : ℝ) {a b : ℝ} {f g : ℝ → PhaseSpace}
    (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ t ∈ Ico a b, HasDerivWithinAt f (frequencyVectorField c ν (f t)) (Ici t) t)
    (hg : ContinuousOn g (Icc a b))
    (hg' : ∀ t ∈ Ico a b, HasDerivWithinAt g (frequencyVectorField c ν (g t)) (Ici t) t)
    (ha : f a = g a) : EqOn f g (Icc a b) := by
  have hc : IsCompact (f '' Icc a b ∪ g '' Icc a b) :=
    (isCompact_Icc.image_of_continuousOn hf).union
      (isCompact_Icc.image_of_continuousOn hg)
  obtain ⟨R, hR⟩ := hc.isBounded.exists_norm_le
  obtain ⟨K, hK⟩ := (contDiff_frequencyVectorField c ν 1).contDiffOn.exists_lipschitzOnWith
    one_ne_zero (convex_closedBall (0 : PhaseSpace) R) (isCompact_closedBall 0 R)
  have hfs : ∀ t ∈ Ico a b, f t ∈ Metric.closedBall (0 : PhaseSpace) R := by
    intro t ht
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      hR (f t) (Or.inl ⟨t, ⟨ht.1, ht.2.le⟩, rfl⟩)
  have hgs : ∀ t ∈ Ico a b, g t ∈ Metric.closedBall (0 : PhaseSpace) R := by
    intro t ht
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      hR (g t) (Or.inr ⟨t, ⟨ht.1, ht.2.le⟩, rfl⟩)
  exact ODE_solution_unique_of_mem_Icc_right
    (v := fun _ => frequencyVectorField c ν) (s := fun _ => Metric.closedBall 0 R)
    (K := K) (fun _ _ => hK) hf hf' hfs hg hg' hgs ha

theorem continuousOn_frequencyEvolution (c ν : ℝ) (p : PhaseSpace) :
    ContinuousOn (fun t => frequencyEvolution c ν t p) (Ici 0) :=
  fun _ ht => (hasDerivAt_frequencyEvolution c ν ht p).continuousAt.continuousWithinAt

/-- The explicit evolution is the unique global forward solution, allowing
the usual right-sided differential equation at time zero. -/
theorem frequencyEvolution_unique (c ν : ℝ) (p : PhaseSpace) {f : ℝ → PhaseSpace}
    (hf : ContinuousOn f (Ici 0))
    (hf' : ∀ t, 0 ≤ t → HasDerivWithinAt f (frequencyVectorField c ν (f t)) (Ici t) t)
    (h0 : f 0 = p) : EqOn f (fun t => frequencyEvolution c ν t p) (Ici 0) := by
  intro t ht
  have hu := frequency_solution_unique_on_Icc c ν (a := 0) (b := t)
    (hf.mono Icc_subset_Ici_self) (fun τ hτ => hf' τ hτ.1)
    ((continuousOn_frequencyEvolution c ν p).mono Icc_subset_Ici_self)
    (fun τ hτ => (hasDerivAt_frequencyEvolution c ν hτ.1 p).hasDerivWithinAt)
    (by simpa using h0)
  exact hu ⟨ht, le_rfl⟩

/-- The explicit solutions have the semigroup law for every ambient initial
point and all nonnegative times. -/
theorem frequencyEvolution_add (c ν : ℝ) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    (p : PhaseSpace) :
    frequencyEvolution c ν (s + t) p = frequencyEvolution c ν t (frequencyEvolution c ν s p) := by
  have hd : ∀ τ, 0 ≤ τ → HasDerivAt (fun u => frequencyEvolution c ν (s + u) p)
      (frequencyVectorField c ν (frequencyEvolution c ν (s + τ) p)) τ := by
    intro τ hτ
    have h := (hasDerivAt_frequencyEvolution c ν (add_nonneg hs hτ) p).scomp τ
      ((hasDerivAt_id τ).const_add s)
    simpa only [Function.comp_def, one_smul] using h
  exact frequencyEvolution_unique c ν (frequencyEvolution c ν s p)
    (fun τ hτ => (hd τ hτ).continuousAt.continuousWithinAt)
    (fun τ hτ => (hd τ hτ).hasDerivWithinAt) (by simp) ht

end Eden
