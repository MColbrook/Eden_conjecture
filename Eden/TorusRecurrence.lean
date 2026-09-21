import Eden.TorusAngles
import Eden.DerivativeFrames
import Eden.Uniqueness
import Mathlib.Topology.MetricSpace.Cauchy

/-!
# Recurrence of every torus point

The torus flow preserves Euclidean distances. A convergent subsequence of its
integer-time orbit therefore gives returns after every prescribed time. The
proof uses IsCompact.tendsto_subseq from Mathlib's Sequences file by Jan-David
Salchow, Patrick Massot and Yury Kudryashov, and the metric Cauchy criterion
from its Cauchy file by Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario
Carneiro and Sébastien Gouëzel (Apache 2.0).
-/

noncomputable section
open Set Filter Topology
namespace Eden

/-- On T the flow is the ambient angular isometry, at every real time. -/
theorem evolution_eq_angularRotation_on_torus (c t : ℝ) {p : PhaseSpace}
    (hp : p ∈ torus) : evolution c t p = angularRotation t p := by
  have h₁ : p 0 ^ 2 + p 1 ^ 2 = 1 := hp.1
  have h₂ : p 2 ^ 2 + p 3 ^ 2 = 1 := hp.2.1
  ext i
  fin_cases i <;> simp [evolution, angularRotation, rotateBlocks,
    planarX, planarY, h₁, h₂, planarAmplitude_at_one_all, hp.2.2] <;> ring

theorem dist_evolution_torus (c t : ℝ) {p q : PhaseSpace}
    (hp : p ∈ torus) (hq : q ∈ torus) :
    dist (evolution c t p) (evolution c t q) = dist p q := by
  rw [evolution_eq_angularRotation_on_torus c t hp,
    evolution_eq_angularRotation_on_torus c t hq]
  exact (angularRotation t).dist_map _ _

/-- Every torus point has arbitrarily late returns within each positive tolerance. -/
theorem torus_recurrence_dist (c : ℝ) {p : PhaseSpace} (hp : p ∈ torus)
    {ε : ℝ} (hε : 0 < ε) (R : ℝ) :
    ∃ t : ℝ, R < t ∧ 0 ≤ t ∧ dist (evolution c t p) p < ε := by
  obtain ⟨a, ha, φ, hφ, hlim⟩ := isCompact_torus.tendsto_subseq
    (fun n : ℕ => torus_invariant_all_real c (n : ℝ) hp)
  have hC := hlim.cauchySeq
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hC ε hε
  obtain ⟨K, hK⟩ := exists_nat_gt (max R 0 + (φ N : ℝ))
  let M : ℕ := N + K
  have hNM : N ≤ M := Nat.le_add_right N K
  have hKM : K ≤ M := Nat.le_add_left K N
  have hKφ : (K : ℝ) ≤ (φ M : ℝ) := by exact_mod_cast hKM.trans (hφ.id_le M)
  have hφNM : (φ N : ℝ) ≤ (φ M : ℝ) := by exact_mod_cast hφ.monotone hNM
  let t : ℝ := (φ M : ℝ) - (φ N : ℝ)
  have ht : 0 ≤ t := sub_nonneg.mpr hφNM
  have htR : R < t := by dsimp [t]; linarith [le_max_left R 0]
  refine ⟨t, htR, ht, ?_⟩
  have hadd : evolution c (φ M : ℝ) p =
      evolution c (φ N : ℝ) (evolution c t p) := by
    have he : (φ M : ℝ) = t + (φ N : ℝ) := by dsimp [t]; ring
    conv_lhs => rw [he]
    exact evolution_add c ht (Nat.cast_nonneg _) p
  have hd := dist_evolution_torus c (φ N : ℝ) (torus_invariant_all_real c t hp) hp
  rw [← hadd] at hd
  rw [← hd]
  exact hN M hNM N le_rfl

/-- The flow restricted to the invariant torus, with its subspace topology. -/
def torusEvolution (c t : ℝ) (p : torus) : torus :=
  ⟨evolution c t p, torus_invariant_all_real c t p.property⟩

/-- Every neighbourhood in T is revisited after any prescribed positive real time. -/
theorem torus_recurrence_nhds (c : ℝ) (p : torus) {U : Set torus}
    (hU : U ∈ 𝓝 p) {R : ℝ} (_hR : 0 < R) :
    ∃ t : ℝ, R < t ∧ torusEvolution c t p ∈ U := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
  obtain ⟨t, htR, ht, hd⟩ := torus_recurrence_dist c p.property hε R
  exact ⟨t, htR, hball hd⟩

theorem torus_recurrence_ambient_nhds (c : ℝ) {p : PhaseSpace} (hp : p ∈ torus)
    {U : Set PhaseSpace} (hU : U ∈ 𝓝 p) {R : ℝ} (_hR : 0 < R) :
    ∃ t : ℝ, R < t ∧ evolution c t p ∈ U := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
  obtain ⟨t, htR, ht, hd⟩ := torus_recurrence_dist c hp hε R
  exact ⟨t, htR, hball hd⟩

/-- No positive real time fixes a torus point. -/
theorem torusEvolution_no_positive_return (c : ℝ) (p : torus) {t : ℝ} (ht : 0 < t) :
    torusEvolution c t p ≠ p := by
  intro h
  exact torus_no_positive_return c p.property ht (congrArg Subtype.val h)

end Eden
