import Eden.InvariantSets
import Mathlib.Topology.Order.IntermediateValue

/-!
# Strict invariance of the product of discs

For each nonnegative time, the scalar map sends `[0,2]` onto itself by Mathlib's
intermediate value theorem. An inverse rotation and positive rescaling then
supply a Cartesian preimage in each disc. This proves surjectivity in Cartesian
coordinates, including at the origin.
-/

noncomputable section
namespace Eden

theorem squaredRadiusEvolution_surjOn {t : ℝ} (ht : 0 ≤ t) :
    Set.SurjOn (squaredRadiusEvolution t) (Set.Icc 0 2) (Set.Icc 0 2) := by
  have hc : Continuous (squaredRadiusEvolution t) :=
    continuous_iff_continuousAt.2 fun s =>
      (hasDerivAt_squaredRadiusEvolution_parameter ht s).continuousAt
  have h := intermediate_value_Icc (show (0 : ℝ) ≤ 2 by norm_num) hc.continuousOn
  intro s hs
  exact h (by simpa only [squaredRadiusEvolution_at_zero,
    squaredRadiusEvolution_at_two] using hs)

/-- Every point of the closed disc has a preimage in that disc. -/
theorem planar_surjective_on_disc (Ω : ℝ) {t x y : ℝ} (ht : 0 ≤ t)
    (hxy : x ^ 2 + y ^ 2 ≤ 2) :
    ∃ u v : ℝ, u ^ 2 + v ^ 2 ≤ 2 ∧ planarX Ω t u v = x ∧ planarY Ω t u v = y := by
  obtain ⟨s, hs, heq⟩ := squaredRadiusEvolution_surjOn ht
    ⟨add_nonneg (sq_nonneg x) (sq_nonneg y), hxy⟩
  let g := planarAmplitude t s
  let a := Real.cos (Ω * t)
  let b := Real.sin (Ω * t)
  have hg : g ≠ 0 := ne_of_gt (planarAmplitude_pos ht hs.1)
  have hab : a ^ 2 + b ^ 2 = 1 := by
    dsimp [a, b]
    nlinarith [Real.sin_sq_add_cos_sq (Ω * t)]
  have hsg : s * g ^ 2 = x ^ 2 + y ^ 2 := by
    dsimp [g]
    rw [planarAmplitude_sq ht hs.1, mul_amplitudeSq ht, heq]
  let u := (x * a + y * b) / g
  let v := (-x * b + y * a) / g
  have huv : u ^ 2 + v ^ 2 = s := by
    dsimp [u, v]
    field_simp
    nlinarith [congrArg (fun z : ℝ => (x ^ 2 + y ^ 2) * z) hab]
  refine ⟨u, v, huv ▸ hs.2, ?_, ?_⟩
  · unfold planarX
    rw [huv]
    change g * (u * a - v * b) = x
    dsimp [u, v]
    field_simp
    nlinarith [congrArg (fun z : ℝ => x * z) hab]
  · unfold planarY
    rw [huv]
    change g * (u * b + v * a) = y
    dsimp [u, v]
    field_simp
    nlinarith [congrArg (fun z : ℝ => y * z) hab]

theorem evolution_surjOn_attractor (c : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    Set.SurjOn (evolution c t) attractor attractor := by
  intro p hp
  obtain ⟨u₁, v₁, h₁, hx₁, hy₁⟩ := planar_surjective_on_disc 1 ht hp.1
  obtain ⟨u₂, v₂, h₂, hx₂, hy₂⟩ := planar_surjective_on_disc (Real.sqrt 2) ht hp.2.1
  refine ⟨!₂[u₁, v₁, u₂, v₂, 0], ?_, ?_⟩
  · change u₁ ^ 2 + v₁ ^ 2 ≤ 2 ∧ u₂ ^ 2 + v₂ ^ 2 ≤ 2 ∧ (0 : ℝ) = 0
    exact ⟨h₁, h₂, rfl⟩
  · ext i
    fin_cases i <;>
      simp [evolution, hx₁, hy₁, hx₂, hy₂, hp.2.2]

theorem evolution_image_attractor (c : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    evolution c t '' attractor = attractor := by
  apply Set.Subset.antisymm
  · rintro _ ⟨p, hp, rfl⟩
    exact evolution_mem_attractor c ht hp
  · exact evolution_surjOn_attractor c ht

end Eden
