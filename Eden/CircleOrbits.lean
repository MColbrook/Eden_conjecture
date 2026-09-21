import Eden.PeriodicSets
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# The four circles as geometric orbits

Equal nonzero planar radii can be joined by a positive rotation angle. The
construction uses Mathlib's complex argument and its sine/cosine formulas,
with an added full turn to ensure positive time. This argument library is
due to Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne and
Benjamin Davidson. The resulting orbit sets use the forward evolution.
-/

noncomputable section
open Set
namespace Eden

/-- The geometric forward orbit under the evolution. -/
def forwardOrbit (c : ℝ) (p : PhaseSpace) : Set PhaseSpace :=
  {q | ∃ t : ℝ, 0 ≤ t ∧ evolution c t p = q}

theorem exists_positive_rotation_between {x y u v s : ℝ} (hs : 0 < s)
    (hxy : x ^ 2 + y ^ 2 = s) (huv : u ^ 2 + v ^ 2 = s) :
    ∃ θ : ℝ, 0 < θ ∧ x * Real.cos θ - y * Real.sin θ = u ∧
      x * Real.sin θ + y * Real.cos θ = v := by
  let a := (x * u + y * v) / s
  let b := (x * v - y * u) / s
  have hid : (x * u + y * v) ^ 2 + (x * v - y * u) ^ 2 = s ^ 2 := by
    calc
      _ = (x ^ 2 + y ^ 2) * (u ^ 2 + v ^ 2) := by ring
      _ = _ := by rw [hxy, huv]; ring
  have hab : a ^ 2 + b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, ← add_div, hid, div_self (pow_ne_zero 2 (ne_of_gt hs))]
  let z : ℂ := ⟨a, b⟩
  have hz : ‖z‖ = 1 := by
    have hnorm : ‖z‖ ^ 2 = 1 := by
      rw [← Complex.normSq_eq_norm_sq]
      change a * a + b * b = 1
      nlinarith [hab]
    nlinarith [norm_nonneg z]
  have hcos : Real.cos (Complex.arg z) = a := by
    simpa only [hz, one_mul] using Complex.norm_mul_cos_arg z
  have hsin : Real.sin (Complex.arg z) = b := by
    simpa only [hz, one_mul] using Complex.norm_mul_sin_arg z
  refine ⟨Complex.arg z + 2 * Real.pi,
    by linarith [Complex.neg_pi_lt_arg z, Real.pi_pos], ?_, ?_⟩
  · rw [Real.cos_add_two_pi, Real.sin_add_two_pi, hcos, hsin]
    dsimp [a, b]
    field_simp
    nlinarith [congrArg (fun w : ℝ => u * w) hxy]
  · rw [Real.cos_add_two_pi, Real.sin_add_two_pi, hcos, hsin]
    dsimp [a, b]
    field_simp
    nlinarith [congrArg (fun w : ℝ => v * w) hxy]

theorem exists_planar_time_on_stationary_radius {Ω s x y u v : ℝ}
    (hΩ : 0 < Ω) (hs : s = 1 ∨ s = 2)
    (hxy : x ^ 2 + y ^ 2 = s) (huv : u ^ 2 + v ^ 2 = s) :
    ∃ t : ℝ, 0 < t ∧ planarX Ω t x y = u ∧ planarY Ω t x y = v := by
  have hs₀ : 0 < s := by rcases hs with rfl | rfl <;> norm_num
  obtain ⟨θ, hθ, hx, hy⟩ := exists_positive_rotation_between hs₀ hxy huv
  have ht : 0 < θ / Ω := div_pos hθ hΩ
  have hangle : Ω * (θ / Ω) = θ := by field_simp
  have hg : planarAmplitude (θ / Ω) (x ^ 2 + y ^ 2) = 1 := by
    rw [hxy]
    rcases hs with rfl | rfl
    · exact planarAmplitude_at_one ht.le
    · exact planarAmplitude_at_two ht.le
  exact ⟨θ / Ω, ht, by simpa only [planarX, hg, one_mul, hangle] using hx,
    by simpa only [planarY, hg, one_mul, hangle] using hy⟩

theorem firstCircle_invariant (c : ℝ) {s t : ℝ} (hs : s = 1 ∨ s = 2)
    (ht : 0 ≤ t) {p : PhaseSpace} (hp : p ∈ firstCircle s) :
    evolution c t p ∈ firstCircle s := by
  refine ⟨?_, ?_, ?_⟩
  · rw [radiusSq₁_evolution c ht, hp.1]
    rcases hs with rfl | rfl <;> simp
  · rw [radiusSq₂_evolution c ht, hp.2.1]
    simp
  · simp [evolution, hp.2.2]

theorem secondCircle_invariant (c : ℝ) {s t : ℝ} (hs : s = 1 ∨ s = 2)
    (ht : 0 ≤ t) {p : PhaseSpace} (hp : p ∈ secondCircle s) :
    evolution c t p ∈ secondCircle s := by
  refine ⟨?_, ?_, ?_⟩
  · rw [radiusSq₁_evolution c ht, hp.1]
    simp
  · rw [radiusSq₂_evolution c ht, hp.2.1]
    rcases hs with rfl | rfl <;> simp
  · simp [evolution, hp.2.2]

/-- Every point of a invariant circle has that entire circle as its geometric orbit. -/
theorem forwardOrbit_eq_firstCircle (c : ℝ) {s : ℝ} (hs : s = 1 ∨ s = 2)
    {p : PhaseSpace} (hp : p ∈ firstCircle s) : forwardOrbit c p = firstCircle s := by
  ext q
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact firstCircle_invariant c hs ht hp
  · intro hq
    obtain ⟨t, ht, hx, hy⟩ := exists_planar_time_on_stationary_radius
      (show (0 : ℝ) < 1 by norm_num) hs hp.1 hq.1
    refine ⟨t, ht.le, ?_⟩
    obtain ⟨hp₂, hp₃⟩ := (radiusSq₂_eq_zero_iff p).mp hp.2.1
    obtain ⟨hq₂, hq₃⟩ := (radiusSq₂_eq_zero_iff q).mp hq.2.1
    ext i
    fin_cases i <;> simp [evolution, hx, hy, hp₂, hp₃, hq₂, hq₃, hp.2.2, hq.2.2]

/-- The second-plane circles are also whole geometric orbits, at frequency sqrt(2). -/
theorem forwardOrbit_eq_secondCircle (c : ℝ) {s : ℝ} (hs : s = 1 ∨ s = 2)
    {p : PhaseSpace} (hp : p ∈ secondCircle s) : forwardOrbit c p = secondCircle s := by
  ext q
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact secondCircle_invariant c hs ht hp
  · intro hq
    obtain ⟨t, ht, hx, hy⟩ := exists_planar_time_on_stationary_radius
      (show (0 : ℝ) < Real.sqrt 2 by positivity) hs hp.2.1 hq.2.1
    refine ⟨t, ht.le, ?_⟩
    obtain ⟨hp₀, hp₁⟩ := (radiusSq₁_eq_zero_iff p).mp hp.1
    obtain ⟨hq₀, hq₁⟩ := (radiusSq₁_eq_zero_iff q).mp hq.1
    ext i
    fin_cases i <;> simp [evolution, hx, hy, hp₀, hp₁, hq₀, hq₁, hp.2.2, hq.2.2]

end Eden
