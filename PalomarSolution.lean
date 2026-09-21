import Solution

/-!
# Proof of the independent Palomar statement

This module repeats the explicit definitions and theorem type from
`PalomarChallenge.lean` and proves `EdenPalomar.main_theorem` using the
substantive development in `Solution.lean`. Comparator checks the two modules
independently. The witness is `Eden.evolution c`; the repeated definitions reduce
to their counterparts in the existing proof library.
-/

noncomputable section
open Set Filter
open scoped Topology
namespace EdenPalomar

/-- Real coordinates (Re z₁, Im z₁, Re z₂, Im z₂, w) with Euclidean norm. -/
abbrev PhaseSpace := EuclideanSpace ℝ (Fin 5)

/-- Squared modulus of the first complex coordinate. -/
def radiusSq₁ (p : PhaseSpace) : ℝ := p 0 ^ 2 + p 1 ^ 2

/-- Squared modulus of the second complex coordinate. -/
def radiusSq₂ (p : PhaseSpace) : ℝ := p 2 ^ 2 + p 3 ^ 2

/-- The radial polynomial q(s) = -(s-1)(s-2). -/
def q (s : ℝ) : ℝ := -(s - 1) * (s - 2)

/-- Equation (1.6), a degree-five real polynomial field with frequencies 1, √2. -/
def vectorField (c : ℝ) (p : PhaseSpace) : PhaseSpace :=
  !₂[q (radiusSq₁ p) * p 0 - p 1, q (radiusSq₁ p) * p 1 + p 0,
     q (radiusSq₂ p) * p 2 - Real.sqrt 2 * p 3,
     q (radiusSq₂ p) * p 3 + Real.sqrt 2 * p 2, -c * p 4]

/-- Product of the closed discs of radius √2, with w = 0; equation (1.7). -/
def attractor : Set PhaseSpace :=
  {p | radiusSq₁ p ≤ 2 ∧ radiusSq₂ p ≤ 2 ∧ p 4 = 0}

/-- Product of the unit circles, with w = 0; equation (1.7). -/
def torus : Set PhaseSpace :=
  {p | radiusSq₁ p = 1 ∧ radiusSq₂ p = 1 ∧ p 4 = 0}

/-- Standard angular parametrisation of the unit two-torus. -/
def torusPoint (θ₁ θ₂ : ℝ) : PhaseSpace :=
  !₂[Real.cos θ₁, Real.sin θ₁, Real.cos θ₂, Real.sin θ₂, 0]

/-- Divergence is the trace of the ambient Fréchet derivative. -/
def divergence (c : ℝ) (p : PhaseSpace) : ℝ :=
  LinearMap.trace ℝ PhaseSpace (fderiv ℝ (vectorField c) p).toLinearMap

/-- Equation (1.1): the first k singular values have weight one, the next
has weight α at d = k + α, and later ones have weight zero (indices start at 0).
At d = 5 this is the product of all five singular values. -/
def singularValueFunction (M : PhaseSpace →ₗ[ℝ] PhaseSpace) (d : ℝ) : ℝ :=
  ∏ i ∈ Finset.range 5, M.singularValues i ^ (min 1 (max 0 (d - i)))

/-- Dimensions in [0,5] at which the singular-value function is at least one. -/
def admissibleDimensions (φ : ℝ → PhaseSpace → PhaseSpace) (t : ℝ)
    (p : PhaseSpace) : Set ℝ :=
  {d | d ∈ Icc 0 5 ∧ 1 ≤ singularValueFunction (fderiv ℝ (φ t) p).toLinearMap d}

/-- Finite-time local dimension (1.2); attainment is part of the theorem. -/
def finiteTimeDimension (φ : ℝ → PhaseSpace → PhaseSpace) (t : ℝ)
    (p : PhaseSpace) : ℝ := sSup (admissibleDimensions φ t p)

/-- Infimum over positive times of the spatial supremum, equation (1.3). -/
def globalLyapunovDimension (φ : ℝ → PhaseSpace → PhaseSpace) (K : Set PhaseSpace) : ℝ :=
  sInf {v : ℝ | ∃ t : ℝ, 0 < t ∧ v = sSup (finiteTimeDimension φ t '' K)}

/-- Singular-value exponent (1.4); existence of this real-time limit is proved. -/
def lyapunovExponent (φ : ℝ → PhaseSpace → PhaseSpace) (p : PhaseSpace)
    (i : Fin 5) : ℝ :=
  limUnder atTop (fun t : ℝ => Real.log ((fderiv ℝ (φ t) p).toLinearMap.singularValues i) / t)

/-- Extend a five-entry spectrum by zero to write natural-number partial sums. -/
def spectrumEntry (a : Fin 5 → ℝ) (i : ℕ) : ℝ :=
  if h : i < 5 then a ⟨i, h⟩ else 0

/-- Sum of the first k ordered exponents, with the empty sum equal to zero. -/
def spectrumPartialSum (a : Fin 5 → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range k, spectrumEntry a i

/-- Admissible Kaplan--Yorke indices; zero partial sums include neutral directions. -/
def nonnegativeSumIndices (a : Fin 5 → ℝ) : Finset ℕ :=
  (Finset.range 6).filter (fun k => 0 ≤ spectrumPartialSum a k)

/-- The empty partial sum makes zero an admissible index. -/
theorem indices_nonempty (a : Fin 5 → ℝ) : (nonnegativeSumIndices a).Nonempty := by
  refine ⟨0, ?_⟩
  simp only [nonnegativeSumIndices, Finset.mem_filter, Finset.mem_range]
  exact ⟨by decide, by simp [spectrumPartialSum]⟩

/-- Largest index in {0,...,5} with nonnegative partial sum. -/
def kaplanYorkeIndex (a : Fin 5 → ℝ) : ℕ :=
  (nonnegativeSumIndices a).max' (indices_nonempty a)

/-- Equation (1.5), including the two endpoint cases j = 0 and j = 5. -/
def kaplanYorkeDimension (a : Fin 5 → ℝ) : ℝ :=
  if kaplanYorkeIndex a = 0 then 0
  else if kaplanYorkeIndex a = 5 then 5
  else (kaplanYorkeIndex a : ℝ) +
    spectrumPartialSum a (kaplanYorkeIndex a) / |spectrumEntry a (kaplanYorkeIndex a)|

/-- Pointwise asymptotic Kaplan--Yorke dimension of the singular-value exponents. -/
def asymptoticDimension (φ : ℝ → PhaseSpace → PhaseSpace) (p : PhaseSpace) : ℝ :=
  kaplanYorkeDimension (lyapunovExponent φ p)

/-- Equilibria and positive-return points in the attractor. -/
def periodicEquilibriumSet (c : ℝ) (φ : ℝ → PhaseSpace → PhaseSpace) : Set PhaseSpace :=
  attractor ∩ ({p | vectorField c p = 0} ∪ {p | ∃ t : ℝ, 0 < t ∧ φ t p = p})

/-- Compact global attractor: nonempty, compact, strictly forward invariant,
and attracting every bounded set uniformly. -/
def IsGlobalAttractor (φ : ℝ → PhaseSpace → PhaseSpace) (K : Set PhaseSpace) : Prop :=
  K.Nonempty ∧ IsCompact K ∧ (∀ t : ℝ, 0 ≤ t → φ t '' K = K) ∧
    ∀ B : Set PhaseSpace, Bornology.IsBounded B → ∀ ε : ℝ, 0 < ε →
      ∃ T : ℝ, 0 ≤ T ∧ ∀ t : ℝ, T ≤ t → ∀ p ∈ B,
        ∃ q ∈ K, dist (φ t p) q < ε

/-- Theorem 1.1, including the forward ODE, uniqueness, differentiability,
invertibility, dimension attainment and existence of exponents. The exact
angular formula strengthens the asserted absence of periodic orbits. -/
theorem main_theorem (c : ℝ) (hc : 4 < c) :
    ∃ φ : ℝ → PhaseSpace → PhaseSpace,
    (∀ p, φ 0 p = p ∧ ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (fun τ => φ τ p) (vectorField c (φ t p)) t) ∧
    (∀ (p : PhaseSpace) (f : ℝ → PhaseSpace),
      ContinuousOn f (Ici 0) →
      (∀ t : ℝ, 0 ≤ t → HasDerivWithinAt f (vectorField c (f t)) (Ici t) t) →
      f 0 = p → EqOn f (fun t => φ t p) (Ici 0)) ∧
    (∀ (s t : ℝ), 0 ≤ s → 0 ≤ t → ∀ p, φ (s + t) p = φ t (φ s p)) ∧
    (∀ t : ℝ, 0 ≤ t → ContDiff ℝ 1 (φ t)) ∧
    (∀ t : ℝ, 0 ≤ t → ∀ p, Function.Bijective (fderiv ℝ (φ t) p)) ∧
    IsGlobalAttractor φ attractor ∧
    (∀ p, divergence c p = 4 - c - 6 * (radiusSq₁ p - 1) ^ 2 -
      6 * (radiusSq₂ p - 1) ^ 2 ∧ divergence c p ≤ 4 - c ∧ 4 - c < 0) ∧
    (4 < 4 + 4 / c ∧ 4 + 4 / c < 5) ∧
    (∀ t : ℝ, 0 < t →
      IsGreatest (finiteTimeDimension φ t '' attractor) (4 + 4 / c) ∧
      {p ∈ attractor | finiteTimeDimension φ t p = 4 + 4 / c} = torus) ∧
    (∀ p ∈ attractor, ∀ i : Fin 5,
      Tendsto (fun t : ℝ => Real.log ((fderiv ℝ (φ t) p).toLinearMap.singularValues i) / t)
        atTop (𝓝 (lyapunovExponent φ p i))) ∧
    (globalLyapunovDimension φ attractor = 4 + 4 / c) ∧
    IsGreatest (asymptoticDimension φ '' attractor) (4 + 4 / c) ∧
    ({p ∈ attractor | asymptoticDimension φ p = 4 + 4 / c} = torus) ∧
    IsGreatest (asymptoticDimension φ '' periodicEquilibriumSet c φ) 3 ∧
    (∀ t : ℝ, 0 < t →
      IsGreatest (finiteTimeDimension φ t '' periodicEquilibriumSet c φ) 3) ∧
    (∀ (t : ℝ) (p : PhaseSpace), p ∈ torus → φ t p ∈ torus) ∧
    (∀ p ∈ torus, ∀ t : ℝ, 0 < t → φ t p ≠ p) ∧
    (∀ t θ₁ θ₂ : ℝ, φ t (torusPoint θ₁ θ₂) =
      torusPoint (θ₁ + t) (θ₂ + Real.sqrt 2 * t)) ∧
    (∀ p ∈ attractor, Tendsto (fun t : ℝ => finiteTimeDimension φ t p)
      atTop (𝓝 (asymptoticDimension φ p))) ∧
    (∀ t : ℝ, 0 < t → ∀ p,
      IsGreatest (admissibleDimensions φ t p) (finiteTimeDimension φ t p)) := by
  rcases EdenVerified.main_theorem c hc with
    ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19⟩
  exact ⟨Eden.evolution c, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13,
    h14, h15, h16, h17, h18, h19, fun t ht p => Eden.finiteTimeDimension_isGreatest c ht.le p⟩

end EdenPalomar
