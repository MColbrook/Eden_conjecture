import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The polynomial vector field and its invariant sets

These definitions describe the system in Matthew J. Colbrook's
*Aperiodic maximisers of Lyapunov dimension: a counterexample to the unrestricted
form of Eden's conjecture*. Coordinates are ordered
`(Re z₁, Im z₁, Re z₂, Im z₂, w)` and carry the Euclidean inner product.

The ambient space uses Mathlib's `EuclideanSpace`, developed by Joseph Myers,
Sébastien Gouëzel and Heather Macbeth.
-/

noncomputable section

namespace Eden

/-- The ambient five-dimensional real Euclidean space. -/
abbrev PhaseSpace := EuclideanSpace ℝ (Fin 5)

/-- The squared radius of the first planar coordinate. -/
def radiusSq₁ (p : PhaseSpace) : ℝ := p 0 ^ 2 + p 1 ^ 2

/-- The squared radius of the second planar coordinate. -/
def radiusSq₂ (p : PhaseSpace) : ℝ := p 2 ^ 2 + p 3 ^ 2

/-- The polynomial multiplying each planar coordinate. -/
def q (s : ℝ) : ℝ := -(s - 1) * (s - 2)

/-- The scalar radial vector field, on the nonnegative half-line. -/
def radialField (r : ℝ) : ℝ := -r * (r ^ 2 - 1) * (r ^ 2 - 2)

/-- The real polynomial vector field, with angular frequencies `1` and `√2`. -/
def vectorField (c : ℝ) (p : PhaseSpace) : PhaseSpace :=
  !₂[q (radiusSq₁ p) * p 0 - p 1,
     q (radiusSq₁ p) * p 1 + p 0,
     q (radiusSq₂ p) * p 2 - Real.sqrt 2 * p 3,
     q (radiusSq₂ p) * p 3 + Real.sqrt 2 * p 2,
     -c * p 4]

/-- The product of the two closed discs of radius `√2` in the plane `w = 0`. -/
def attractor : Set PhaseSpace :=
  {p | radiusSq₁ p ≤ 2 ∧ radiusSq₂ p ≤ 2 ∧ p 4 = 0}

/-- The product of the two unit circles in the plane `w = 0`. -/
def torus : Set PhaseSpace :=
  {p | radiusSq₁ p = 1 ∧ radiusSq₂ p = 1 ∧ p 4 = 0}

/-- The radial rate in the rotating planar variational equation. -/
def radialRate (s : ℝ) : ℝ := -5 * s ^ 2 + 9 * s - 2

/-- The tangential rate in the rotating planar variational equation. -/
def tangentialRate (s : ℝ) : ℝ := -s ^ 2 + 3 * s - 2

/-- The formula for the maximal Lyapunov dimension when `c > 4`. -/
def targetDimension (c : ℝ) : ℝ := 4 + 4 / c

end Eden
