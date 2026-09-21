import Eden.TorusAngles
import Mathlib.Topology.MetricSpace.HausdorffDimension

/-!
# Euclidean geometry for the Hausdorff dimension bounds

Coordinate embeddings and projections act between Euclidean spaces.
An open cube supplies a full-dimensional subset of each projected image.
The dimension arguments use Yury Kudryashov's Hausdorff-dimension API in
Mathlib.Topology.MetricSpace.HausdorffDimension (Apache 2.0).
-/

noncomputable section
open Set MeasureTheory
namespace Eden

/-- An open coordinate cube in real Euclidean n-space. -/
def euclideanOpenCube (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ∀ i, |x i| < 1}

theorem isOpen_euclideanOpenCube (n : ℕ) : IsOpen (euclideanOpenCube n) := by
  have he : euclideanOpenCube n = ⋂ i : Fin n, {x : EuclideanSpace ℝ (Fin n) | |x i| < 1} := by
    ext x
    simp [euclideanOpenCube]
  rw [he]
  apply isOpen_iInter_of_finite
  intro i
  apply isOpen_lt _ continuous_const
  fun_prop

theorem euclideanOpenCube_nonempty (n : ℕ) : (euclideanOpenCube n).Nonempty := by
  refine ⟨0, ?_⟩
  intro i
  simp

theorem dimH_euclideanOpenCube (n : ℕ) : dimH (euclideanOpenCube n) = n := by
  have hi : (interior (euclideanOpenCube n)).Nonempty := by
    rw [(isOpen_euclideanOpenCube n).interior_eq]
    exact euclideanOpenCube_nonempty n
  simpa only [finrank_euclideanSpace_fin] using Real.dimH_of_nonempty_interior hi

/-- Inclusion of the first four coordinates into the plane w=0. -/
def embedFour : EuclideanSpace ℝ (Fin 4) →ₗ[ℝ] PhaseSpace where
  toFun x := !₂[x 0, x 1, x 2, x 3, 0]
  map_add' x y := by ext i; fin_cases i <;> simp
  map_smul' r x := by ext i; fin_cases i <;> simp

/-- Projection to the first four real coordinates, with Euclidean norms. -/
def projectFour : PhaseSpace →ₗ[ℝ] EuclideanSpace ℝ (Fin 4) where
  toFun p := !₂[p 0, p 1, p 2, p 3]
  map_add' x y := by ext i; fin_cases i <;> simp
  map_smul' r x := by ext i; fin_cases i <;> simp

/-- Projection to the real component of each planar coordinate. -/
def projectTorus : PhaseSpace →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) where
  toFun p := !₂[p 0, p 2]
  map_add' x y := by ext i; fin_cases i <;> simp
  map_smul' r x := by ext i; fin_cases i <;> simp

theorem projectFour_embedFour (x : EuclideanSpace ℝ (Fin 4)) :
    projectFour (embedFour x) = x := by
  ext i
  fin_cases i <;> simp [projectFour, embedFour]

theorem embedFour_projectFour {p : PhaseSpace} (hp : p 4 = 0) :
    embedFour (projectFour p) = p := by
  ext i
  fin_cases i <;> simp [embedFour, projectFour, hp]

theorem attractor_subset_range_embedFour : attractor ⊆ range embedFour := by
  intro p hp
  exact ⟨projectFour p, embedFour_projectFour hp.2.2⟩

theorem embedFour_mem_attractor {x : EuclideanSpace ℝ (Fin 4)}
    (hx : x ∈ euclideanOpenCube 4) : embedFour x ∈ attractor := by
  have hs (i : Fin 4) : x i ^ 2 < 1 := by
    have hi := abs_lt.mp (hx i)
    nlinarith [mul_pos (by linarith : 0 < 1 - x i) (by linarith : 0 < 1 + x i)]
  change x 0 ^ 2 + x 1 ^ 2 ≤ 2 ∧ x 2 ^ 2 + x 3 ^ 2 ≤ 2 ∧ (0 : ℝ) = 0
  exact ⟨by linarith [hs 0, hs 1], by linarith [hs 2, hs 3], rfl⟩

theorem euclideanOpenCube_subset_projectFour :
    euclideanOpenCube 4 ⊆ projectFour '' attractor := by
  intro x hx
  exact ⟨embedFour x, embedFour_mem_attractor hx, projectFour_embedFour x⟩

/-- A point on the torus over each point of the open projected square. -/
def torusGraph (x : EuclideanSpace ℝ (Fin 2)) : PhaseSpace :=
  !₂[x 0, Real.sqrt (1 - x 0 ^ 2), x 1, Real.sqrt (1 - x 1 ^ 2), 0]

theorem torusGraph_mem {x : EuclideanSpace ℝ (Fin 2)}
    (hx : x ∈ euclideanOpenCube 2) : torusGraph x ∈ torus := by
  have hs (i : Fin 2) : 0 ≤ 1 - x i ^ 2 := by
    have hi := abs_lt.mp (hx i)
    nlinarith [mul_pos (by linarith : 0 < 1 - x i) (by linarith : 0 < 1 + x i)]
  simp [torusGraph, torus, radiusSq₁, radiusSq₂, Real.sq_sqrt (hs 0), Real.sq_sqrt (hs 1)]

theorem projectTorus_torusGraph (x : EuclideanSpace ℝ (Fin 2)) :
    projectTorus (torusGraph x) = x := by
  ext i
  fin_cases i <;> simp [projectTorus, torusGraph]

theorem euclideanOpenCube_subset_projectTorus :
    euclideanOpenCube 2 ⊆ projectTorus '' torus := by
  intro x hx
  exact ⟨torusGraph x, torusGraph_mem hx, projectTorus_torusGraph x⟩

/-- The angular parametrization with real Euclidean two-space as domain. -/
def torusParametrization (x : EuclideanSpace ℝ (Fin 2)) : PhaseSpace := torusPoint (x 0) (x 1)

theorem range_torusParametrization : range torusParametrization = torus := by
  ext p
  constructor
  · rintro ⟨x, rfl⟩
    exact torusPoint_mem _ _
  · intro hp
    obtain ⟨a, b, hab⟩ := exists_torusPoint_of_mem hp
    exact ⟨!₂[a, b], hab⟩

theorem contDiff_torusParametrization (n : WithTop ℕ∞) :
    ContDiff ℝ n torusParametrization := by
  rw [contDiff_piLp]
  intro i
  fin_cases i <;> simp [torusParametrization, torusPoint] <;> fun_prop

end Eden
