import Eden.HausdorffGeometry

/-!
# Hausdorff dimensions of the attractor and torus

Smooth Euclidean parametrizations bound the dimensions above. Linear
coordinate projections whose images contain open cubes give the matching
lower bounds. Both dimensions refer to the ambient Euclidean sets.
-/

noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace Eden

/-- The attractor has Hausdorff dimension four in the ambient metric. -/
theorem dimH_attractor : dimH attractor = 4 := by
  apply le_antisymm
  · calc
      dimH attractor ≤ dimH (range embedFour) := dimH_mono attractor_subset_range_embedFour
      _ ≤ 4 := by
        simpa only [LinearMap.coe_toContinuousLinearMap', finrank_euclideanSpace_fin, Nat.cast_ofNat] using
          embedFour.toContinuousLinearMap.contDiff.dimH_range_le
  · calc
      (4 : ℝ≥0∞) = dimH (euclideanOpenCube 4) := (dimH_euclideanOpenCube 4).symm
      _ ≤ dimH (projectFour '' attractor) := dimH_mono euclideanOpenCube_subset_projectFour
      _ ≤ dimH attractor := projectFour.toContinuousLinearMap.lipschitz.dimH_image_le attractor

/-- The invariant torus has Hausdorff dimension two in the ambient metric. -/
theorem dimH_torus : dimH torus = 2 := by
  apply le_antisymm
  · rw [← range_torusParametrization]
    simpa only [finrank_euclideanSpace_fin, Nat.cast_ofNat] using
      (contDiff_torusParametrization 1).dimH_range_le
  · calc
      (2 : ℝ≥0∞) = dimH (euclideanOpenCube 2) := (dimH_euclideanOpenCube 2).symm
      _ ≤ dimH (projectTorus '' torus) := dimH_mono euclideanOpenCube_subset_projectTorus
      _ ≤ dimH torus := projectTorus.toContinuousLinearMap.lipschitz.dimH_image_le torus

end Eden
