import Eden.Basic
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Orthogonal block rotations in the ambient Euclidean space

Each planar block is a real rotation specified by its cosine and sine. The fifth
coordinate is fixed. Norm preservation is proved in the Euclidean norm, using
Mathlib's `EuclideanSpace.real_norm_sq_eq`. These rotations will supply the
input and output frames for the derivative.
-/

noncomputable section
namespace Eden

/-- Two planar linear maps, with a fixed fifth coordinate. They are rotations when
`a²+b²=1` and `d²+e²=1`, as required by `blockRotation` below. -/
def rotateBlocks (a b d e : ℝ) (v : PhaseSpace) : PhaseSpace :=
  !₂[a * v 0 - b * v 1, b * v 0 + a * v 1,
     d * v 2 - e * v 3, e * v 2 + d * v 3, v 4]

theorem rotateBlocks_inverse {a b d e : ℝ}
    (h₁ : a ^ 2 + b ^ 2 = 1) (h₂ : d ^ 2 + e ^ 2 = 1) (v : PhaseSpace) :
    rotateBlocks a (-b) d (-e) (rotateBlocks a b d e v) = v := by
  have ha (i : Fin 5) := congrArg (fun r : ℝ => r * v i) h₁
  have hd (i : Fin 5) := congrArg (fun r : ℝ => r * v i) h₂
  ext i
  fin_cases i <;> simp [rotateBlocks]
  all_goals nlinarith only [ha 0, ha 1, hd 2, hd 3]

theorem norm_rotateBlocks {a b d e : ℝ}
    (h₁ : a ^ 2 + b ^ 2 = 1) (h₂ : d ^ 2 + e ^ 2 = 1) (v : PhaseSpace) :
    ‖rotateBlocks a b d e v‖ = ‖v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1
  simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]
  simp [rotateBlocks]
  nlinarith [congrArg (fun r : ℝ => r * ((v 0) ^ 2 + (v 1) ^ 2)) h₁,
    congrArg (fun r : ℝ => r * ((v 2) ^ 2 + (v 3) ^ 2)) h₂]

/-- The block rotations as Euclidean linear isometries. -/
def blockRotation (a b d e : ℝ) (h₁ : a ^ 2 + b ^ 2 = 1) (h₂ : d ^ 2 + e ^ 2 = 1) :
    PhaseSpace ≃ₗᵢ[ℝ] PhaseSpace where
  toFun := rotateBlocks a b d e
  invFun := rotateBlocks a (-b) d (-e)
  left_inv := rotateBlocks_inverse h₁ h₂
  right_inv := by
    have h₁' : a ^ 2 + (-b) ^ 2 = 1 := by simpa using h₁
    have h₂' : d ^ 2 + (-e) ^ 2 = 1 := by simpa using h₂
    intro v
    simpa using rotateBlocks_inverse h₁' h₂' v
  map_add' := by
    intro v w
    ext i
    fin_cases i <;> simp [rotateBlocks] <;> ring
  map_smul' := by
    intro r v
    ext i
    fin_cases i <;> simp [rotateBlocks, smul_eq_mul] <;> ring
  norm_map' := norm_rotateBlocks h₁ h₂

@[simp] theorem blockRotation_apply (a b d e : ℝ) (h₁ : a ^ 2 + b ^ 2 = 1)
    (h₂ : d ^ 2 + e ^ 2 = 1) (v : PhaseSpace) :
    blockRotation a b d e h₁ h₂ v = rotateBlocks a b d e v := rfl

end Eden
