import Eden.ExteriorLimits
import Eden.SelectedSums
import Eden.KaplanYorke
import Mathlib.Topology.Order.LiminfLimsup

/-!
# Attained maximal growth on unit exterior vectors

The growth rate is defined from the induced derivative and canonical
exterior norm. Its existence is already proved for every fixed nonzero
vector. Unit basis wedges in the initial orthonormal frame attain the sums
of the block exponents; the greatest such sum is the ordered partial sum.
-/

noncomputable section
open Filter Set
open scoped Topology
namespace Eden

/-- The real-time logarithmic growth rate of a fixed exterior vector.
Existence is asserted only for nonzero vectors in the theorems below. -/
def exteriorGrowthRate (k : ℕ) (c : ℝ) (p : PhaseSpace) (v : ExteriorSpace k) : ℝ :=
  limUnder atTop (fun t => Real.log ‖exteriorEvolution k c t p v‖ / t)

theorem exteriorGrowthRate_eq {k : ℕ} (c : ℝ) (p : PhaseSpace)
    {v : ExteriorSpace k} (hv : v ≠ 0) :
    exteriorGrowthRate k c p v =
      (exteriorSupport k p v).sup' (exteriorSupport_nonempty p hv) (exteriorRate k c p) :=
  (tendsto_log_norm_exteriorEvolution_div c p hv).limUnder_eq

theorem tendsto_exteriorGrowthRate {k : ℕ} (c : ℝ) (p : PhaseSpace)
    {v : ExteriorSpace k} (hv : v ≠ 0) :
    Tendsto (fun t => Real.log ‖exteriorEvolution k c t p v‖ / t) atTop
      (𝓝 (exteriorGrowthRate k c p v)) := by
  rw [exteriorGrowthRate_eq c p hv]
  exact tendsto_log_norm_exteriorEvolution_div c p hv

theorem limsup_exteriorGrowthRate {k : ℕ} (c : ℝ) (p : PhaseSpace)
    {v : ExteriorSpace k} (hv : v ≠ 0) :
    limsup (fun t => Real.log ‖exteriorEvolution k c t p v‖ / t) atTop =
      exteriorGrowthRate k c p v :=
  (tendsto_exteriorGrowthRate c p hv).limsup_eq

/-- A standard unit wedge transported into the fixed initial radial frame. -/
def initialExteriorBasisVector (k : ℕ) (p : PhaseSpace) (s : ExteriorIndex k) : ExteriorSpace k :=
  exteriorPower.map k (radialFrame p).toLinearMap (exteriorBasis k s)

theorem norm_initialExteriorBasisVector (k : ℕ) (p : PhaseSpace) (s : ExteriorIndex k) :
    ‖initialExteriorBasisVector k p s‖ = 1 := by
  rw [initialExteriorBasisVector, norm_exterior_map_isometry]
  exact (exteriorBasis k).orthonormal.norm_eq_one s

theorem initialExteriorBasisVector_ne_zero (k : ℕ) (p : PhaseSpace) (s : ExteriorIndex k) :
    initialExteriorBasisVector k p s ≠ 0 := by
  intro h
  have hn := norm_initialExteriorBasisVector k p s
  rw [h, norm_zero] at hn
  norm_num at hn

theorem exteriorInitialCoordinates_basis (k : ℕ) (p : PhaseSpace) (s : ExteriorIndex k) :
    exteriorInitialCoordinates k p (initialExteriorBasisVector k p s) =
      (exteriorBasis k).repr (exteriorBasis k s) := by
  have hcomp : (radialFrame p).symm.toLinearMap ∘ₗ (radialFrame p).toLinearMap = LinearMap.id := by
    ext v
    simp
  unfold exteriorInitialCoordinates initialExteriorBasisVector
  rw [← LinearMap.comp_apply, ← exteriorPower.map_comp, hcomp, exteriorPower.map_id]
  rfl

theorem exteriorSupport_basis (k : ℕ) (p : PhaseSpace) (s : ExteriorIndex k) :
    exteriorSupport k p (initialExteriorBasisVector k p s) = {s} := by
  classical
  ext j
  simp [exteriorSupport, exteriorInitialCoordinates_basis]

theorem exteriorGrowthRate_basis (k : ℕ) (c : ℝ) (p : PhaseSpace) (s : ExteriorIndex k) :
    exteriorGrowthRate k c p (initialExteriorBasisVector k p s) = exteriorRate k c p s := by
  rw [exteriorGrowthRate_eq c p (initialExteriorBasisVector_ne_zero k p s)]
  simp [exteriorSupport_basis]

theorem exteriorRate_eq_sum (k : ℕ) (c : ℝ) (p : PhaseSpace) (s : ExteriorIndex k) :
    exteriorRate k c p s = ∑ j ∈ s.val, factorExponents c p j := by
  unfold exteriorRate
  change (∑ i : Fin k, factorExponents c p (s.val.orderEmbOfFin s.property i)) = _
  conv_rhs => rw [← Finset.image_orderEmbOfFin_univ s.val s.property]
  rw [Finset.sum_image (fun _ _ _ _ h => (s.val.orderEmbOfFin s.property).injective h)]

theorem spectrumPartialSum_eq_fin_sum {k : ℕ} (hk : k ≤ 5) (a : Fin 5 → ℝ) :
    spectrumPartialSum a k = ∑ i : Fin k, a (Fin.castLE hk i) := by
  rw [spectrumPartialSum, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  simp [spectrumEntry, lt_of_lt_of_le i.isLt hk]
  rfl

theorem isGreatest_exteriorRate {k : ℕ} (hk : k ≤ 5) (c : ℝ) (p : PhaseSpace) :
    IsGreatest (Set.range (exteriorRate k c p)) (spectrumPartialSum (lyapunovExponent c p) k) := by
  have h := isGreatest_selected_sum hk (lyapunovExponent_antitone c p) (multiset_lyapunovExponent c p)
  rw [spectrumPartialSum_eq_fin_sum hk]
  convert h using 1
  ext r
  simp only [Set.mem_range, Set.mem_ofPred_eq, exteriorRate_eq_sum]
  constructor
  · rintro ⟨s, hs⟩
    exact ⟨s, hs.symm⟩
  · rintro ⟨s, hs⟩
    exact ⟨s, hs.symm⟩

/-- The largest growth rate over unit k-vectors is precisely the sum of
the first k ordered Lyapunov exponents, and is attained. -/
theorem isGreatest_exteriorGrowthRate_unit {k : ℕ} (hk : k ≤ 5) (c : ℝ) (p : PhaseSpace) :
    IsGreatest (exteriorGrowthRate k c p '' {v : ExteriorSpace k | ‖v‖ = 1})
      (spectrumPartialSum (lyapunovExponent c p) k) := by
  obtain ⟨⟨s, hs⟩, hupper⟩ := isGreatest_exteriorRate hk c p
  constructor
  · exact ⟨initialExteriorBasisVector k p s, norm_initialExteriorBasisVector k p s,
      (exteriorGrowthRate_basis k c p s).trans hs⟩
  · rintro r ⟨v, hv, rfl⟩
    have hv₀ : v ≠ 0 := by intro h; simp [h] at hv
    rw [exteriorGrowthRate_eq c p hv₀]
    exact Finset.sup'_le _ _ (fun s _ => hupper ⟨s, rfl⟩)

theorem isGreatest_exteriorGrowthRate_nonzero {k : ℕ} (hk : k ≤ 5) (c : ℝ) (p : PhaseSpace) :
    IsGreatest (exteriorGrowthRate k c p '' {v : ExteriorSpace k | v ≠ 0})
      (spectrumPartialSum (lyapunovExponent c p) k) := by
  obtain ⟨⟨s, hs⟩, hupper⟩ := isGreatest_exteriorRate hk c p
  constructor
  · exact ⟨initialExteriorBasisVector k p s, initialExteriorBasisVector_ne_zero k p s,
      (exteriorGrowthRate_basis k c p s).trans hs⟩
  · rintro r ⟨v, hv, rfl⟩
    rw [exteriorGrowthRate_eq c p hv]
    exact Finset.sup'_le _ _ (fun s _ => hupper ⟨s, rfl⟩)

end Eden
