import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffCentredSplitInt

/-!
# The crossed pairing of the oscillation part is a scalar annealed average

The oscillation part of the cutoff-mean defect of `p.response.transfer` is the vector whose
coordinates are the annealed flat averages, over the coarse subcells `V_w` of the terminal cell, of
the `(φ - (φ)_{V_w})`-weighted subcell means of the optimizer state.  Because the dual variable `Y`
is deterministic, its crossed pairing with that vector commutes with all three averages — the
expectation, the flat average over the subcells and the subcell mean — so the whole row is a
statement about the single SCALAR field `⟨Y₂, ∇u⟩ + ⟨Y₁, a∇u⟩`, which is the form the Fenchel probe
of AK.HC (A.4) consumes.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **The crossed pairing of the oscillation part is a scalar annealed average.**  The pairing of
the deterministic dual variable `Y` with the vector of annealed flat averages of the
`(φ - (φ)_{V_w})`-weighted subcell means of a block field is the annealed flat average of the
`(φ - (φ)_{V_w})`-weighted subcell means of the scalar crossed pairing.  This is the scalar form of
the oscillation half of the cutoff-mean row of `p.response.transfer`. -/
theorem vecDot_avsum_volumeAverage_osc_eq {d : ℕ} {α : Type*} [MeasurableSpace α]
    (P : Measure α) (Z : Finset (Fin d → ℤ)) (V : (Fin d → ℤ) → Set (Vec d))
    (φ : Vec d → ℝ) (X : α → Vec d → BlockVec d) (Y : BlockVec d)
    (hint1 : ∀ i : Fin d, Integrable (fun a => ((Z.card : ℝ))⁻¹ * ∑ w ∈ Z,
      volumeAverage (V w) (fun x => (φ x - volumeAverage (V w) φ) * (X a x).1 i)) P)
    (hint2 : ∀ i : Fin d, Integrable (fun a => ((Z.card : ℝ))⁻¹ * ∑ w ∈ Z,
      volumeAverage (V w) (fun x => (φ x - volumeAverage (V w) φ) * (X a x).2 i)) P)
    (hIOn1 : ∀ (a : α), ∀ w ∈ Z, ∀ i : Fin d, IntegrableOn
      (fun x => (φ x - volumeAverage (V w) φ) * (X a x).1 i) (V w))
    (hIOn2 : ∀ (a : α), ∀ w ∈ Z, ∀ i : Fin d, IntegrableOn
      (fun x => (φ x - volumeAverage (V w) φ) * (X a x).2 i) (V w)) :
    vecDot (fun i => ∫ a, ((Z.card : ℝ))⁻¹ * ∑ w ∈ Z,
          volumeAverage (V w) (fun x => (φ x - volumeAverage (V w) φ) * (X a x).1 i) ∂P) Y.2
        + vecDot Y.1 (fun i => ∫ a, ((Z.card : ℝ))⁻¹ * ∑ w ∈ Z,
          volumeAverage (V w) (fun x => (φ x - volumeAverage (V w) φ) * (X a x).2 i) ∂P)
      = ∫ a, ((Z.card : ℝ))⁻¹ * ∑ w ∈ Z,
          volumeAverage (V w) (fun x => (φ x - volumeAverage (V w) φ) *
            (vecDot Y.2 (X a x).1 + vecDot Y.1 (X a x).2)) ∂P := by
  classical
  -- the finite-sum bookkeeping that moves the two deterministic vectors through the averages
  have hstep : ∀ (C : (Fin d → ℤ) → Fin d → ℝ) (u : Vec d),
      ∑ i : Fin d, (((Z.card : ℝ))⁻¹ * ∑ w ∈ Z, C w i) * u i
        = ((Z.card : ℝ))⁻¹ * ∑ w ∈ Z, ∑ i : Fin d, C w i * u i := by
    intro C u
    calc ∑ i : Fin d, (((Z.card : ℝ))⁻¹ * ∑ w ∈ Z, C w i) * u i
        = ∑ i : Fin d, ∑ w ∈ Z, ((Z.card : ℝ))⁻¹ * (C w i * u i) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [Finset.mul_sum, Finset.sum_mul]
          exact Finset.sum_congr rfl (fun w _ => by ring)
      _ = ∑ w ∈ Z, ∑ i : Fin d, ((Z.card : ℝ))⁻¹ * (C w i * u i) := Finset.sum_comm
      _ = ((Z.card : ℝ))⁻¹ * ∑ w ∈ Z, ∑ i : Fin d, C w i * u i := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun w _ => by rw [Finset.mul_sum])
  -- the one-cell identity: the two slot sums are the subcell mean of the scalar pairing
  have hcell : ∀ (a : α), ∀ w ∈ Z,
      (∑ i : Fin d, volumeAverage (V w)
            (fun x => (φ x - volumeAverage (V w) φ) * (X a x).1 i) * Y.2 i)
        + ∑ i : Fin d, volumeAverage (V w)
            (fun x => (φ x - volumeAverage (V w) φ) * (X a x).2 i) * Y.1 i
      = volumeAverage (V w) (fun x => (φ x - volumeAverage (V w) φ) *
          (vecDot Y.2 (X a x).1 + vecDot Y.1 (X a x).2)) := by
    intro a w hw
    have h1 : ∀ i : Fin d, volumeAverage (V w)
          (fun x => (φ x - volumeAverage (V w) φ) * (X a x).1 i) * Y.2 i
        = volumeAverage (V w)
            (fun x => (φ x - volumeAverage (V w) φ) * (X a x).1 i * Y.2 i) := by
      intro i
      rw [mul_comm, ← volumeAverage_smul]
      refine congrArg (volumeAverage (V w)) ?_
      funext x
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    have h2 : ∀ i : Fin d, volumeAverage (V w)
          (fun x => (φ x - volumeAverage (V w) φ) * (X a x).2 i) * Y.1 i
        = volumeAverage (V w)
            (fun x => (φ x - volumeAverage (V w) φ) * (X a x).2 i * Y.1 i) := by
      intro i
      rw [mul_comm, ← volumeAverage_smul]
      refine congrArg (volumeAverage (V w)) ?_
      funext x
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [Finset.sum_congr rfl (fun i _ => h1 i), Finset.sum_congr rfl (fun i _ => h2 i),
      ← volumeAverage_sum Finset.univ
        (fun i x => (φ x - volumeAverage (V w) φ) * (X a x).1 i * Y.2 i)
        (fun i _ => (hIOn1 a w hw i).mul_const (Y.2 i)),
      ← volumeAverage_sum Finset.univ
        (fun i x => (φ x - volumeAverage (V w) φ) * (X a x).2 i * Y.1 i)
        (fun i _ => (hIOn2 a w hw i).mul_const (Y.1 i)),
      ← volumeAverage_add
        (integrable_finsetSum _ fun i _ => (hIOn1 a w hw i).mul_const (Y.2 i))
        (integrable_finsetSum _ fun i _ => (hIOn2 a w hw i).mul_const (Y.1 i))]
    refine congrArg (volumeAverage (V w)) ?_
    funext x
    simp only [Pi.add_apply]
    rw [vecDot, vecDot, mul_add, Finset.mul_sum, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl (fun i _ => by ring)
    · exact Finset.sum_congr rfl (fun i _ => by ring)
  -- move both pairings inside the expectation
  have hL1 : vecDot (fun i => ∫ a, ((Z.card : ℝ))⁻¹ * ∑ w ∈ Z,
        volumeAverage (V w) (fun x => (φ x - volumeAverage (V w) φ) * (X a x).1 i) ∂P) Y.2
      = ∫ a, ∑ i : Fin d, (((Z.card : ℝ))⁻¹ * ∑ w ∈ Z,
          volumeAverage (V w) (fun x => (φ x - volumeAverage (V w) φ) * (X a x).1 i))
            * Y.2 i ∂P := by
    simp only [vecDot]
    simp_rw [← integral_mul_const]
    rw [← integral_finsetSum Finset.univ (fun i _ => (hint1 i).mul_const (Y.2 i))]
  have hL2 : vecDot Y.1 (fun i => ∫ a, ((Z.card : ℝ))⁻¹ * ∑ w ∈ Z,
        volumeAverage (V w) (fun x => (φ x - volumeAverage (V w) φ) * (X a x).2 i) ∂P)
      = ∫ a, ∑ i : Fin d, (((Z.card : ℝ))⁻¹ * ∑ w ∈ Z,
          volumeAverage (V w) (fun x => (φ x - volumeAverage (V w) φ) * (X a x).2 i))
            * Y.1 i ∂P := by
    conv_lhs => rw [vecDot_comm]
    simp only [vecDot]
    simp_rw [← integral_mul_const]
    rw [← integral_finsetSum Finset.univ (fun i _ => (hint2 i).mul_const (Y.1 i))]
  rw [hL1, hL2, ← integral_add
    (integrable_finsetSum _ fun i _ => (hint1 i).mul_const (Y.2 i))
    (integrable_finsetSum _ fun i _ => (hint2 i).mul_const (Y.1 i))]
  refine integral_congr_ae ?_
  filter_upwards with a
  rw [hstep (fun w i => volumeAverage (V w)
      (fun x => (φ x - volumeAverage (V w) φ) * (X a x).1 i)) Y.2,
    hstep (fun w i => volumeAverage (V w)
      (fun x => (φ x - volumeAverage (V w) φ) * (X a x).2 i)) Y.1,
    ← mul_add, ← Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl (fun w hw => hcell a w hw)

end

end Homogenization.HighContrast.Multiscale
