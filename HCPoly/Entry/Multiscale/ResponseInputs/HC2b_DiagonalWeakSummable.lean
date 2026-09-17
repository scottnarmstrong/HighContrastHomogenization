import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakSeminormSplit
import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakPrimalLHS

/-!
# Summability of the recentred, metric-transported cell-average family

The scale-average seminorm `besovSeminorm` is a real `tsum`, so every identity that splits it
needs its family to be summable.  The tree already proves the needed summability above the
cell-average estimate in `AdaptedWeakRouteCore.lean`, but that module sits above the estimate in
import order, so the estimate cannot reach it.  This module re-lands the same fact below it, on
the two public cell-average identities of `HC2b_DiagonalWeakPrimalLHS.lean`.

The engine is `summable_besov_cellAverageFamily` (`HC2_WeakSeminorm.lean`): for the transported
recentring `x ↦ A (X x - ⟨X⟩_{U_t})` the family of cell averages is summable as soon as the
transported field is in `L²` on `U_t`; the recentred family of the statement is that family,
restricted to the labels `w ∈ triadicIndexBox d n` the seminorm reads.

The second statement is the unsplit normalisation of the seminorm: pulling the factor
`3 ^ (-(t/2))` inside the `tsum` moves the weight of the `n`-th term to `3 ^ (-(n/2))`.  It is a
series identity and needs no summability.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

variable {d : ℕ} [NeZero d]

/-! ### Local helpers

These are the `L²`-to-integrability ingredients of the proof.  They are not imported because the
copies in `AdaptedWeakRouteCore.lean` are `private` and that module is above this one in import
order.  The cell-average identities themselves are the public
`h6a_cellAverage_blockMatVecMul_pub` and `h6a_cellAverage_sub_const_pub`. -/

omit [NeZero d] in
/-- A slot of a vector `L²` field on `U` is integrable on every finite-measure subset `V ⊆ U`. -/
private theorem h6aSum_integrableOn_slot {U V : Set (Vec d)} (hVU : V ⊆ U)
    (hVfin : volume V ≠ ⊤) {g : Vec d → Vec d} (hg : MemVectorL2 U g) (j : Fin d) :
    IntegrableOn (fun x => g x j) V := by
  have : IsFiniteMeasure (volume.restrict V) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_of_le_of_ne le_top hVfin⟩
  have h2 : MemLp (fun x => g x j) 2 (volume.restrict U) :=
    (MeasureTheory.memLp_pi_iff.mp hg) j
  have h2' : MemLp (fun x => g x j) 2 (volume.restrict V) :=
    h2.mono_measure (Measure.restrict_mono hVU le_rfl)
  exact MemLp.integrable (by norm_num) h2'

omit [NeZero d] in
/-- The squared pointwise norm of a block field whose two slots are `L²` is `L¹`. -/
private theorem h6aSum_memLp_one_blockVecDot {U : Set (Vec d)} {X : Vec d → BlockVec d}
    (h1 : MemVectorL2 U (fun x => (X x).1)) (h2 : MemVectorL2 U (fun x => (X x).2)) :
    MemLp (fun x => blockVecDot (X x) (X x)) 1 (volume.restrict U) := by
  have e1 := MeasureTheory.memLp_pi_iff.mp h1
  have e2 := MeasureTheory.memLp_pi_iff.mp h2
  rw [memLp_one_iff_integrable]
  have hA : Integrable (fun x => ∑ i, (X x).1 i * (X x).1 i) (volume.restrict U) :=
    integrable_finsetSum _ fun i _ => by
      simpa [Pi.mul_apply] using! (e1 i).integrable_mul (e1 i)
  have hB : Integrable (fun x => ∑ i, (X x).2 i * (X x).2 i) (volume.restrict U) :=
    integrable_finsetSum _ fun i _ => by
      simpa [Pi.mul_apply] using! (e2 i).integrable_mul (e2 i)
  simpa [blockVecDot, vecDot] using! hA.add hB

/-- **The summability half.**  The recentred, metric-transported cell-average family of an
`L²(U_t)` block field is summable with the scale weights of the seminorm.  The engine
`summable_besov_cellAverageFamily` is applied to the transported recentring
`X' = x ↦ A (X x - ⟨X⟩_{U_t})`; on the read cells the cell average of `X'` is the transported
recentred cell average, by the two public cell-average identities. -/
theorem h6a_summable_centred (q : Mat d) (hq : IsUnit q) (t : ℤ) (A : BlockMat d)
    (X : Vec d → BlockVec d)
    (hs1 : MemVectorL2 (HighContrast.adaptedCell q t) (fun x => (X x).1))
    (hs2 : MemVectorL2 (HighContrast.adaptedCell q t) (fun x => (X x).2)) :
    Summable (fun n : ℕ => (3 : ℝ) ^ (((t : ℝ) - (n : ℝ)) / 2) *
      Real.sqrt ((((triadicIndexBox d n).card : ℝ))⁻¹ *
        ∑ w ∈ triadicIndexBox d n,
          blockVecDot
            (blockMatVecMul A (cellAverageFamily q t X n w - cellAverage (HighContrast.adaptedCell q t) X))
            (blockMatVecMul A (cellAverageFamily q t X n w -
              cellAverage (HighContrast.adaptedCell q t) X)))) := by
  classical
  have hUfin : volume (HighContrast.adaptedCell q t) ≠ ⊤ := by
    rw [Geometry.volume_adaptedCell]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  have : IsFiniteMeasure (volume.restrict (HighContrast.adaptedCell q t)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_of_le_of_ne le_top hUfin⟩
  set C : BlockVec d := cellAverage (HighContrast.adaptedCell q t) X with hCdef
  set X' : Vec d → BlockVec d := fun x => blockMatVecMul A (X x - C) with hX'def
  have hd1 : MemVectorL2 (HighContrast.adaptedCell q t) (fun x => (X x).1 - C.1) :=
    hs1.sub (memLp_const C.1)
  have hd2 : MemVectorL2 (HighContrast.adaptedCell q t) (fun x => (X x).2 - C.2) :=
    hs2.sub (memLp_const C.2)
  have hX'1 : MemVectorL2 (HighContrast.adaptedCell q t) (fun x => (X' x).1) :=
    (memVectorL2_matVecMul_const A.upperLeft hd1).add
      (memVectorL2_matVecMul_const A.upperRight hd2)
  have hX'2 : MemVectorL2 (HighContrast.adaptedCell q t) (fun x => (X' x).2) :=
    (memVectorL2_matVecMul_const A.lowerLeft hd1).add
      (memVectorL2_matVecMul_const A.lowerRight hd2)
  have hX'mem : MemLp (fun x => blockVecDot (X' x) (X' x)) 1
      (volume.restrict (HighContrast.adaptedCell q t)) :=
    h6aSum_memLp_one_blockVecDot hX'1 hX'2
  have hsum' := summable_besov_cellAverageFamily q hq t X' hX'mem
  refine hsum'.congr fun n => ?_
  have hV : ∀ w ∈ triadicIndexBox d n,
      cellAverageFamily q t X' n w = blockMatVecMul A (cellAverageFamily q t X n w - C) := by
    intro w hw
    have hsub : adaptedCellAtCenter q (t - (n : ℤ)) w ⊆ HighContrast.adaptedCell q t :=
      adaptedCellAtCenter_subset_adaptedCell q t n hw
    have hVfin : volume (adaptedCellAtCenter q (t - (n : ℤ)) w) ≠ ⊤ :=
      Geometry.volume_adaptedCellAtCenter_ne_top q (t - (n : ℤ)) w
    have : IsFiniteMeasure (volume.restrict (adaptedCellAtCenter q (t - (n : ℤ)) w)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact lt_of_le_of_ne le_top hVfin⟩
    have hVpos : (volume (adaptedCellAtCenter q (t - (n : ℤ)) w)).toReal ≠ 0 :=
      ne_of_gt (volume_adaptedCellAtCenter_toReal_pos q hq (t - (n : ℤ)) w)
    have h1 : ∀ j, IntegrableOn (fun x => (X x).1 j) (adaptedCellAtCenter q (t - (n : ℤ)) w) :=
      fun j => h6aSum_integrableOn_slot hsub hVfin hs1 j
    have h2 : ∀ j, IntegrableOn (fun x => (X x).2 j) (adaptedCellAtCenter q (t - (n : ℤ)) w) :=
      fun j => h6aSum_integrableOn_slot hsub hVfin hs2 j
    have hc1 : ∀ j, IntegrableOn (fun x => (X x - C).1 j) (adaptedCellAtCenter q (t - (n : ℤ)) w) :=
      fun j => (h1 j).sub (integrable_const (C.1 j))
    have hc2 : ∀ j, IntegrableOn (fun x => (X x - C).2 j) (adaptedCellAtCenter q (t - (n : ℤ)) w) :=
      fun j => (h2 j).sub (integrable_const (C.2 j))
    unfold cellAverageFamily
    rw [hX'def]
    rw [h6a_cellAverage_blockMatVecMul_pub A (fun x => X x - C) hc1 hc2,
      h6a_cellAverage_sub_const_pub hVfin hVpos X C h1 h2]
  have hsumeq : ∑ w ∈ triadicIndexBox d n,
        blockVecDot (cellAverageFamily q t X' n w) (cellAverageFamily q t X' n w)
      = ∑ w ∈ triadicIndexBox d n,
        blockVecDot (blockMatVecMul A (cellAverageFamily q t X n w - C))
          (blockMatVecMul A (cellAverageFamily q t X n w - C)) :=
    Finset.sum_congr rfl fun w hw => by rw [hV w hw]
  rw [hsumeq]

end

end Homogenization.HighContrast.Multiscale
