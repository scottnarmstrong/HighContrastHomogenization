/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.PortableHistory.MajorizationSup

/-!
# The centered maximum below the checkpoint

The first display of the majorization step of `p.fixed.geometry.one.grid.propagation` bounds
the part of the centered maximum `e.scale.selection.fluctuation.history` at the
terminal scale `T` that is carried by the scales at most `b`:

`E[(sup_{j_* ≤ j ≤ b} 3^{-ρ(T-j)} max_{z ∈ 3^j 𝕃_q ∩ ⋄_T^q} |·|_{E_T^q})^Q]`
`  ≤ 3^{-(Qρ-d)(T-b)}(1 + 𝔥_Q(P_{b,T}^q)) 𝓗_q^cen(b)`
`  ≤ 3^{-a(T-b)}(1 + 𝔥_Q(P_{b,T}^q)) 𝓗_q^cen(b)`.

The proof is the printed one.  The terminal cell is partitioned into its
`3^{d(T-b)}` aligned scale-`b` children; on each child the scales at most `b`
contribute exactly the statistic of `e.scale.selection.fluctuation.history` at the
child's center, which has the law of the statistic at the origin by
stationarity of the coefficient law; the change from `E_b^q` to `E_T^q` costs
`|P_{b,T}^q| ≤ 1 + tr(P_{b,T}^q - I)` on each term, hence
`1 + 𝔥_Q(P_{b,T}^q)` after the `Q`-th power; and max-to-sum over the children
produces the counting factor `3^{d(T-b)}`, which the admissibility
`a ≤ Qρ_max - d` absorbs.
-/

namespace Homogenization
namespace HighContrast
namespace PortableHistory

open MeasureTheory

open scoped MatrixOrder Matrix.Norms.L2Operator Matrix ENNReal

noncomputable section

/-- The scalar rearrangement of the terminal renormalization: two nonnegative
weights and one size bound. -/
private theorem weighted_size_le {c₁ c₂ lam S S' : ℝ} (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (h : S ≤ lam * S') : c₁ * c₂ * S ≤ c₁ * lam * (c₂ * S') := by
  calc c₁ * c₂ * S ≤ c₁ * c₂ * (lam * S') := mul_le_mul_of_nonneg_left h (mul_nonneg hc₁ hc₂)
    _ = c₁ * lam * (c₂ * S') := by ring

section Window

variable {d : ℕ} {P : Measure (CoeffSpace d)} {l : ℤ} {q : Mat d} {jStar TMax : ℤ}

/-- The relative size of the two adapted means at the `Q`-th power is the gain
`1 + 𝔥_Q(P_{b,T}^q)`. -/
theorem blockSize_adaptedMean_rpow_le [NeZero d] [IsProbabilityMeasure P] {Q : ℝ}
    (hQ : 0 ≤ Q) (hP : HCPoly.Frozen.IsStationaryLaw P) (hq : IsRoundedGrid l q)
    (hlj : l ≤ jStar) (hfin : ∀ j : ℤ, jStar ≤ j → j ≤ TMax → HasFiniteAdaptedMean P q j)
    {j T : ℤ} (hj : jStar ≤ j) (hjT : j ≤ T) (hT : T ≤ TMax) :
    blockSize (adaptedMean P q j) (adaptedMean P q T) ^ Q ≤
      1 + frakH Q (relMean P q j T) := by
  have hjTM : j ≤ TMax := le_trans hjT hT
  have hEj : (toFullBlockMat (adaptedMean P q j)).PosDef :=
    Recurrence.posDef_toFullBlockMat_adaptedMean hq j (hfin j hj hjTM)
  have hET : (toFullBlockMat (adaptedMean P q T)).PosDef :=
    Recurrence.posDef_toFullBlockMat_adaptedMean hq T (hfin T (le_trans hj hjT) hT)
  have hrel : (toFullBlockMat (relMean P q j T)).PosDef := by
    rw [Recurrence.toFullBlockMat_relMean]
    exact posDef_normalize hEj hET
  have hone : (1 : FullBlockMat d) ≤ toFullBlockMat (relMean P q j T) :=
    one_le_relMean_window hP hq hlj hfin hj hjT hT
  have hsize : blockSize (adaptedMean P q j) (adaptedMean P q T) =
      ‖toFullBlockMat (relMean P q j T)‖ :=
    blockSize_eq_norm (Recurrence.isSymmetricBlockMat_adaptedMean P q j)
      (Recurrence.isSymmetricBlockMat_adaptedMean P q T)
      ((blockPosDef_iff_posDef (Recurrence.isSymmetricBlockMat_adaptedMean P q T)).mpr hET)
  have hnorm : ‖toFullBlockMat (relMean P q j T)‖ ≤
      1 + Matrix.trace (toFullBlockMat (relMean P q j T) - 1) :=
    norm_le_one_add_trace_sub_one hrel hone
  have hgap : (0 : ℝ) ≤ Matrix.trace (toFullBlockMat (relMean P q j T) - 1) :=
    trace_sub_one_nonneg hone
  have hpow := Real.rpow_le_rpow (norm_nonneg (toFullBlockMat (relMean P q j T))) hnorm hQ
  rw [hsize, frakH_eq_rpow]
  linarith only [hpow, hgap]

/-- **The scales at or below the checkpoint.**  The part of the centered maximum
at the terminal scale carried by the scales at most `b` is majorized by the
centered history at `b`, at the cost of the terminal renormalization and of the
counting factor of the aligned subdivision. -/
theorem centered_low_le [NeZero d] [IsProbabilityMeasure P] {Q a rhoMax : ℝ}
    (hQ : 0 < Q) (hadm : a ≤ Q * rhoMax - (d : ℝ))
    (hP : HCPoly.Frozen.IsStationaryLaw P) (hq : IsRoundedGrid l q) (hlj : l ≤ jStar)
    (hfin : ∀ j : ℤ, jStar ≤ j → j ≤ TMax → HasFiniteAdaptedMean P q j)
    {b T : ℤ} (hjb : jStar ≤ b) (hbT : b ≤ T) (hT : T ≤ TMax) :
    ∫⁻ x, (⨆ (j : ℤ) (_ : jStar ≤ j) (_ : j ≤ b) (w : Fin d → ℤ)
        (_ : adaptedCellCenter q j w ∈ adaptedCell q T),
      ENNReal.ofReal ((3 : ℝ) ^ (-rhoMax * ((T : ℝ) - (j : ℝ))) *
        blockSize (blockSub (adaptedResponse q j w x) (adaptedMean P q j))
          (adaptedMean P q T))) ^ Q ∂P ≤
      ENNReal.ofReal ((3 : ℝ) ^ (-a * ((T : ℝ) - (b : ℝ))) *
          (1 + frakH Q (relMean P q b T))) *
        centeredHistory P Q rhoMax q jStar b := by
  classical
  have hqPD : q.PosDef := Recurrence.posDef_of_isRoundedGrid hq
  have hlb : l ≤ b := le_trans hlj hjb
  have hbTM : b ≤ TMax := le_trans hbT hT
  have hEb : (toFullBlockMat (adaptedMean P q b)).PosDef :=
    Recurrence.posDef_toFullBlockMat_adaptedMean hq b (hfin b hjb hbTM)
  have hET : (toFullBlockMat (adaptedMean P q T)).PosDef :=
    Recurrence.posDef_toFullBlockMat_adaptedMean hq T (hfin T (le_trans hjb hbT) hT)
  have hpdb : Book.Ch02.BlockPosDef (adaptedMean P q b) :=
    (blockPosDef_iff_posDef (Recurrence.isSymmetricBlockMat_adaptedMean P q b)).mpr hEb
  have hpdT : Book.Ch02.BlockPosDef (adaptedMean P q T) :=
    (blockPosDef_iff_posDef (Recurrence.isSymmetricBlockMat_adaptedMean P q T)).mpr hET
  obtain ⟨hlam, -⟩ := blockSize_sandwich (Recurrence.isSymmetricBlockMat_adaptedMean P q b)
    (Recurrence.isSymmetricBlockMat_adaptedMean P q T) hpdT
  have hlam0 : (0 : ℝ) ≤ blockSize (adaptedMean P q b) (adaptedMean P q T) :=
    blockSize_nonneg (Recurrence.isSymmetricBlockMat_adaptedMean P q b)
      (Recurrence.isSymmetricBlockMat_adaptedMean P q T) hpdT
  choose v hv using fun y : Fin d → ℤ => Recurrence.exists_intVec_adaptedCellCenter hq hlb y
  obtain ⟨Z, hZ, hcard, -, -, -, -⟩ := Recurrence.aligned_subdivision hq hlb hbT
  have hmem : ∀ y : Fin d → ℤ, adaptedCellCenter q b y ∈ adaptedCell q T → y ∈ Z := by
    intro y hy
    have hy' : y ∈ (↑Z : Set (Fin d → ℤ)) := by rw [hZ]; exact hy
    exact hy'
  -- every admissible pair is read on a child of the terminal cell
  have hpt : ∀ x : CoeffSpace d,
      (⨆ (j : ℤ) (_ : jStar ≤ j) (_ : j ≤ b) (w : Fin d → ℤ)
          (_ : adaptedCellCenter q j w ∈ adaptedCell q T),
        ENNReal.ofReal ((3 : ℝ) ^ (-rhoMax * ((T : ℝ) - (j : ℝ))) *
          blockSize (blockSub (adaptedResponse q j w x) (adaptedMean P q j))
            (adaptedMean P q T))) ≤
      ENNReal.ofReal ((3 : ℝ) ^ (-rhoMax * ((T : ℝ) - (b : ℝ))) *
          blockSize (adaptedMean P q b) (adaptedMean P q T)) *
        ⨆ (y : Fin d → ℤ) (_ : y ∈ Z),
          (⨆ (j : ℤ) (_ : jStar ≤ j) (_ : j ≤ b) (w : Fin d → ℤ)
              (_ : adaptedCellCenter q j w ∈ adaptedCell q b),
            ENNReal.ofReal ((3 : ℝ) ^ (-rhoMax * ((b : ℝ) - (j : ℝ))) *
              blockSize (blockSub (adaptedResponse q j w (translateCoeff (v y) x))
                (adaptedMean P q j)) (adaptedMean P q b))) := by
    intro x
    refine iSup_le fun j => iSup_le fun hj1 => iSup_le fun hj2 => iSup_le fun w =>
      iSup_le fun hw => ?_
    obtain ⟨y, w', hyT, hw'b, hsum⟩ := exists_index_split hqPD hj2 hbT hw
    rw [adaptedResponse_split q (adaptedCellCenter_split q hj2 hsum) (hv y) x]
    have hsize := blockSize_le_mul_blockSize
      (H := blockSub (adaptedResponse q j w' (translateCoeff (v y) x)) (adaptedMean P q j))
      (isSymmetricBlockMat_blockSub
        (Recurrence.isSymmetricBlockMat_adaptedResponse q j w' (translateCoeff (v y) x))
        (Recurrence.isSymmetricBlockMat_adaptedMean P q j))
      (Recurrence.isSymmetricBlockMat_adaptedMean P q b) hpdb
      (Recurrence.isSymmetricBlockMat_adaptedMean P q T) hpdT hlam0 hlam
    have hsplit3 : (3 : ℝ) ^ (-rhoMax * ((T : ℝ) - (j : ℝ))) =
        (3 : ℝ) ^ (-rhoMax * ((T : ℝ) - (b : ℝ))) *
          (3 : ℝ) ^ (-rhoMax * ((b : ℝ) - (j : ℝ))) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      ring_nf
    have hreal : (3 : ℝ) ^ (-rhoMax * ((T : ℝ) - (j : ℝ))) *
        blockSize (blockSub (adaptedResponse q j w' (translateCoeff (v y) x))
          (adaptedMean P q j)) (adaptedMean P q T) ≤
        (3 : ℝ) ^ (-rhoMax * ((T : ℝ) - (b : ℝ))) *
            blockSize (adaptedMean P q b) (adaptedMean P q T) *
          ((3 : ℝ) ^ (-rhoMax * ((b : ℝ) - (j : ℝ))) *
            blockSize (blockSub (adaptedResponse q j w' (translateCoeff (v y) x))
              (adaptedMean P q j)) (adaptedMean P q b)) := by
      rw [hsplit3]
      exact weighted_size_le (by positivity) (by positivity) hsize
    refine le_trans (ENNReal.ofReal_le_ofReal hreal) ?_
    rw [ENNReal.ofReal_mul (mul_nonneg (by positivity) hlam0)]
    refine mul_le_mul_right ?_ _
    exact le_iSup_of_le y (le_iSup_of_le (hmem y hyT)
      (le_iSup_of_le j (le_iSup_of_le hj1 (le_iSup_of_le hj2
        (le_iSup_of_le w' (le_iSup_of_le hw'b le_rfl))))))
  have hbase : AEMeasurable (fun x : CoeffSpace d =>
      ⨆ (j : ℤ) (_ : jStar ≤ j) (_ : j ≤ b) (w : Fin d → ℤ)
          (_ : adaptedCellCenter q j w ∈ adaptedCell q b),
        ENNReal.ofReal ((3 : ℝ) ^ (-rhoMax * ((b : ℝ) - (j : ℝ))) *
          blockSize (blockSub (adaptedResponse q j w x) (adaptedMean P q j))
            (adaptedMean P q b))) P :=
    aemeasurable_adaptedSup hqPD (Recurrence.isSymmetricBlockMat_adaptedMean P q b) hpdb
      (fun j => (3 : ℝ) ^ (-rhoMax * ((b : ℝ) - (j : ℝ)))) jStar b (adaptedCell q b)
  have hconst : ENNReal.ofReal ((3 : ℝ) ^ (-rhoMax * ((T : ℝ) - (b : ℝ))) *
        blockSize (adaptedMean P q b) (adaptedMean P q T)) ^ Q * (Z.card : ℝ≥0∞) ≤
      ENNReal.ofReal ((3 : ℝ) ^ (-a * ((T : ℝ) - (b : ℝ))) *
        (1 + frakH Q (relMean P q b T))) := by
    have htb : (0 : ℝ) ≤ (T : ℝ) - (b : ℝ) := by
      have : (b : ℝ) ≤ (T : ℝ) := by exact_mod_cast hbT
      linarith only [this]
    have htoNat : (((T - b).toNat : ℕ) : ℝ) = (T : ℝ) - (b : ℝ) := by
      have hz : ((T - b).toNat : ℤ) = T - b := Int.toNat_of_nonneg (by omega)
      exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) hz
    have hcast : ((Z.card : ℕ) : ℝ) = (3 : ℝ) ^ ((d : ℝ) * ((T : ℝ) - (b : ℝ))) := by
      rw [hcard]
      push_cast
      rw [← Real.rpow_natCast (3 : ℝ) (d * (T - b).toNat)]
      congr 1
      push_cast [htoNat]
      ring
    have hlamQ : blockSize (adaptedMean P q b) (adaptedMean P q T) ^ Q ≤
        1 + frakH Q (relMean P q b T) :=
      blockSize_adaptedMean_rpow_le hQ.le hP hq hlj hfin hjb hbT hT
    have hsplitpow := three_rpow_admissible_le (Q := Q) (rhoMax := rhoMax) hadm htb hlam0 hlamQ
    rw [ENNReal.ofReal_rpow_of_nonneg (mul_nonneg (by positivity) hlam0) hQ.le,
      ← ENNReal.ofReal_natCast, hcast,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg (mul_nonneg (by positivity) hlam0) Q)]
    exact ENNReal.ofReal_le_ofReal hsplitpow
  rw [centeredHistory]
  calc ∫⁻ x, (⨆ (j : ℤ) (_ : jStar ≤ j) (_ : j ≤ b) (w : Fin d → ℤ)
          (_ : adaptedCellCenter q j w ∈ adaptedCell q T),
        ENNReal.ofReal ((3 : ℝ) ^ (-rhoMax * ((T : ℝ) - (j : ℝ))) *
          blockSize (blockSub (adaptedResponse q j w x) (adaptedMean P q j))
            (adaptedMean P q T))) ^ Q ∂P
      ≤ ∫⁻ x, (ENNReal.ofReal ((3 : ℝ) ^ (-rhoMax * ((T : ℝ) - (b : ℝ))) *
            blockSize (adaptedMean P q b) (adaptedMean P q T)) *
          ⨆ (y : Fin d → ℤ) (_ : y ∈ Z),
            (⨆ (j : ℤ) (_ : jStar ≤ j) (_ : j ≤ b) (w : Fin d → ℤ)
                (_ : adaptedCellCenter q j w ∈ adaptedCell q b),
              ENNReal.ofReal ((3 : ℝ) ^ (-rhoMax * ((b : ℝ) - (j : ℝ))) *
                blockSize (blockSub (adaptedResponse q j w (translateCoeff (v y) x))
                  (adaptedMean P q j)) (adaptedMean P q b)))) ^ Q ∂P :=
        lintegral_mono fun x => ENNReal.rpow_le_rpow (hpt x) hQ.le
    _ = ENNReal.ofReal ((3 : ℝ) ^ (-rhoMax * ((T : ℝ) - (b : ℝ))) *
            blockSize (adaptedMean P q b) (adaptedMean P q T)) ^ Q *
          ∫⁻ x, (⨆ (y : Fin d → ℤ) (_ : y ∈ Z),
            (⨆ (j : ℤ) (_ : jStar ≤ j) (_ : j ≤ b) (w : Fin d → ℤ)
                (_ : adaptedCellCenter q j w ∈ adaptedCell q b),
              ENNReal.ofReal ((3 : ℝ) ^ (-rhoMax * ((b : ℝ) - (j : ℝ))) *
                blockSize (blockSub (adaptedResponse q j w (translateCoeff (v y) x))
                  (adaptedMean P q j)) (adaptedMean P q b)))) ^ Q ∂P := by
        rw [← lintegral_const_mul' _ _
          (ENNReal.rpow_ne_top_of_nonneg hQ.le ENNReal.ofReal_ne_top)]
        exact lintegral_congr fun x => ENNReal.mul_rpow_of_nonneg _ _ hQ.le
    _ ≤ ENNReal.ofReal ((3 : ℝ) ^ (-rhoMax * ((T : ℝ) - (b : ℝ))) *
            blockSize (adaptedMean P q b) (adaptedMean P q T)) ^ Q *
          ((Z.card : ℝ≥0∞) *
            ∫⁻ x, (⨆ (j : ℤ) (_ : jStar ≤ j) (_ : j ≤ b) (w : Fin d → ℤ)
                (_ : adaptedCellCenter q j w ∈ adaptedCell q b),
              ENNReal.ofReal ((3 : ℝ) ^ (-rhoMax * ((b : ℝ) - (j : ℝ))) *
                blockSize (blockSub (adaptedResponse q j w x) (adaptedMean P q j))
                  (adaptedMean P q b))) ^ Q ∂P) :=
        mul_le_mul_right (lintegral_iSup_translate_le hP hQ hbase Z v) _
    _ = ENNReal.ofReal ((3 : ℝ) ^ (-rhoMax * ((T : ℝ) - (b : ℝ))) *
            blockSize (adaptedMean P q b) (adaptedMean P q T)) ^ Q * (Z.card : ℝ≥0∞) *
          ∫⁻ x, (⨆ (j : ℤ) (_ : jStar ≤ j) (_ : j ≤ b) (w : Fin d → ℤ)
              (_ : adaptedCellCenter q j w ∈ adaptedCell q b),
            ENNReal.ofReal ((3 : ℝ) ^ (-rhoMax * ((b : ℝ) - (j : ℝ))) *
              blockSize (blockSub (adaptedResponse q j w x) (adaptedMean P q j))
                (adaptedMean P q b))) ^ Q ∂P := (mul_assoc _ _ _).symm
    _ ≤ _ := mul_le_mul_left hconst _

end Window

end

end PortableHistory
end HighContrast
end Homogenization
