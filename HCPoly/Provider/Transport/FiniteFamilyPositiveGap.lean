/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Transport.FiniteFamilyCollectiveGap
import HCPoly.Provider.Transport.DefectTraceSum
import HCPoly.Provider.Transport.DefectGap
import HCPoly.Provider.Recurrence.PositiveGapClosure
import HCPoly.Provider.Transport.GapFunctions
import HCPoly.Annealed.SchattenDefinedness
import HCPoly.Provider.Transport.CellGap
import HCPoly.Provider.Recurrence.RecurrenceAssembly
import HCPoly.Provider.PortableHistory.MajorizationSize

/-!
# A collective positive-gap estimate for finitely many target cells

The target cells are absorbed simultaneously.  Their trace defects and mean
gaps are summed, but their centered majorants enter through one pathwise
maximum.  This is the form needed before the centered-history supremum is
integrated.
-/

namespace Homogenization
namespace HighContrast
namespace Transport

open MeasureTheory

open scoped ENNReal Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- A finite family of ordered random blocks pays the centered upper family
once and the sum of its deterministic gap budgets. -/
theorem finite_family_positive_gap [NeZero d] {ι : Type*} [DecidableEq ι]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (s : Finset ι) (hs : s.Nonempty) {Q : ℕ} (hQ : 2 ≤ Q) (hQeven : Even Q)
    (wt : ι → ℝ) (hwt : ∀ i ∈ s, 0 < wt i)
    (F G : ι → CoeffSpace d → BlockMat d) (H K : ι → BlockMat d)
    (F0 : BlockMat d)
    (hF0sym : IsSymmetricBlockMat F0) (hF0pd : Book.Ch02.BlockPosDef F0)
    (hFsym : ∀ i ∈ s, ∀ x, IsSymmetricBlockMat (F i x))
    (hGsym : ∀ i ∈ s, ∀ x, IsSymmetricBlockMat (G i x))
    (hHsym : ∀ i ∈ s, IsSymmetricBlockMat (H i))
    (hKsym : ∀ i ∈ s, IsSymmetricBlockMat (K i))
    (hFpos : ∀ i ∈ s, ∀ x, (toFullBlockMat (F i x)).PosSemidef)
    (hFG : ∀ i ∈ s, ∀ x, toFullBlockMat (F i x) ≤ toFullBlockMat (G i x))
    (hFint : ∀ i ∈ s, Integrable (fun x => toFullBlockMat (F i x)) P)
    (hGint : ∀ i ∈ s, Integrable (fun x => toFullBlockMat (G i x)) P)
    (hFmean : ∀ i ∈ s, ∫ x, toFullBlockMat (F i x) ∂P = toFullBlockMat (H i))
    (hGmean : ∀ i ∈ s, ∫ x, toFullBlockMat (G i x) ∂P = toFullBlockMat (K i))
    (hGmeas : ∀ i ∈ s, ∀ α β : BlockCoord d,
      AEStronglyMeasurable (fun x => toFullBlockMat (G i x) α β) P)
    (hIH : ∀ i ∈ s,
      (1 : FullBlockMat d) ≤ toFullBlockMat (normalizedBlock (H i) F0))
    (hHK : ∀ i ∈ s, toFullBlockMat (normalizedBlock (H i) F0) ≤
      toFullBlockMat (normalizedBlock (K i) F0))
    {B : ℝ} (hB : 0 ≤ B)
    (hgap : ∑ i ∈ s, wt i ^ (Q : ℝ) *
      gapG (Q : ℝ) (normalizedBlock (K i) F0) ≤ B) :
    ∫⁻ x, ENNReal.ofReal (s.sup' hs fun i => wt i *
        schattenSize (Q : ℝ) (blockSub (F i x) (H i)) F0) ^ (Q : ℝ) ∂P ≤
      ENNReal.ofReal
          ((((2 * (d : ℝ)) ^ ((Q : ℝ))⁻¹) *
              (1 + (2 * (1 + (2 : ℝ) ^ ((Q : ℝ) - 2) +
                (2 : ℝ) ^ ((Q : ℝ) - 2) *
                  (2 * (d : ℝ)) ^ (1 - ((Q : ℝ))⁻¹))) ^ ((Q : ℝ))⁻¹ +
                (2 * (1 + (2 : ℝ) ^ ((Q : ℝ) - 2) +
                  (2 : ℝ) ^ ((Q : ℝ) - 2) *
                    (2 * (d : ℝ)) ^ (1 - ((Q : ℝ))⁻¹))) ^
                  ((Q : ℝ) - 1)⁻¹)) ^ (Q : ℝ) *
            (2 : ℝ) ^ ((Q : ℝ) - 1)) *
        ((∫⁻ x, ENNReal.ofReal (s.sup' hs fun i => wt i *
            schattenSize (Q : ℝ) (blockSub (G i x) (K i)) F0) ^ (Q : ℝ) ∂P) +
          ENNReal.ofReal (2 * B)) := by
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hQR : (2 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
  have hQ1 : (1 : ℝ) ≤ (Q : ℝ) := by linarith only [hQR]
  have hQ0 : (0 : ℝ) < (Q : ℝ) := lt_of_lt_of_le zero_lt_two hQR
  have hF0full : (toFullBlockMat F0).PosDef :=
    posDef_toFullBlockMat hF0sym hF0pd
  let D : ι → CoeffSpace d → BlockMat d := fun i x =>
    normalizedBlock (blockSub (G i x) (F i x)) F0
  let Yc : ι → CoeffSpace d → BlockMat d := fun i x =>
    normalizedBlock (blockSub (G i x) (K i)) F0
  let Bm : ι → BlockMat d := fun i =>
    blockSub (normalizedBlock (K i) F0) (normalizedBlock (H i) F0)
  let pm : ι → ℝ := fun i => blockOpSize (normalizedBlock (K i) F0)
  let cellF : ι → CoeffSpace d → ℝ := fun i x =>
    schattenSize (Q : ℝ) (blockSub (F i x) (H i)) F0
  let cellD : ι → CoeffSpace d → ℝ := fun i x => schattenNorm (Q : ℝ) (D i x)
  let cellY : ι → CoeffSpace d → ℝ := fun i x => schattenNorm (Q : ℝ) (Yc i x)
  let cellT : ι → CoeffSpace d → ℝ := fun i x =>
    pm i ^ ((Q : ℝ) - 1) * blockTrace (D i x)
  let cellB : ι → ℝ := fun i => blockTrace (Bm i)
  let C : ℝ := 1 + (2 : ℝ) ^ ((Q : ℝ) - 2) +
    (2 : ℝ) ^ ((Q : ℝ) - 2) * (2 * (d : ℝ)) ^ (1 - ((Q : ℝ))⁻¹)
  let Kdim : ℝ := (2 * (d : ℝ)) ^ ((Q : ℝ))⁻¹
  let u : CoeffSpace d → ℝ := fun x => s.sup' hs fun i => wt i * cellD i x
  let v : CoeffSpace d → ℝ := fun x => s.sup' hs fun i => wt i * cellY i x
  let f : CoeffSpace d → ℝ := fun x => s.sup' hs fun i => wt i * cellF i x
  let tsum : CoeffSpace d → ℝ := fun x =>
    ∑ i ∈ s, wt i ^ (Q : ℝ) * cellT i x
  have hDsym : ∀ i ∈ s, ∀ x, IsSymmetricBlockMat (D i x) := by
    intro i hi x
    exact isSymmetricBlockMat_normalizedBlock
      (isSymmetricBlockMat_blockSub (hGsym i hi x) (hFsym i hi x))
  have hYsym : ∀ i ∈ s, ∀ x, IsSymmetricBlockMat (Yc i x) := by
    intro i hi x
    exact isSymmetricBlockMat_normalizedBlock
      (isSymmetricBlockMat_blockSub (hGsym i hi x) (hKsym i hi))
  have hBsym : ∀ i ∈ s, IsSymmetricBlockMat (Bm i) := by
    intro i hi
    exact isSymmetricBlockMat_blockSub
      (isSymmetricBlockMat_normalizedBlock (hKsym i hi))
      (isSymmetricBlockMat_normalizedBlock (hHsym i hi))
  have hDpos : ∀ i ∈ s, ∀ x, (toFullBlockMat (D i x)).PosSemidef := by
    intro i hi x
    simp only [D, Recurrence.toFullBlockMat_normalizedBlock, Recurrence.toFullBlockMat_blockSub]
    exact posSemidef_normalize (Matrix.le_iff.mp (hFG i hi x)) hF0full
  have hBpos : ∀ i ∈ s, (toFullBlockMat (Bm i)).PosSemidef := by
    intro i hi
    simp only [Bm, Recurrence.toFullBlockMat_blockSub]
    exact Matrix.le_iff.mp (hHK i hi)
  have hpm0 : ∀ i ∈ s, 0 ≤ pm i := by
    intro i hi
    have hKps := (posDef_of_one_le ((hIH i hi).trans (hHK i hi))).posSemidef
    simp only [pm, blockOpSize_eq_norm hKps]
    exact norm_nonneg _
  have hC0 : 0 < C := by
    simp only [C]
    have h1 : 0 ≤ (2 : ℝ) ^ ((Q : ℝ) - 2) := Real.rpow_nonneg (by norm_num) _
    have h2 : 0 ≤ (2 * (d : ℝ)) ^ (1 - ((Q : ℝ))⁻¹) :=
      Real.rpow_nonneg (by positivity) _
    positivity
  have hKdim0 : 0 ≤ Kdim := by
    simp only [Kdim]
    exact Real.rpow_nonneg (by positivity) _
  have hcellF0 : ∀ i ∈ s, ∀ x, 0 ≤ cellF i x := by
    intro i hi x
    exact Recurrence.zero_le_schattenNorm
      (isSymmetricBlockMat_normalizedBlock
        (isSymmetricBlockMat_blockSub (hFsym i hi x) (hHsym i hi))) _
  have hcellD0 : ∀ i ∈ s, ∀ x, 0 ≤ cellD i x := fun i hi x =>
    Recurrence.zero_le_schattenNorm (hDsym i hi x) _
  have hcellY0 : ∀ i ∈ s, ∀ x, 0 ≤ cellY i x := fun i hi x =>
    Recurrence.zero_le_schattenNorm (hYsym i hi x) _
  have hcellT0 : ∀ i ∈ s, ∀ x, 0 ≤ cellT i x := by
    intro i hi x
    exact mul_nonneg (Real.rpow_nonneg (hpm0 i hi) _)
      (hDpos i hi x).trace_nonneg
  have hcellB0 : ∀ i ∈ s, 0 ≤ cellB i := fun i hi => (hBpos i hi).trace_nonneg
  have hcellQ : ∀ i ∈ s, ∀ x,
      cellD i x ^ (Q : ℝ) ≤ C * cellT i x +
        C * (cellY i x ^ ((Q : ℝ) - 1) * cellD i x) := by
    intro i hi x
    have hKps := (posDef_of_one_le ((hIH i hi).trans (hHK i hi))).posSemidef
    have hPm : toFullBlockMat (normalizedBlock (K i) F0) ≤
        pm i • (1 : FullBlockMat d) := by
      simp only [pm, blockOpSize_eq_norm hKps]
      exact le_norm_smul_one hKps
    have hsplit : toFullBlockMat (normalizedBlock (G i x) F0) =
        toFullBlockMat (normalizedBlock (K i) F0) + toFullBlockMat (Yc i x) := by
      simp only [Yc, Recurrence.toFullBlockMat_normalizedBlock,
        Recurrence.toFullBlockMat_normalizedBlock, Recurrence.toFullBlockMat_blockSub]
      rw [Matrix.mul_sub, Matrix.sub_mul]
      abel
    have hDG : toFullBlockMat (D i x) ≤
        toFullBlockMat (normalizedBlock (G i x) F0) := by
      simp only [D, Recurrence.toFullBlockMat_normalizedBlock,
        Recurrence.toFullBlockMat_normalizedBlock, Recurrence.toFullBlockMat_blockSub]
      have hFnorm : (0 : FullBlockMat d) ≤
          matSqrt (toFullBlockMat F0)⁻¹ * toFullBlockMat (F i x) *
            matSqrt (toFullBlockMat F0)⁻¹ := Matrix.nonneg_iff_posSemidef.mpr
        (posSemidef_normalize (hFpos i hi x) hF0full)
      rw [Matrix.mul_sub, Matrix.sub_mul]
      exact sub_le_self _ hFnorm
    have hraw := Recurrence.schattenNorm_rpow_le_add_mul_schattenNorm hd
      (hDsym i hi x) (hDpos i hi x) (hYsym i hi x) hQR (hpm0 i hi)
      hsplit hPm hDG
    have ht0 := hcellT0 i hi x
    have hcross0 : 0 ≤ cellY i x ^ ((Q : ℝ) - 1) * cellD i x :=
      mul_nonneg (Real.rpow_nonneg (hcellY0 i hi x) _)
        (hcellD0 i hi x)
    have ha0 : 0 ≤ (2 : ℝ) ^ ((Q : ℝ) - 2) := Real.rpow_nonneg (by norm_num) _
    have hb0 : 0 ≤ (2 : ℝ) ^ ((Q : ℝ) - 2) *
        (2 * (d : ℝ)) ^ (1 - ((Q : ℝ))⁻¹) :=
      mul_nonneg ha0 (Real.rpow_nonneg (by positivity) _)
    dsimp only [cellD, cellY, cellT] at hraw ⊢
    simp only [C]
    nlinarith only [hraw, ht0, hcross0, ha0, hb0]
  have hcellTri : ∀ i ∈ s, ∀ x,
      cellF i x ≤ Kdim * (cellY i x + cellD i x + cellB i) := by
    intro i hi x
    have hHc : IsSymmetricBlockMat
        (normalizedBlock (blockSub (F i x) (H i)) F0) :=
      isSymmetricBlockMat_normalizedBlock
        (isSymmetricBlockMat_blockSub (hFsym i hi x) (hHsym i hi))
    have hid : toFullBlockMat (normalizedBlock (blockSub (F i x) (H i)) F0) =
        toFullBlockMat (Yc i x) - (toFullBlockMat (D i x) - toFullBlockMat (Bm i)) := by
      simp only [D, Yc, Bm, Recurrence.toFullBlockMat_normalizedBlock,
        Recurrence.toFullBlockMat_blockSub]
      noncomm_ring
    simpa only [cellF, cellY, cellD, cellB, Kdim] using
      Recurrence.schattenNorm_le_mul_add_blockTrace hHc (hYsym i hi x)
        (hDsym i hi x) (hBsym i hi) (hBpos i hi) hQ1 hid
  have hDint : ∀ i ∈ s, Integrable (fun x => toFullBlockMat (D i x)) P := by
    intro i hi
    simp only [D, Recurrence.toFullBlockMat_normalizedBlock, Recurrence.toFullBlockMat_blockSub]
    apply integrable_mul_left_mul_right
    change Integrable
      ((fun x => toFullBlockMat (G i x)) - fun x => toFullBlockMat (F i x)) P
    exact (hGint i hi).sub (hFint i hi)
  have hDmean : ∀ i ∈ s, ∫ x, toFullBlockMat (D i x) ∂P = toFullBlockMat (Bm i) := by
    intro i hi
    have hsub : Integrable
        ((fun x => toFullBlockMat (G i x)) - fun x => toFullBlockMat (F i x)) P :=
      (hGint i hi).sub (hFint i hi)
    have hsub' : Integrable
        (fun x => toFullBlockMat (G i x) - toFullBlockMat (F i x)) P := by
      simpa only [Pi.sub_apply] using hsub
    simp only [D, Bm, Recurrence.toFullBlockMat_normalizedBlock, Recurrence.toFullBlockMat_blockSub]
    rw [integral_mul_left_mul_right _ _ hsub',
      integral_sub (hGint i hi) (hFint i hi),
      hGmean i hi, hFmean i hi]
    noncomm_ring
  have htraceEq := eLpNorm_defect_trace_sum_eq (Q := (Q : ℝ)) s wt pm D
    (fun i => normalizedBlock (H i) F0) (fun i => normalizedBlock (K i) F0)
    (fun i hi => (hwt i hi).le) hpm0 hDpos hDint hDmean
  have htraceNonneg : ∀ x, 0 ≤ tsum x := by
    intro x
    simp only [tsum]
    exact Finset.sum_nonneg fun i hi =>
      mul_nonneg (Real.rpow_nonneg (hwt i hi).le _)
        (hcellT0 i hi x)
  have htraceInt : Integrable tsum P := by
    simp only [tsum, cellT]
    refine integrable_finset_sum s fun i hi => ?_
    have hiInt := (Recurrence.integrable_blockTrace (hDint i hi)).const_mul
      (wt i ^ (Q : ℝ) * pm i ^ ((Q : ℝ) - 1))
    simpa only [mul_assoc] using hiInt
  have htraceL : ∫⁻ x, ENNReal.ofReal (tsum x) ∂P =
      ENNReal.ofReal (∑ i ∈ s, wt i ^ (Q : ℝ) *
        pm i ^ ((Q : ℝ) - 1) * blockTrace (Bm i)) := by
    have hnorm : ∀ x, ‖tsum x‖ₑ = ENNReal.ofReal (tsum x) := fun x =>
      Real.enorm_eq_ofReal (htraceNonneg x)
    have htraceEq' : eLpNorm tsum 1 P =
        ENNReal.ofReal (∑ i ∈ s, wt i ^ (Q : ℝ) *
          pm i ^ ((Q : ℝ) - 1) * blockTrace (Bm i)) := by
      simpa only [tsum, cellT, Bm, mul_assoc] using htraceEq
    rw [eLpNorm_one_eq_lintegral_enorm] at htraceEq'
    rw [lintegral_congr hnorm] at htraceEq'
    exact htraceEq'
  have hcharges : ∑ i ∈ s, wt i ^ (Q : ℝ) *
        (pm i ^ ((Q : ℝ) - 1) * blockTrace (Bm i) + cellB i ^ (Q : ℝ)) ≤ B := by
    refine (Finset.sum_le_sum fun i hi => ?_).trans hgap
    have hterms := defect_terms_le_gapG hQ1 (hIH i hi) (hHK i hi)
    dsimp only [pm, cellB, Bm]
    exact mul_le_mul_of_nonneg_left hterms (Real.rpow_nonneg (hwt i hi).le _)
  have htraceBudget : ∫⁻ x, ENNReal.ofReal (tsum x) ∂P ≤ ENNReal.ofReal B := by
    rw [htraceL]
    refine ENNReal.ofReal_le_ofReal ?_
    exact (Finset.sum_le_sum fun i hi => by
      have hpow0 := Real.rpow_nonneg (hcellB0 i hi) (Q : ℝ)
      have hw0 := Real.rpow_nonneg (hwt i hi).le (Q : ℝ)
      nlinarith only [hpow0, hw0]).trans hcharges
  have hBsum : ∑ i ∈ s, (wt i * cellB i) ^ (Q : ℝ) ≤ B := by
    refine (Finset.sum_le_sum fun i hi => ?_).trans hcharges
    rw [Real.mul_rpow (hwt i hi).le (hcellB0 i hi)]
    have htrace0 : 0 ≤ pm i ^ ((Q : ℝ) - 1) * blockTrace (Bm i) :=
      mul_nonneg (Real.rpow_nonneg (hpm0 i hi) _) (hcellB0 i hi)
    exact mul_le_mul_of_nonneg_left (by linarith only [htrace0])
      (Real.rpow_nonneg (hwt i hi).le _)
  have hpath := finite_family_collective_gap_pointwise s hs hQR hC0 hKdim0 hB
    wt hwt cellF cellD cellY cellT cellB hcellF0 hcellD0 hcellY0 hcellT0
    hcellB0 hcellQ hcellTri u v f tsum (fun _ => rfl) (fun _ => rfl)
    (fun _ => rfl) (fun _ => rfl) hBsum
  have hvmeas : AEMeasurable (fun x => ENNReal.ofReal (v x) ^ (Q : ℝ)) P := by
    have hcellYm : ∀ i ∈ s, AEStronglyMeasurable (cellY i) P := by
      intro i hi
      exact Recurrence.aestronglyMeasurable_schattenNorm (hYsym i hi) hQeven
        (Recurrence.aestronglyMeasurable_entry_normalizedBlock_blockSub F0
          (hGmeas i hi) (fun _ _ => aestronglyMeasurable_const))
    have hvstrong : AEStronglyMeasurable v P := by
      have hae : AEMeasurable (s.sup' hs fun i x => wt i * cellY i x) P :=
        Finset.sup'_induction hs (fun i x => wt i * cellY i x)
          (fun (_f : CoeffSpace d → ℝ) (hf' : AEMeasurable _f P)
              (_g : CoeffSpace d → ℝ) (hg' : AEMeasurable _g P) => hf'.sup hg')
          (fun i hi => ((hcellYm i hi).const_mul (wt i)).aemeasurable)
      have hvEq : v = s.sup' hs fun i x => wt i * cellY i x := by
        funext x
        simp only [v, Finset.sup'_apply]
      rw [hvEq]
      exact hae.aestronglyMeasurable
    exact ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
      (ENNReal.measurable_ofReal.comp_aemeasurable hvstrong.aemeasurable)
  have htsmeas : AEMeasurable (fun x => ENNReal.ofReal (tsum x)) P :=
    ENNReal.measurable_ofReal.comp_aemeasurable htraceInt.aestronglyMeasurable.aemeasurable
  have hfac0 : 0 ≤ (Kdim * (1 + (2 * C) ^ ((Q : ℝ))⁻¹ +
      (2 * C) ^ ((Q : ℝ) - 1)⁻¹)) ^ (Q : ℝ) * (2 : ℝ) ^ ((Q : ℝ) - 1) :=
    mul_nonneg (Real.rpow_nonneg (mul_nonneg hKdim0 (by positivity)) _)
      (Real.rpow_nonneg (by norm_num) _)
  have hlin : ∫⁻ x, ENNReal.ofReal (f x) ^ (Q : ℝ) ∂P ≤
      ENNReal.ofReal ((Kdim * (1 + (2 * C) ^ ((Q : ℝ))⁻¹ +
          (2 * C) ^ ((Q : ℝ) - 1)⁻¹)) ^ (Q : ℝ) *
            (2 : ℝ) ^ ((Q : ℝ) - 1)) *
        ((∫⁻ x, ENNReal.ofReal (v x) ^ (Q : ℝ) ∂P) + ENNReal.ofReal (2 * B)) := by
    have hmono : (∫⁻ x, ENNReal.ofReal (f x) ^ (Q : ℝ) ∂P) ≤
        ∫⁻ x, ENNReal.ofReal
          (((Kdim * (1 + (2 * C) ^ ((Q : ℝ))⁻¹ +
              (2 * C) ^ ((Q : ℝ) - 1)⁻¹)) ^ (Q : ℝ) *
                (2 : ℝ) ^ ((Q : ℝ) - 1)) *
            (v x ^ (Q : ℝ) + (tsum x + B))) ∂P := by
      refine lintegral_mono fun x => ?_
      have hf0 : 0 ≤ f x := by
        simp only [f]
        exact (mul_nonneg (hwt hs.choose hs.choose_spec).le
          (hcellF0 hs.choose hs.choose_spec x)).trans
            (Finset.le_sup' (fun i => wt i * cellF i x) hs.choose_spec)
      rw [ENNReal.ofReal_rpow_of_nonneg hf0 hQ0.le]
      exact ENNReal.ofReal_le_ofReal (hpath x)
    refine hmono.trans ?_
    · simp_rw [ENNReal.ofReal_mul hfac0]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      have hsummeas : AEMeasurable (fun x =>
          ENNReal.ofReal (v x) ^ (Q : ℝ) + ENNReal.ofReal (tsum x)) P :=
        hvmeas.add htsmeas
      have hpoint : ∀ x, ENNReal.ofReal (v x ^ (Q : ℝ) + (tsum x + B)) =
          ENNReal.ofReal (v x) ^ (Q : ℝ) + ENNReal.ofReal (tsum x) +
            ENNReal.ofReal B := by
        intro x
        have hv0 : 0 ≤ v x := by
          simp only [v]
          exact (mul_nonneg (hwt hs.choose hs.choose_spec).le
            (hcellY0 hs.choose hs.choose_spec x)).trans
              (Finset.le_sup' (fun i => wt i * cellY i x) hs.choose_spec)
        rw [ENNReal.ofReal_add (Real.rpow_nonneg hv0 _) (add_nonneg (htraceNonneg x) hB),
          ENNReal.ofReal_add (htraceNonneg x) hB,
          ENNReal.ofReal_rpow_of_nonneg hv0 hQ0.le]
        exact (add_assoc _ _ _).symm
      simp_rw [hpoint]
      rw [lintegral_add_left' hsummeas, lintegral_add_left' hvmeas]
      refine mul_le_mul' le_rfl ?_
      rw [add_assoc]
      refine add_le_add le_rfl ?_
      rw [lintegral_const, measure_univ, mul_one]
      refine (add_le_add htraceBudget le_rfl).trans ?_
      rw [← ENNReal.ofReal_add hB hB]
      exact ENNReal.ofReal_le_ofReal (by ring_nf; exact le_rfl)
  simpa only [cellF, cellY, f, v, Kdim, C] using hlin

end

end Transport
end HighContrast
end Homogenization
