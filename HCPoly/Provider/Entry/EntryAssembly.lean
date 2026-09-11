/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Entry.Tolerances
import HCPoly.Provider.Entry.AdapterAssembly
import HCPoly.Provider.Entry.TerminalBlocks
import HCPoly.Provider.Entry.ContrastBridge
import HCPoly.Provider.Entry.ScaleAccount
import HCPoly.Frozen.RandomSourceWindow
import HCPoly.Frozen.RandomAdaptedResponse
import HCPoly.Frozen.RandomSourceGlobalSelection
import HCPoly.Frozen.RandomPersistenceTransfer

/-!
# Polynomial entry from the random-source development

The entry threshold and the terminal scale are assembled from the dimensional
tolerances, the bounded-window multiplier, the fixed-window response, the
global selection, persistence and Euclidean transfer, and the final scale
account.  The fixed-window response is consumed once, where its structural
constants are chosen; all later steps use only the resulting response package.

There are no definitions in this file.
-/

open Homogenization
open Homogenization.HighContrast
open Homogenization.HighContrast.Recurrence
open Homogenization.HighContrast.Transport
open Homogenization.HighContrast.Sharp
open MeasureTheory

open scoped ENNReal

noncomputable section

/-- **`t.polynomial.entry`**: the random-source entry
generation has polynomial size in the intrinsic contrast and gauge growth
witness. -/
theorem Homogenization.HighContrast.Entry.polynomial_entry_assembly
    (d : ℕ) (hd : 2 ≤ d)
    (cSc δ₀ cEnd : ℝ) (hcSc : 0 < cSc) (hδ₀ : δ₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hcEnd : 0 < cEnd)
    (hcal : (1 + δ₀) ^ 2 * (1 + cEnd) ≤ 1 + cSc) :
    ∃ cStar : ℝ, cStar ∈ Set.Ioc 0 (min cSc cEnd) ∧
      ∀ g : ℝ, g ∈ Set.Ico (0 : ℝ) 1 →
        ∃ C : ℝ, 0 < C ∧
          ∀ (P : MeasureTheory.Measure (Homogenization.HighContrast.CoeffSpace d))
            (E : Homogenization.BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
            (S : Homogenization.HighContrast.CoeffSpace d → ℝ),
            MeasureTheory.IsProbabilityMeasure P →
            HCPoly.Frozen.IsStationaryLaw P →
            HCPoly.Frozen.IsUnitRangeLaw P →
            HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S →
            ∃ mEnt : ℕ,
              (mEnt : ℤ) ≤
                ⌈C * Real.logb 3
                  (2 + Homogenization.HighContrast.aspectRatio E * K)⌉ ∧
              Homogenization.HighContrast.annealedContrast P (mEnt : ℤ) - 1 ≤ cStar ∧
              (3 : ℝ) ^ (mEnt : ℕ) ≤
                3 * (2 + Homogenization.HighContrast.aspectRatio E * K) ^ C
    := by
  classical
  haveI : NeZero d := ⟨by omega⟩
  have hcEndSc : cEnd ≤ cSc := by
    have hdeltaOne : (1 : ℝ) ≤ 1 + δ₀ := by
      linarith only [hδ₀.1]
    have hsquare : (1 : ℝ) ≤ (1 + δ₀) ^ 2 := one_le_pow₀ hdeltaOne
    have hcEndNonneg : (0 : ℝ) ≤ 1 + cEnd := by
      linarith only [hcEnd]
    have hproduct : 1 + cEnd ≤ (1 + δ₀) ^ 2 * (1 + cEnd) := by
      calc
        1 + cEnd = 1 * (1 + cEnd) := by ring
        _ ≤ (1 + δ₀) ^ 2 * (1 + cEnd) :=
          mul_le_mul_of_nonneg_right hsquare hcEndNonneg
    linarith only [hproduct, hcal]
  have hmin : min cSc cEnd = cEnd := min_eq_right hcEndSc
  obtain ⟨cStar, deltaAd, etaPlus, etaMinus, etaIso, hcStarMem, hdeltaAdLo,
    hdeltaAdHi, hetaPlusLo, hetaPlusHi, hetaMinusLo, hetaMinusHi, hetaIsoLo,
    hetaIsoHi, hetaPlusIso, hetaMinusIso, hhier⟩ :=
    Entry.exists_entry_tolerances d hd cSc cEnd hcSc hcEnd
  have hcStar : 0 < cStar := hcStarMem.1
  have hcStarEnd : cStar ≤ cEnd := by
    rw [← hmin]
    exact hcStarMem.2
  have hcStarMem' : cStar ∈ Set.Ioc 0 (min cSc cEnd) := by
    refine ⟨hcStar, ?_⟩
    rw [hmin]
    exact hcStarEnd
  refine ⟨cStar, hcStarMem', ?_⟩
  intro g hg
  have hQ2 : 2 ≤ (initExpQ d g : ℝ) := by
    have hpos : 0 < 2 * ((d : ℝ) + 1) / (1 - g) := by
      have hgpos : (0 : ℝ) < 1 - g := by
        linarith only [hg.2]
      positivity
    have hceil : 1 ≤ ⌈2 * ((d : ℝ) + 1) / (1 - g)⌉₊ :=
      Nat.ceil_pos.mpr hpos
    have hnat : (2 : ℕ) ≤ initExpQ d g := by
      simpa [initExpQ] using Nat.mul_le_mul_left 2 hceil
    exact_mod_cast hnat
  -- the window's dimensional constant, before the law
  obtain ⟨Cd0, _hCd0, hwin⟩ :=
    HCPoly.Frozen.random_source_window d hd g hg
      ((initExpQ d g : ℕ) : ℝ)
      hQ2
  have hCd1 : (1 : ℝ) ≤ max 1 Cd0 := le_max_left _ _
  have hCdge : Cd0 ≤ max 1 Cd0 := le_max_right _ _
  -- The fixed-window response is consumed here, at its structural choices.
  obtain ⟨epsCal, deltaDet, H, eta, etaDr, hepsCalLo, hepsCalHi, hdeltaDetLo,
    hdeltaDetHi, hH, hetaLo, hetaHi, hetaDrLo, hetaDrHi, hresp2⟩ :=
    HCPoly.Frozen.random_adapted_response d hd g hg deltaAd hdeltaAdLo hdeltaAdHi
      (max 1 Cd0) hCd1
  have hpowle :
      (2 : ℝ) ^ (-(initExpQ d g : ℤ)) ≤ 1 := by
    apply zpow_le_one_of_nonpos₀ (by norm_num)
    simp
  have hprofLo :
      0 < (2 : ℝ) ^ (-(initExpQ d g : ℤ)) * eta := by
    positivity
  have hprofHi :
      (2 : ℝ) ^ (-(initExpQ d g : ℤ)) * eta ≤ 1 := by
    calc (2 : ℝ) ^ (-(initExpQ d g : ℤ)) * eta
        ≤ 1 * eta := mul_le_mul_of_nonneg_right hpowle hetaLo.le
      _ = eta := one_mul _
      _ ≤ 1 := by linarith only [hetaHi]
  -- the selector's pre-law clause
  obtain ⟨Arad, _Agrid, hAradPos, _hAgridPos, etaIn, etaOut, epsSt, deltaTerm,
    _hetaInPos, _hetaOutPos, _hepsStPos, hdeltaTermPos, Cport, hCport, hcaps1,
    hcaps2, hsel2⟩ :=
    HCPoly.Frozen.random_source_global_selection d hd g hg cStar hcStar epsCal
      hepsCalLo (by linarith only [hepsCalHi]) etaDr hetaDrLo
      (le_trans hetaDrHi (min_le_left _ _))
      ((2 : ℝ) ^ (-(initExpQ d g : ℤ)) * eta)
      hprofLo hprofHi deltaDet hdeltaDetLo hdeltaDetHi H hH (max 1 Cd0) hCd1
  obtain ⟨Bresp, _hBrespPos, _hslack, _hterm, _hrow, hresp3⟩ :=
    hresp2 Arad hAradPos.le
  obtain ⟨B, Cexec, Csel, hBmin, hCexec, hCsel, _hcut1, _hcut2, hsel3⟩ :=
    hsel2 (max 1 Bresp) (le_max_left _ _)
  -- the Euclidean adapter and the two-gap constant, both before the law
  obtain ⟨CAE, hCAElo, hCAE⟩ := Entry.exists_euclidean_adapter d hd g hg
  obtain ⟨Cgap, hCgapPos, htrans⟩ :=
    HCPoly.Frozen.random_persistence_transfer d hd g hg (max 1 Cd0) hCd1 CAE
      hCAElo hCAE 2 (by norm_num) deltaAd hdeltaAdLo.le hdeltaAdHi etaPlus
      etaMinus etaIso hetaPlusLo hetaPlusHi hetaMinusLo hetaMinusHi hetaIsoLo
      hetaIsoHi hetaPlusIso hetaMinusIso Arad hAradPos.le
  -- the constant of the theorem, fixed before the law
  obtain ⟨C, hCpos, hacct⟩ :=
    Entry.exists_entry_scale_constant d hd g hg Cexec Csel Cgap hCexec hCsel
      hCgapPos
  refine ⟨C, hCpos, ?_⟩
  intro P E Ψ K S hP hstat hunit hdag
  haveI := hP
  have hAR : 1 ≤ aspectRatio E :=
    one_le_aspectRatio_of_coarseEllipticityDagger hdag
  have hLam : 1 ≤ Real.logb 3 (2 + aspectRatio E) := by
    have hthree : (3 : ℝ) ≤ 2 + aspectRatio E := by
      linarith only [hAR]
    have hlog := Real.logb_le_logb_of_le (b := 3) (by norm_num)
      (by norm_num : (0 : ℝ) < 3) hthree
    rwa [Real.logb_self_eq_one (by norm_num)] at hlog
  have hLam0 :
      (0 : ℝ) ≤ Real.logb 3 (2 + aspectRatio E) :=
    le_trans zero_le_one hLam
  obtain ⟨jdag, hjdagdef⟩ :
      ∃ j : ℤ,
        j = coupledExecBurn d
          ((initExpQ d g : ℕ) : ℝ) K Cexec
          (Real.logb 3 (2 + aspectRatio E)) := ⟨_, rfl⟩
  obtain ⟨Mexec, hMexecdef⟩ :
      ∃ m : ℤ,
        m = jdag +
          ⌈Cexec *
            Real.logb 3 (2 + aspectRatio E)⌉ := ⟨_, rfl⟩
  obtain ⟨hwinfacts, hsel4⟩ :=
    hsel3 P E Ψ K S hP hstat hunit hdag _ rfl jdag Mexec hjdagdef hMexecdef
  obtain ⟨_hMheight, hcw, _hburn⟩ := hwinfacts
  obtain ⟨_w1, _w2, _w3, Y, hYmul, hYint, hYlq, _w4, _w5⟩ :=
    hwin (max 1 Cd0) hCdge P E Ψ K S hP hstat hdag _ _ hcw
  obtain ⟨E0, m0, q, s, t, hsymE0, hposE0, hm0, hq, htdef, hscales, henc, hcalib,
    hhist, hsrcY⟩ := hsel4
  obtain ⟨hsrc, _hmax⟩ := hsrcY Y hYmul
  obtain ⟨hsLo, htUp, hecc, _hgrid⟩ := hscales
  obtain ⟨henc1, henc2⟩ := henc
  obtain ⟨hcal1, hcal2, hdetT, hdrift⟩ := hcalib
  obtain ⟨_hh1, hh2, hh3, hh4, _hh5⟩ := hhist
  -- the scale bookkeeping of the entry argument
  have hburn0 :
      (0 : ℤ) ≤ sourceBurn d
        ((initExpQ d g : ℕ) : ℝ) K :=
    le_trans (Int.natCast_nonneg _) (le_max_left _ _)
  have hburnj :
      sourceBurn d
        ((initExpQ d g : ℕ) : ℝ) K ≤ jdag := by
    rw [hjdagdef]; exact le_max_left _ _
  have hjdag0 : (0 : ℤ) ≤ jdag := le_trans hburn0 hburnj
  have hB1 : (1 : ℝ) ≤ B := le_trans (le_max_left 1 Bresp) hBmin
  have hBL :
      (1 : ℝ) ≤ B * Real.logb 3 (2 + aspectRatio E) :=
    hLam.trans (le_mul_of_one_le_left hLam0 hB1)
  have hceil1 :
      (1 : ℤ) ≤
        ⌈B * Real.logb 3 (2 + aspectRatio E)⌉ := by
    have := le_trans hBL
      (Int.le_ceil
        (B * Real.logb 3 (2 + aspectRatio E)))
    exact_mod_cast this
  have hceil0 :
      (0 : ℤ) ≤
        ⌈B * Real.logb 3 (2 + aspectRatio E)⌉ :=
    le_trans zero_le_one hceil1
  have hjs : jdag ≤ s := le_trans (le_add_of_nonneg_right hceil0) hsLo
  have hHnn : (0 : ℤ) ≤ (H : ℤ) := Int.natCast_nonneg _
  have hst : s ≤ t := by rw [htdef]; linarith only [hHnn]
  have hjt : jdag ≤ t := le_trans hjs hst
  have h1s : (1 : ℤ) ≤ s :=
    le_trans (by linarith only [hjdag0, hceil1]) hsLo
  have hHt : (H : ℤ) < t := by rw [htdef]; linarith only [h1s]
  have h1t : (1 : ℤ) ≤ t := le_trans h1s hst
  have hbufle :
      ⌈Bresp * Real.logb 3 (2 + aspectRatio E)⌉ ≤
        ⌈B * Real.logb 3 (2 + aspectRatio E)⌉ := by
    refine Int.ceil_le_ceil ?_
    have hBr : Bresp ≤ B := le_trans (le_max_right 1 Bresp) hBmin
    exact mul_le_mul_of_nonneg_right hBr hLam0
  have hbuf :
      jdag +
          ⌈Bresp *
            Real.logb 3 (2 + aspectRatio E)⌉ ≤ s :=
    le_trans (by linarith only [hbufle]) hsLo
  -- the blocks of the terminal range and the two sharp orders
  have hm0pos : m0.PosDef := by
    rw [hm0]
    exact posDef_canonMetric
      (posDef_toFullBlockMat hsymE0 hposE0)
  have hqpos : q.PosDef := by
    rw [hq]
    exact posDef_of_isRoundedGrid
      (isRoundedGrid_roundedGrid_of_isCoupledWindow hcw hm0pos)
  have hbl :=
    Entry.terminal_range_blocks d hd g hg P E Ψ K S hstat hdag (max 1 Cd0)
      m0 q jdag t Mexec Y hm0pos hq hcw hYmul henc1
  have hfinS := (hbl s hjs hst).1
  have hposS := (hbl s hjs hst).2.1
  have hEtEs := (hbl s hjs hst).2.2
  have hfinT := (hbl t hjt le_rfl).1
  have hposT := (hbl t hjt le_rfl).2.1
  have hshS :
      BlockMatLoewnerLE
        (blockSharp
          (annealedBlock P
            (adaptedCell q s)))
        (annealedBlock P
          (adaptedCell q s)) :=
    Sharp.blockSharp_annealedBlock_le_of_nonempty
      (isOpenBoundedConvexDomain_adaptedCell hqpos s)
      (adaptedCell_nonempty q s) hfinS
  have hshT :
      BlockMatLoewnerLE
        (blockSharp
          (annealedBlock P
            (adaptedCell q t)))
        (annealedBlock P
          (adaptedCell q t)) :=
    Sharp.blockSharp_annealedBlock_le_of_nonempty
      (isOpenBoundedConvexDomain_adaptedCell hqpos t)
      (adaptedCell_nonempty q t) hfinT
  -- the determinant ratio at the response tolerance
  have hdetpos :
      (0 : ℝ) <
        (toFullBlockMat
          (adaptedMean P q t)).det :=
    (posDef_toFullBlockMat
      (HighContrast.isSymmetricBlockMat_annealedBlock P
        (adaptedCell q t)) hposT).det_pos
  have hrootpos :
      (0 : ℝ) < adaptedDetRoot P q t :=
    Real.rpow_pos_of_pos hdetpos _
  have hdetDet :
      adaptedDetRoot P q s <
        (1 + deltaDet) * adaptedDetRoot P q t := by
    have hle :
        (1 + deltaTerm) * adaptedDetRoot P q t ≤
          (1 + deltaDet) * adaptedDetRoot P q t :=
      mul_le_mul_of_nonneg_right (by linarith only [hcaps2]) hrootpos.le
    exact lt_of_lt_of_le hdetT hle
  -- the adapted response closes on the selected tuple
  have hYmean : 1 ≤ ∫ a, Y a ∂P := by
    have hmom := hYmul.lp_moment 1 le_rfl
    rw [ENNReal.ofReal_one] at hmom
    have hmem : MemLp Y 1 P :=
      ⟨hYmul.measurable.aestronglyMeasurable,
        lt_of_le_of_lt hmom ENNReal.ofReal_lt_top⟩
    have hint : Integrable Y P := (memLp_one_iff_integrable).mp hmem
    have hmono := integral_mono (integrable_const (1 : ℝ)) hint hYmul.one_le
    simpa using hmono
  have himb :
      blockImbalance
        (adaptedMean P q t) ≤ 1 + deltaAd :=
    hresp3 P E Ψ K S hP hstat hunit hdag _ _ hcw Y hYmul
      hYmean hYint hYlq
      E0 m0 q s t hsymE0 hposE0 hm0 hq hjs htdef hHt henc1 henc2
      (fun k hk1 hk2 => ⟨(hbl k hk1 hk2).1, (hbl k hk1 hk2).2.1⟩)
      (fun k hk1 hk2 => (hbl k hk1 hk2).2.2) hsrc Cport hCport hh3 hEtEs hshS
      hshT hdetDet hcal1 hcal2 deltaDet deltaTerm hdeltaDetLo le_rfl
      hdeltaTermPos hcaps2 hdetT hdrift
      ((2 : ℝ) ^ (-(initExpQ d g : ℤ)) * eta) etaIn
      etaOut epsSt hprofLo le_rfl hh2 hh4 hcaps1 hsrc.kappaRef_le hecc hbuf
  -- the transfer
  have hYU : ∫ a, Y a ∂P ≤ 2 := by
    have h2 : ENNReal.ofReal (∫ a, Y a ∂P) ≤ 2 := le_trans hYint hYlq
    rw [show (2 : ENNReal) = ENNReal.ofReal 2 by simp] at h2
    exact (ENNReal.ofReal_le_ofReal_iff (by norm_num)).mp h2
  obtain ⟨l, hl⟩ :
      ∃ l : ℤ,
        l = ⌈max 1 (max 0
          (Real.logb 3
            (transferSizeBar 2 CAE (max 1 Cd0) g K E
              m0 t / etaPlus)))⌉ := ⟨_, rfl⟩
  obtain ⟨ment, hment⟩ : ∃ ment : ℤ, ment = t + l := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ :
      ∃ r : ℤ,
        r = ⌈max 1 (max 0
          (Real.logb 3
            (transferSizeBar 2 CAE (max 1 Cd0) g K E
              m0 ment / etaMinus)))⌉ := ⟨_, rfl⟩
  obtain ⟨maux, hmaux⟩ : ∃ maux : ℤ, maux = ment + r := ⟨_, rfl⟩
  obtain ⟨_hper, hcostimp, hready⟩ :=
    htrans P E Ψ K S hP hstat hunit hdag _ _ hcw m0 q hm0pos hq t
      (max_le hjt h1t) (henc1 t hjt le_rfl) Y hYmul hYU himb l ment r maux hl
      hment hr hmaux
  have hcost := (hcostimp hecc).2
  have hl1 : (1 : ℝ) ≤ (l : ℝ) := by
    have h := Int.le_ceil (max 1 (max 0
      (Real.logb 3
        (transferSizeBar 2 CAE (max 1 Cd0) g K E m0 t
          / etaPlus))))
    rw [← hl] at h
    exact le_trans (le_max_left _ _) h
  have hr1 : (1 : ℝ) ≤ (r : ℝ) := by
    have h := Int.le_ceil (max 1 (max 0
      (Real.logb 3
        (transferSizeBar 2 CAE (max 1 Cd0) g K E m0
          ment / etaMinus))))
    rw [← hr] at h
    exact le_trans (le_max_left _ _) h
  have hmentR : (ment : ℝ) = (t : ℝ) + (l : ℝ) := by rw [hment]; push_cast; ring
  have hmentUp :
      (ment : ℝ) ≤
        (jdag : ℝ) +
          (Csel + Cgap) *
            Real.logb 3 (2 + aspectRatio E) := by
    rw [hmentR, add_mul]
    linarith only [htUp, hcost, hr1]
  have hment0 : (0 : ℤ) ≤ ment := by
    have h1 : (1 : ℤ) ≤ l := by exact_mod_cast hl1
    rw [hment]; linarith only [h1t, h1]
  have hmentburn :
      sourceBurn d
        ((initExpQ d g : ℕ) : ℝ) K ≤ ment := by
    have h1 : (1 : ℤ) ≤ l := by exact_mod_cast hl1
    have : jdag ≤ ment := by rw [hment]; linarith only [hjt, h1]
    exact le_trans hburnj this
  -- the scale account
  obtain ⟨mEnt, hmEntEq, hmEntCeil, hmEntPoly⟩ :=
    hacct E K hdag.one_lt_growthWitness hAR jdag ment hjdagdef hmentUp hment0
  refine ⟨mEnt, hmEntCeil, ?_, hmEntPoly⟩
  rw [hmEntEq]
  have h4 :=
    Entry.entry_contrast d hd g hg P E Ψ K S hstat hunit hdag ment
      hmentburn
  have h5 := hready cStar hhier
  linarith only [h4, h5]


end
