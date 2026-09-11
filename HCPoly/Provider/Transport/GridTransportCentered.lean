/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Transport.FiniteTargetGap
import HCPoly.Provider.Transport.FiniteTargetGapBudget
import HCPoly.Provider.Transport.FiniteTargetPositiveGap
import HCPoly.Provider.Transport.FiniteCellMajorantMaxSplit
import HCPoly.Provider.Transport.GridTransportCenteredConstants
import HCPoly.Provider.Transport.BelowStartTransportBound

/-!
# The centered half of random-source grid transport
-/

namespace Homogenization
namespace HighContrast
namespace Transport

open MeasureTheory

open scoped ENNReal Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

/-- The centered-history premise consumed by
`random_source_grid_transport_assembly_of_centered_bound`. -/
theorem exists_grid_transport_centered_bound
    (d : ℕ) (hd : 2 ≤ d) (g : ℝ) (hg : g ∈ Set.Ico (0 : ℝ) 1)
    (Q : ℕ) (hQ : 2 ≤ Q)
    (rhoMax : ℝ) (a : ℝ)
    (hadef : a = (Q : ℝ) * (rhoMax - g) - (d : ℝ))
    (halo : 0 < a) (hahi : a < 1 - g)
    (Khop : ℝ) (hKhop : 1 ≤ Khop) :
    Even Q →
    g < rhoMax →
    rhoMax < 1 →
    0 < ((d : ℝ) + 1) / 2 - g - a / (Q : ℝ) →
    ∃ Ccen CcenS : ℝ, 0 ≤ Ccen ∧ 0 ≤ CcenS ∧
      ∀ l0 : ℕ, 1 ≤ l0 →
      ∀ Cd : ℝ, 1 ≤ Cd →
      ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
        (S : CoeffSpace d → ℝ),
        IsProbabilityMeasure P →
        HCPoly.Frozen.IsStationaryLaw P →
        HCPoly.Frozen.IsUnitRangeLaw P →
        HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S →
        ∀ jStar M : ℤ, IsCoupledWindow d Q K jStar M →
        ∀ Y : CoeffSpace d → ℝ,
          IsWindowMultiplier P g E Ψ K Cd jStar M Y →
        ∀ mu mu' : Mat d, mu.PosDef → mu'.PosDef →
        gridRatio (roundedGrid jStar mu) (roundedGrid jStar mu') ≤ Khop →
        ∀ rchk u : ℤ, jStar ≤ rchk → rchk ≤ u →
        (∀ r : Mat d, r = roundedGrid jStar mu ∨ r = roundedGrid jStar mu' →
          ∀ j : ℤ, jStar ≤ j → j ≤ u + 2 * (l0 : ℤ) →
            adaptedCell r j ⊆ centeredCube d M) →
        ∀ etaX : ℝ, 0 ≤ etaX → etaX ≤ 1 / 4 →
        BlockMatLoewnerLE
          (blockScale (1 - etaX)
            (adaptedMean P (roundedGrid jStar mu) (u + 2 * (l0 : ℤ))))
          (adaptedMean P (roundedGrid jStar mu') (u + (l0 : ℤ))) →
        BlockMatLoewnerLE
          (adaptedMean P (roundedGrid jStar mu') (u + (l0 : ℤ)))
          (blockScale (1 + etaX)
            (adaptedMean P (roundedGrid jStar mu) (u + 2 * (l0 : ℤ)))) →
        centeredHistory P (Q : ℝ) rhoMax (roundedGrid jStar mu') jStar
            (u + (l0 : ℤ)) ≤
          ENNReal.ofReal (Ccen * (3 : ℝ) ^ (2 * a * (l0 : ℝ))) *
              portableProfile P (Q : ℝ) a rhoMax (roundedGrid jStar mu)
                jStar rchk (u + 2 * (l0 : ℤ)) +
            ENNReal.ofReal (Ccen * etaX) +
            ENNReal.ofReal
              (CcenS * (3 : ℝ) ^ (a * (l0 : ℝ)) *
                transportSrcRemainder Cd g (Q : ℝ) a E jStar mu mu'
                  (u + (l0 : ℤ))) := by
  classical
  intro hQeven hrhoLo hrhoHi hkernelG
  obtain ⟨CgapP, CgapE, CgapS, hCgapP, hCgapE, hCgapS, hgapBudget⟩ :=
    exists_finite_target_gap_ennreal_bound d hd g hg Q hQ rhoMax a hadef
      halo hahi Khop hKhop
  have hkernel : 0 < ((d : ℝ) + 1) / 2 - a / (Q : ℝ) := by
    linarith only [hg.1, hkernelG]
  obtain ⟨hKgap, hKsplit, hCinh, hCfresh, hCsource⟩ :=
    centered_component_constants_nonnegative d Q hrhoHi hkernel hKhop
  obtain ⟨hCcen, hCcenS, hCprof, hCbridge, hCsrc⟩ :=
    centered_final_constants_data d Q hKgap hKsplit hCinh hCfresh hCsource
      hCgapP hCgapE hCgapS
  refine ⟨centeredTransportProfileConst d Q rhoMax a Khop CgapP CgapE,
    centeredTransportSourceConst d Q Khop CgapS, hCcen, hCcenS, ?_⟩
  intro l0 hl0 Cd hCd P E Ψ K S hPprob hPstat hPunit hced jStar M hw Y hY
    mu mu' hmu hmu' hKgrid rchk u hjr hru hcont etaX heta0 heta4 hlo hhi
  letI : IsProbabilityMeasure P := hPprob
  haveI : NeZero d := ⟨by omega⟩
  -- The concrete finite target family and its simultaneous majorants.
  obtain ⟨Z, hs, Zfill, cfill, Gmajor, Kmajor, hZcard, htarget, hwt,
      hhistory, hmajor, hbudget⟩ :=
    exists_finite_target_majorants_gap_sum_le d hd g hg Q hQ rhoMax a hadef
      halo hahi Khop hKhop l0 hl0 Cd hCd P E Ψ K S hPprob hPstat hced
      jStar M hw Y hY mu mu' hmu hmu' hKgrid rchk u hjr hru hcont etaX
      heta0 heta4 hlo hhi
  let targets : Finset ((_ : ℤ) × (Fin d → ℤ)) :=
    (Finset.Icc jStar (u + (l0 : ℤ))).sigma Z
  let wt : ((_ : ℤ) × (Fin d → ℤ)) → ℝ := fun i =>
    (3 : ℝ) ^ (rhoMax * ((i.1 : ℝ) - ((u + (l0 : ℤ) : ℤ) : ℝ)))
  let F0 : BlockMat d :=
    adaptedMean P (roundedGrid jStar mu') (u + (l0 : ℤ))
  let Bgap : ℝ :=
    (2 * 2 ^ (Q : ℝ) * (1 + 2 * (d : ℝ)) ^ (Q : ℝ)) *
      ((1 + (6 * (d : ℝ) * Real.sqrt d * Khop) *
          ((3 : ℝ) ^ (-(1 - g - a)) /
            (1 - (3 : ℝ) ^ (-(1 - g - a))))) *
          (3 : ℝ) ^ (a * (l0 : ℝ)) *
          ∑ r ∈ Finset.Ico jStar (u + 2 * (l0 : ℤ)),
            (3 : ℝ) ^
                (-a * (((u + 2 * (l0 : ℤ) : ℤ) : ℝ) - 1 - (r : ℝ))) *
              frakH (Q : ℝ)
                (relMean P (roundedGrid jStar mu) r
                  (u + 2 * (l0 : ℤ))) +
        6 * (1 / (1 - (3 : ℝ) ^
          (-((Q : ℝ) * rhoMax - (d : ℝ))))) * etaX +
        ((3 : ℝ) ^ a *
          (1 / (1 - (3 : ℝ) ^ (-a)) +
            1 / (1 - (3 : ℝ) ^ (-(1 - g - a))) +
            1 / (1 - (3 : ℝ) ^
              (-((Q : ℝ) * (1 - g) - a))))) *
          (18 * (d : ℝ) * Real.sqrt d * Khop) ^ (Q : ℝ) *
          transportSrcRemainder Cd g (Q : ℝ) a E jStar mu mu'
            (u + (l0 : ℤ)))
  change 0 ≤ Bgap ∧
    ∑ i ∈ targets, wt i ^ (Q : ℝ) *
      gapG (Q : ℝ) (normalizedBlock (Kmajor i) F0) ≤ Bgap at hbudget
  obtain ⟨hBgap0, hgapSum⟩ := hbudget
  have hd1 : 1 ≤ d := by omega
  have hg0 : 0 ≤ g := hg.1
  have hg1 : g < 1 := hg.2
  have hQreal0 : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast (by omega : 0 < Q)
  have hQreal1 : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast (by omega : 1 ≤ Q)
  have hjn : jStar ≤ u + (l0 : ℤ) := by omega
  have hjt : jStar ≤ u + 2 * (l0 : ℤ) := by omega
  have hnt : u + (l0 : ℤ) ≤ u + 2 * (l0 : ℤ) := by omega
  have hq := isRoundedGrid_roundedGrid_of_isCoupledWindow hw hmu
  have hq' := isRoundedGrid_roundedGrid_of_isCoupledWindow hw hmu'
  have hqPD : (roundedGrid jStar mu).PosDef := Recurrence.posDef_of_isRoundedGrid hq
  obtain ⟨hdef, hmono, _⟩ :=
    transport_definedness_and_bridge d hd g Q hQ l0 Cd P E Ψ K S hPprob
      hPstat hced jStar M hw Y hY mu mu' hmu hmu' rchk u hjr hru hcont
  have hFpd : Book.Ch02.BlockPosDef F0 := by
    exact (hdef _ (Or.inr rfl) _ hjn hnt).2.1
  have hTpd : Book.Ch02.BlockPosDef
      (adaptedMean P (roundedGrid jStar mu) (u + 2 * (l0 : ℤ))) :=
    (hdef _ (Or.inl rfl) _ hjt le_rfl).2.1
  have hbpd : Book.Ch02.BlockPosDef
      (adaptedMean P (roundedGrid jStar mu) rchk) :=
    (hdef _ (Or.inl rfl) _ hjr (by omega)).2.1
  have hlev : ∀ i ∈ targets, jStar ≤ i.1 := by
    intro i hi
    exact (Finset.mem_Icc.mp (Finset.mem_sigma.mp hi).1).1
  have hfinTarget : ∀ i ∈ targets,
      HasFiniteAdaptedMean P (roundedGrid jStar mu') i.1 := by
    intro i hi
    have hij := Finset.mem_Icc.mp (Finset.mem_sigma.mp hi).1
    exact (hdef _ (Or.inr rfl) _ hij.1 (hij.2.trans hnt)).1
  have hFillEq := fun i hi => (hmajor i hi).1
  have hFillSub := fun i hi => (hmajor i hi).2.1
  have hcfill := fun i hi => (hmajor i hi).2.2.1
  have hratio := fun i hi => (hmajor i hi).2.2.2.1
  have hmass := fun i hi => (hmajor i hi).2.2.2.2.1
  have hrow := fun i hi => (hmajor i hi).2.2.2.2.2.1
  have hdom := fun i hi => (hmajor i hi).2.2.2.2.2.2.1
  have hGsym := fun i hi => (hmajor i hi).2.2.2.2.2.2.2.1
  have hGmeas := fun i hi => (hmajor i hi).2.2.2.2.2.2.2.2.1
  have hGint := fun i hi => (hmajor i hi).2.2.2.2.2.2.2.2.2.1
  have hGmean := fun i hi => (hmajor i hi).2.2.2.2.2.2.2.2.2.2.1
  have hKsym := fun i hi => (hmajor i hi).2.2.2.2.2.2.2.2.2.2.2.1
  have hcentered := fun i hi =>
    (hmajor i hi).2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hIH := fun i hi =>
    (hmajor i hi).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hHK := fun i hi =>
    (hmajor i hi).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  change targets.Nonempty at hs
  change ∀ i ∈ targets, 0 < wt i at hwt
  have hmain := finite_target_family_positive_gap hPstat hQ hQeven hq'
    targets hs (fun i => i.1) (fun i => i.2) hlev hfinTarget wt hwt
    Gmajor Kmajor hFpd hGsym hKsym hdom hGint hGmean hGmeas hIH hHK
    hBgap0 hgapSum
  have hmain' :
      ∫⁻ x, ENNReal.ofReal (targets.sup' hs fun i => wt i *
          schattenSize (Q : ℝ)
            (blockSub
              (adaptedResponse (roundedGrid jStar mu') i.1 i.2 x)
              (adaptedMean P (roundedGrid jStar mu') i.1)) F0) ^
            (Q : ℝ) ∂P ≤
        ENNReal.ofReal (centeredCollectiveGapConst d Q) *
          ((∫⁻ x, ENNReal.ofReal (targets.sup' hs fun i => wt i *
              schattenSize (Q : ℝ) (blockSub (Gmajor i x) (Kmajor i)) F0) ^
                (Q : ℝ) ∂P) + ENNReal.ofReal (2 * Bgap)) := by
    simpa only [targets, wt, F0, centeredCollectiveGapConst] using hmain
  let src : ((_ : ℤ) × (Fin d → ℤ)) → CoeffSpace d → ℝ := fun i x =>
    6 * (d : ℝ) * Real.sqrt d * Khop * boundaryConst Cd g mu * zetaG g *
      (3 : ℝ) ^ (jStar - i.1) * (Y x - ∫ y, Y y ∂P)
  have hsplitRaw := finite_cell_majorant_three_max_moment_le hQ hQeven
    targets hs wt (fun i hi => (hwt i hi).le) hqPD hjr (fun i => i.1)
    Zfill cfill Gmajor Kmajor E F0 src hced.refBlock_isSymm hGsym hKsym
    (by
      intro i hi
      simpa only [src, mul_assoc] using hcentered i hi)
  have hsplit :
      (∫⁻ x, ENNReal.ofReal (targets.sup' hs fun i => wt i *
          schattenSize (Q : ℝ) (blockSub (Gmajor i x) (Kmajor i)) F0) ^
            (Q : ℝ) ∂P) ≤
        ENNReal.ofReal (centeredMajorantSplitConst d Q) *
          ((∫⁻ x, ENNReal.ofReal (targets.sup' hs fun i => wt i *
              schattenSize (Q : ℝ)
                (ofFullBlockMat
                  (∑ r ∈ Finset.Icc jStar (min rchk i.1), ∑ w ∈ Zfill i r,
                    cfill i r • toFullBlockMat
                      (blockSub
                        (coarseBlock (adaptedCellAt
                          (roundedGrid jStar mu) r w) x)
                        (adaptedMean P (roundedGrid jStar mu) r)))) F0) ^
                (Q : ℝ) ∂P) +
            (∫⁻ x, ENNReal.ofReal (targets.sup' hs fun i => wt i *
              schattenSize (Q : ℝ)
                (ofFullBlockMat
                  (∑ r ∈ Finset.Icc (rchk + 1) i.1, ∑ w ∈ Zfill i r,
                    cfill i r • toFullBlockMat
                      (blockSub
                        (coarseBlock (adaptedCellAt
                          (roundedGrid jStar mu) r w) x)
                        (adaptedMean P (roundedGrid jStar mu) r)))) F0) ^
                (Q : ℝ) ∂P) +
            ∫⁻ x, ENNReal.ofReal (targets.sup' hs fun i => wt i *
              schattenSize (Q : ℝ) (blockScale (src i x) E) F0) ^
                (Q : ℝ) ∂P) := by
    rw [centeredMajorantSplitConst]
    rw [← finite_max_split_coefficient_eq_ofReal d hQreal1]
    exact hsplitRaw
  let buf : ℝ := (3 : ℝ) ^ (a * (l0 : ℝ))
  let buf2 : ℝ := (3 : ℝ) ^ (2 * a * (l0 : ℝ))
  let Rsrc : ℝ :=
    transportSrcRemainder Cd g (Q : ℝ) a E jStar mu mu'
      (u + (l0 : ℤ))
  let profile : ℝ≥0∞ :=
    portableProfile P (Q : ℝ) a rhoMax (roundedGrid jStar mu) jStar rchk
      (u + 2 * (l0 : ℤ))
  have htReal : ((u + 2 * (l0 : ℤ) : ℤ) : ℝ) =
      ((u + (l0 : ℤ) : ℤ) : ℝ) + (l0 : ℝ) := by
    push_cast
    ring
  have hfinOld : ∀ r : ℤ, jStar ≤ r → r ≤ u + 2 * (l0 : ℤ) →
      HasFiniteAdaptedMean P (roundedGrid jStar mu) r := by
    intro r hr hrt
    exact (hdef _ (Or.inl rfl) r hr hrt).1
  have hPm : (1 : FullBlockMat d) ≤ toFullBlockMat
      (relMean P (roundedGrid jStar mu) rchk (u + 2 * (l0 : ℤ))) :=
    PortableHistory.one_le_relMean_window hPstat hq le_rfl hfinOld hjr (by omega) le_rfl
  have htargetTrans : ∀ i ∈ targets,
      adaptedCellAt (roundedGrid jStar mu') i.1 i.2 ⊆
        adaptedCellTranslate (roundedGrid jStar mu') (u + (l0 : ℤ))
          (0 : Vec d) := by
    intro i hi
    have hzero : adaptedCellTranslate (roundedGrid jStar mu')
        (u + (l0 : ℤ)) (0 : Vec d) =
          adaptedCell (roundedGrid jStar mu') (u + (l0 : ℤ)) := by
      simp [adaptedCellTranslate]
    rw [hzero]
    exact htarget i hi
  have hinheritedRaw := inherited_majorant_max_le_portableProfile
    (P := P) (l := jStar) (p := roundedGrid jStar mu')
    (q := roundedGrid jStar mu) (jStar := jStar) (b := rchk)
    (n := u + (l0 : ℤ)) (t := u + 2 * (l0 : ℤ))
    (Q := (Q : ℝ)) (g := g) (rhoMax := rhoMax) (a := a)
    (l0 := (l0 : ℝ)) (Khop := Khop) (etaX := etaX)
    (C := 6 * (d : ℝ) * Real.sqrt d * Khop) (y := (0 : Vec d))
    hd1 hQreal0 hg0 hrhoHi hadef hPstat hq hjr (by omega) htReal hKgrid
    hKhop hbpd hTpd hFpd hPm heta4 hlo (ZT := Z) hs (ZF := Zfill)
    (cF := cfill) hcfill hmass hrow hFillSub htargetTrans
  have hinherited :
      (∫⁻ x, ENNReal.ofReal (targets.sup' hs fun i => wt i *
          schattenSize (Q : ℝ)
            (ofFullBlockMat
              (∑ r ∈ Finset.Icc jStar (min rchk i.1), ∑ w ∈ Zfill i r,
                cfill i r • toFullBlockMat
                  (blockSub
                    (coarseBlock (adaptedCellAt
                      (roundedGrid jStar mu) r w) x)
                    (adaptedMean P (roundedGrid jStar mu) r)))) F0) ^
            (Q : ℝ) ∂P) ≤
        ENNReal.ofReal (centeredInheritedConst d Q rhoMax Khop * buf) *
          profile := by
    simpa only [targets, wt, F0, buf, profile, centeredInheritedConst,
      mul_assoc] using hinheritedRaw
  have hfinFresh : ∀ r ∈ Finset.Icc (rchk + 1)
      (u + 2 * (l0 : ℤ)),
      HasFiniteAdaptedMean P (roundedGrid jStar mu) r := by
    intro r hr
    have hrange := Finset.mem_Icc.mp hr
    exact hfinOld r (by omega) hrange.2
  have hpdFresh : ∀ r ∈ Finset.Icc (rchk + 1)
      (u + 2 * (l0 : ℤ)),
      Book.Ch02.BlockPosDef (adaptedMean P (roundedGrid jStar mu) r) := by
    intro r hr
    have hrange := Finset.mem_Icc.mp hr
    exact (hdef _ (Or.inl rfl) r (by omega) hrange.2).2.1
  have hmeanFresh : ∀ r ∈ Finset.Icc (rchk + 1)
      (u + 2 * (l0 : ℤ)),
      BlockMatLoewnerLE
        (adaptedMean P (roundedGrid jStar mu) (u + 2 * (l0 : ℤ)))
        (adaptedMean P (roundedGrid jStar mu) r) := by
    intro r hr
    have hrange := Finset.mem_Icc.mp hr
    exact hmono _ (Or.inl rfl) r (u + 2 * (l0 : ℤ)) (by omega)
      hrange.2 le_rfl
  have hmomentFresh : ∀ r ∈ Finset.Icc (rchk + 1)
      (u + 2 * (l0 : ℤ)),
      centeredMoment P (Q : ℝ) (roundedGrid jStar mu) r ≠ ⊤ := by
    intro r hr
    have hrange := Finset.mem_Icc.mp hr
    exact (hdef _ (Or.inl rfl) r (by omega) hrange.2).2.2
  have hfreshRaw := fresh_majorant_max_moment_le_portableProfile
    (P := P) hPstat hPunit (Q := Q) hQ hQeven (g := g)
    (rhoMax := rhoMax) (a := a) hg0 hadef hkernel
    (jStar := jStar) (b := rchk) (n := u + (l0 : ℤ))
    (t := u + 2 * (l0 : ℤ)) (l0 := l0) (by omega)
    (q := roundedGrid jStar mu) (q' := roundedGrid jStar mu') hd1 hq hq' hjr
    (Khop := Khop) (etaX := etaX) hKgrid heta4 hTpd hFpd hlo
    (Ztarget := Z) hs (fun j hj => (hZcard j hj).2)
    (Zfill := Zfill) (c := cfill)
    (fun i hi r _ => hFillEq i hi r)
    (fun i hi r _ => hcfill i hi r)
    (fun i hi r _ => hratio i hi r)
    hfinFresh hpdFresh hmeanFresh hmomentFresh
  have hfresh :
      (∫⁻ x, ENNReal.ofReal (targets.sup' hs fun i => wt i *
          schattenSize (Q : ℝ)
            (ofFullBlockMat
              (∑ r ∈ Finset.Icc (rchk + 1) i.1, ∑ w ∈ Zfill i r,
                cfill i r • toFullBlockMat
                  (blockSub
                    (coarseBlock (adaptedCellAt
                      (roundedGrid jStar mu) r w) x)
                    (adaptedMean P (roundedGrid jStar mu) r)))) F0) ^
            (Q : ℝ) ∂P) ≤
        ENNReal.ofReal (centeredFreshConst d Q a Khop * buf) * profile := by
    simpa only [targets, wt, F0, buf, profile, centeredFreshConst,
      mul_assoc] using hfreshRaw
  have haQrho : a ≤ (Q : ℝ) * rhoMax := by
    have hQg0 : 0 ≤ (Q : ℝ) * g :=
      mul_nonneg (Nat.cast_nonneg Q) hg0
    have hdR0 : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
    rw [hadef]
    nlinarith only [hQg0, hdR0]
  have hcontn : adaptedCell (roundedGrid jStar mu') (u + (l0 : ℤ)) ⊆
      centeredCube d M :=
    hcont _ (Or.inr rfl) _ hjn hnt
  have hsourceRaw := below_start_target_max_le_transport
    (P := P) hd1 (g := g) hg0 hg1 (Q := Q) hQ
    (rhoMax := rhoMax) (a := a) (Khop := Khop) hrhoHi hKhop haQrho
    (E := E) (Ψ := Ψ) (K := K) (Cd := Cd) hCd
    hced.refBlock_isSymm hced.refBlock_posDef (jStar := jStar) (M := M) hw
    (Y := Y) hY (mu := mu) (mu' := mu') hmu' hKgrid
    (n := u + (l0 : ℤ)) hjn hcontn hFpd targets hs (fun i => i.1) hlev
  have hsource :
      (∫⁻ x, ENNReal.ofReal (targets.sup' hs fun i => wt i *
          schattenSize (Q : ℝ) (blockScale (src i x) E) F0) ^
            (Q : ℝ) ∂P) ≤
        ENNReal.ofReal (centeredBelowStartConst d Q Khop * Rsrc) := by
    simpa only [targets, wt, F0, src, Rsrc, mul_assoc] using hsourceRaw
  have hCd0 : 0 ≤ Cd := le_trans zero_le_one hCd
  have hSrcCoeff0 : 0 ≤ transportSrcCoeff Cd g E jStar mu mu' :=
    le_trans zero_le_one
      (one_le_transportSrcCoeff hCd0 hg1 E jStar mu mu')
  have hR0 : 0 ≤ Rsrc := by
    simp only [Rsrc, transportSrcRemainder]
    exact mul_nonneg
      (add_nonneg hSrcCoeff0
        (Real.rpow_nonneg hSrcCoeff0 (Q : ℝ)))
      (Real.rpow_nonneg (by norm_num) _)
  have hbuf0 : 0 ≤ buf := by
    simp only [buf]
    positivity
  have hbuf1 : 1 ≤ buf := by
    simp only [buf]
    exact Real.one_le_rpow (by norm_num)
      (mul_nonneg halo.le (Nat.cast_nonneg l0))
  have hbuf2 : buf ≤ buf2 := by
    simp only [buf, buf2]
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have hl0R : 0 ≤ (l0 : ℝ) := Nat.cast_nonneg l0
    nlinarith only [halo.le, hl0R]
  have hgapRaw := hgapBudget l0 hl0 Cd hCd P E Ψ K S hPprob hPstat hced
    jStar M hw Y hY mu mu' hmu hmu' rchk u hjr hru hcont etaX heta0
  have hgap : ENNReal.ofReal Bgap ≤
      ENNReal.ofReal (CgapP * buf) * profile +
        ENNReal.ofReal (CgapE * etaX) +
        ENNReal.ofReal (CgapS * Rsrc) := by
    simpa only [Bgap, buf, profile, Rsrc] using hgapRaw
  have hfinal := centered_collective_conclusion
    (B := Bgap) (etaX := etaX) (Rsrc := Rsrc) (buf := buf) (buf2 := buf2)
    (Kgap := centeredCollectiveGapConst d Q)
    (Ksplit := centeredMajorantSplitConst d Q)
    (Cinh := centeredInheritedConst d Q rhoMax Khop)
    (Cfresh := centeredFreshConst d Q a Khop)
    (Csource := centeredBelowStartConst d Q Khop)
    (CgapP := CgapP) (CgapE := CgapE) (CgapS := CgapS)
    (Ccen := centeredTransportProfileConst d Q rhoMax a Khop CgapP CgapE)
    (CcenS := centeredTransportSourceConst d Q Khop CgapS)
    heta0 hR0 hbuf0 hbuf1 hbuf2 hKgap hKsplit hCinh hCfresh hCsource
    hCgapP hCgapE hCgapS hCcen hCcenS hCprof hCbridge hCsrc
    hmain' hsplit hinherited hfresh hsource hgap
  refine hhistory.trans ?_
  simpa only [targets, wt, F0, buf, buf2, Rsrc, profile] using hfinal

end

end Transport
end HighContrast
end Homogenization
