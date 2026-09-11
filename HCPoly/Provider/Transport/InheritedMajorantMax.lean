/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Transport.InheritedCellSup
import HCPoly.Provider.Transport.SupInherited
import HCPoly.Provider.Transport.CenteredUpper
import HCPoly.Provider.PortableHistory.MajorizationAssembly

/-!
# The inherited part of a finite target-family maximum

All inherited pieces of the target-cell majorants use one finite family of
checkpoint ancestors.  Their weighted pathwise maximum is therefore paid once,
through the old centered history.  The lower bridge supplies the normalization
comparison and the relative mean supplies its scale factor.
-/

namespace Homogenization
namespace HighContrast
namespace Transport

open MeasureTheory

open scoped ENNReal Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- The inherited pieces of a finite sigma family of target majorants have one
weighted-max moment, controlled by the old portable profile. -/
theorem inherited_majorant_max_le_portableProfile [NeZero d]
    {P : Measure (CoeffSpace d)} {l : ℤ} {p q : Mat d}
    {jStar b n t : ℤ} {Q g rhoMax a l0 Khop etaX C : ℝ}
    {y : Vec d}
    (hd : 1 ≤ d) (hQ : 0 < Q) (hg : 0 ≤ g) (hrho : rhoMax < 1)
    (hadef : a = Q * (rhoMax - g) - (d : ℝ))
    (hP : HCPoly.Frozen.IsStationaryLaw P)
    (hq : IsRoundedGrid l q) (hlb : l ≤ b) (hbn : b ≤ n)
    (ht : (t : ℝ) = (n : ℝ) + l0)
    (hK : gridRatio q p ≤ Khop) (hKhop : 1 ≤ Khop)
    (hbpd : Book.Ch02.BlockPosDef (adaptedMean P q b))
    (htpd : Book.Ch02.BlockPosDef (adaptedMean P q t))
    (hnpd : Book.Ch02.BlockPosDef (adaptedMean P p n))
    (hPm : (1 : FullBlockMat d) ≤ toFullBlockMat (relMean P q b t))
    (heta4 : etaX ≤ 1 / 4)
    (hlo : BlockMatLoewnerLE
      (blockScale (1 - etaX) (adaptedMean P q t))
      (adaptedMean P p n))
    {ZT : ℤ → Finset (Fin d → ℤ)}
    (hs : ((Finset.Icc jStar n).sigma ZT :
      Finset ((_ : ℤ) × (Fin d → ℤ))).Nonempty)
    {ZF : ((_ : ℤ) × (Fin d → ℤ)) → ℤ → Finset (Fin d → ℤ)}
    {cF : ((_ : ℤ) × (Fin d → ℤ)) → ℤ → ℝ}
    (hc : ∀ i ∈ ((Finset.Icc jStar n).sigma ZT :
        Finset ((_ : ℤ) × (Fin d → ℤ))), ∀ r, 0 ≤ cF i r)
    (hmass : ∀ i ∈ ((Finset.Icc jStar n).sigma ZT :
        Finset ((_ : ℤ) × (Fin d → ℤ))),
      ∑ r ∈ Finset.Icc jStar i.1, ∑ _w ∈ ZF i r, cF i r ≤ 1)
    (hrow : ∀ i ∈ ((Finset.Icc jStar n).sigma ZT :
        Finset ((_ : ℤ) × (Fin d → ℤ))), ∀ r ∈ Finset.Icc jStar i.1,
      r < i.1 →
        (∑ _w ∈ ZF i r, cF i r) ≤
          C * (3 : ℝ) ^ ((r : ℝ) - (i.1 : ℝ)))
    (hZsub : ∀ i ∈ ((Finset.Icc jStar n).sigma ZT :
        Finset ((_ : ℤ) × (Fin d → ℤ))), ∀ r, ∀ w ∈ ZF i r,
      adaptedCellAt q r w ⊆ adaptedCellAt p i.1 i.2)
    (htarget : ∀ i ∈ ((Finset.Icc jStar n).sigma ZT :
        Finset ((_ : ℤ) × (Fin d → ℤ))),
      adaptedCellAt p i.1 i.2 ⊆ adaptedCellTranslate p n y) :
    ∫⁻ x, ENNReal.ofReal
        (((Finset.Icc jStar n).sigma ZT).sup' hs fun i =>
          (3 : ℝ) ^ (rhoMax * ((i.1 : ℝ) - (n : ℝ))) *
            schattenSize Q
              (ofFullBlockMat
                (∑ r ∈ Finset.Icc jStar (min b i.1), ∑ w ∈ ZF i r,
                  cF i r • toFullBlockMat
                    (blockSub (coarseBlock (adaptedCellAt q r w) x)
                      (adaptedMean P q r))))
              (adaptedMean P p n)) ^ Q ∂P ≤
      ENNReal.ofReal (
          ((((2 * (d : ℝ)) ^ Q⁻¹ * (4 / 3 : ℝ) *
                (max 1 C * (1 / (1 - (3 : ℝ) ^ (-(1 - rhoMax)))))) ^ Q *
              (2 + Real.sqrt d * Khop) ^ d) *
            (3 : ℝ) ^ (a * l0))) *
        portableProfile P Q a rhoMax q jStar b t := by
  classical
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hqPD : q.PosDef := Recurrence.posDef_of_isRoundedGrid hq
  have hbsym : IsSymmetricBlockMat (adaptedMean P q b) :=
    Recurrence.isSymmetricBlockMat_adaptedMean P q b
  have htsym : IsSymmetricBlockMat (adaptedMean P q t) :=
    Recurrence.isSymmetricBlockMat_adaptedMean P q t
  have hnsym : IsSymmetricBlockMat (adaptedMean P p n) :=
    Recurrence.isSymmetricBlockMat_adaptedMean P p n
  have htfull : (toFullBlockMat (adaptedMean P q t)).PosDef :=
    posDef_toFullBlockMat htsym htpd
  have hnfull : (toFullBlockMat (adaptedMean P p n)).PosDef :=
    posDef_toFullBlockMat hnsym hnpd
  have heta1 : etaX < 1 := by linarith only [heta4]
  have hden : 0 < 1 - etaX := sub_pos.mpr heta1
  have hinv0 : 0 ≤ (1 - etaX)⁻¹ := inv_nonneg.mpr hden.le
  have hinv43 : (1 - etaX)⁻¹ ≤ (4 / 3 : ℝ) := by
    rw [inv_eq_one_div, div_le_iff₀ hden]
    linarith only [heta4]
  have hEtF : toFullBlockMat (adaptedMean P q t) ≤
      (1 - etaX)⁻¹ • toFullBlockMat (adaptedMean P p n) := by
    have hflat := le_of_blockMatLoewnerLE
      (isSymmetricBlockMat_blockScale (1 - etaX) htsym) hnsym hlo
    rw [toFullBlockMat_blockScale] at hflat
    have hscaled := smul_le_smul_of_le (c := (1 - etaX)⁻¹) hinv0 hflat
    rwa [smul_smul, inv_mul_cancel₀ (ne_of_gt hden), one_smul] at hscaled
  have hPmps : (toFullBlockMat (relMean P q b t)).PosSemidef :=
    (posDef_of_one_le hPm).posSemidef
  have hEbEt : toFullBlockMat (adaptedMean P q b) ≤
      ‖toFullBlockMat (relMean P q b t)‖ •
        toFullBlockMat (adaptedMean P q t) := by
    apply (conj_normalize htfull _).mpr
    rw [← Recurrence.toFullBlockMat_relMean]
    exact le_norm_smul_one hPmps
  have hEbF : toFullBlockMat (adaptedMean P q b) ≤
      ((1 - etaX)⁻¹ * ‖toFullBlockMat (relMean P q b t)‖) •
        toFullBlockMat (adaptedMean P p n) := by
    calc
      toFullBlockMat (adaptedMean P q b) ≤
          ‖toFullBlockMat (relMean P q b t)‖ •
            toFullBlockMat (adaptedMean P q t) := hEbEt
      _ ≤ ‖toFullBlockMat (relMean P q b t)‖ •
            ((1 - etaX)⁻¹ • toFullBlockMat (adaptedMean P p n)) :=
          smul_le_smul_of_le (norm_nonneg _) hEtF
      _ = ((1 - etaX)⁻¹ * ‖toFullBlockMat (relMean P q b t)‖) •
            toFullBlockMat (adaptedMean P p n) := by
          rw [smul_smul]
          congr 1
          ring
  have hlam0 : 0 ≤ (1 - etaX)⁻¹ *
      ‖toFullBlockMat (relMean P q b t)‖ :=
    mul_nonneg hinv0 (norm_nonneg _)
  let anc : ℤ → (Fin d → ℤ) → (Fin d → ℤ) := fun r w =>
    gridParent^[(b - r).toNat] w
  have hancsub : ∀ r : ℤ, r ≤ b → ∀ w : Fin d → ℤ,
      adaptedCellAt q r w ⊆ adaptedCellAt q b (anc r w) := by
    intro r hr w
    have hsub := adaptedCellAt_subset_ancestor q r w (b - r).toNat
    have hscale : r + ((b - r).toNat : ℤ) = b := by omega
    rwa [hscale] at hsub
  have hAncFin := finite_ancestors (p := p) hd hqPD hbn (y := y)
  let Zanc : Finset (Fin d → ℤ) := hAncFin.toFinset
  have hZanc : ∀ w ∈ Zanc,
      (adaptedCellAt q b w ∩ adaptedCellTranslate p n y).Nonempty := by
    intro w hw
    exact hAncFin.mem_toFinset.mp hw
  let u : ℤ → (Fin d → ℤ) → CoeffSpace d → ℝ := fun j z x =>
    schattenSize Q
      (ofFullBlockMat
        (∑ r ∈ Finset.Icc jStar (min b j), ∑ w ∈ ZF ⟨j, z⟩ r,
          cF ⟨j, z⟩ r • toFullBlockMat
            (blockSub (coarseBlock (adaptedCellAt q r w) x)
              (adaptedMean P q r))))
      (adaptedMean P p n)
  let CW : ℝ := max 1 C * (1 / (1 - (3 : ℝ) ^ (-(1 - rhoMax))))
  have hCW0 : 0 ≤ CW := by
    have hratio := PortableHistory.geom_ratio_lt_one (by linarith only [hrho] : 0 < 1 - rhoMax)
    have hfrac : 0 ≤ 1 / (1 - (3 : ℝ) ^ (-(1 - rhoMax))) :=
      (one_div_pos.mpr (sub_pos.mpr hratio)).le
    exact mul_nonneg (le_trans zero_le_one (le_max_left 1 C)) hfrac
  have hcell : ∀ x : CoeffSpace d, ∀ j, jStar ≤ j → j ≤ n →
      ∀ z, z ∈ ZT j →
        ENNReal.ofReal (u j z x) ≤
          ENNReal.ofReal
            (((2 * (d : ℝ)) ^ Q⁻¹ *
                ((1 - etaX)⁻¹ * ‖toFullBlockMat (relMean P q b t)‖)) *
              CW * (3 : ℝ) ^ (rhoMax * ((b : ℝ) - (j : ℝ)))) *
            ⨆ vB ∈ Zanc, ⨆ (r : ℤ) (_ : jStar ≤ r) (_ : r ≤ b)
                (w : Fin d → ℤ) (_ : adaptedCellAt q r w ⊆ adaptedCellAt q b vB),
              ENNReal.ofReal
                ((3 : ℝ) ^ (-rhoMax * ((b : ℝ) - (r : ℝ))) *
                  blockSize (blockSub
                    (adaptedResponse q r w x) (adaptedMean P q r))
                    (adaptedMean P q b)) := by
    intro x j hjj hjn z hz
    have hi : (⟨j, z⟩ : ((_ : ℤ) × (Fin d → ℤ))) ∈
        ((Finset.Icc jStar n).sigma ZT :
          Finset ((_ : ℤ) × (Fin d → ℤ))) :=
      Finset.mem_sigma.mpr ⟨Finset.mem_Icc.mpr ⟨hjj, hjn⟩, hz⟩
    have hancmem : ∀ r ∈ Finset.Icc jStar (min b j),
        ∀ w ∈ ZF ⟨j, z⟩ r, anc r w ∈ Zanc := by
      intro r hr w hw
      have hrb : r ≤ b := (Finset.mem_Icc.mp hr).2.trans (min_le_left b j)
      have hsource : adaptedCellAt q r w ⊆ adaptedCellTranslate p n y :=
        (hZsub ⟨j, z⟩ hi r w hw).trans (htarget ⟨j, z⟩ hi)
      have hmeet := ancestor_meets_of_subset (hancsub r hrb w) hsource
      exact hAncFin.mem_toFinset.mpr hmeet
    have h := inherited_cell_schatten_le (Q := Q) (rhoMax := rhoMax)
      (lam := (1 - etaX)⁻¹ * ‖toFullBlockMat (relMean P q b t)‖)
      (C := C) hQ (P := P) (q := q) (jStar := jStar) (b := b) (j := j)
      hjj hrho hnsym hnpd hbpd hlam0 hEbF
      (Z := ZF ⟨j, z⟩) (c := cF ⟨j, z⟩) (hc ⟨j, z⟩ hi)
      (hmass ⟨j, z⟩ hi) (hrow ⟨j, z⟩ hi)
      (Zanc := Zanc) (anc := anc) hancmem
      (fun r hr w _ => hancsub r
        ((Finset.mem_Icc.mp hr).2.trans (min_le_left b j)) w) x
    simpa only [u, CW, mul_assoc] using h
  have hsup := sup_inherited_le (P := P) (l := l) (p := p) (q := q)
    (jStar := jStar) (b := b) (n := n) (Q := Q) (rhoMax := rhoMax)
    (lam := (2 * (d : ℝ)) ^ Q⁻¹ *
      ((1 - etaX)⁻¹ * ‖toFullBlockMat (relMean P q b t)‖))
    (CW := CW) (Khop := Khop) (y := y) (Zanc := Zanc)
    (mem := fun j z => z ∈ ZT j) (u := u) hd hQ hP hq hlb hbn hK hbpd
    hZanc (mul_nonneg (Real.rpow_nonneg (by positivity) _) hlam0) hCW0 hcell
  have hfinite : ∀ x : CoeffSpace d,
      ENNReal.ofReal
          (((Finset.Icc jStar n).sigma ZT).sup' hs fun i =>
            (3 : ℝ) ^ (rhoMax * ((i.1 : ℝ) - (n : ℝ))) * u i.1 i.2 x) ≤
        ⨆ (j : ℤ) (_ : jStar ≤ j) (_ : j ≤ n) (z : Fin d → ℤ)
            (_ : z ∈ ZT j),
          ENNReal.ofReal
            ((3 : ℝ) ^ (-rhoMax * ((n : ℝ) - (j : ℝ))) * u j z x) := by
    intro x
    obtain ⟨i, hi, hmax⟩ := ((Finset.Icc jStar n).sigma ZT).exists_mem_eq_sup'
      hs (fun i => (3 : ℝ) ^ (rhoMax * ((i.1 : ℝ) - (n : ℝ))) * u i.1 i.2 x)
    rw [hmax]
    obtain ⟨hilevel, hiindex⟩ := Finset.mem_sigma.mp hi
    obtain ⟨hilo, hihi⟩ := Finset.mem_Icc.mp hilevel
    have hweight : rhoMax * ((i.1 : ℝ) - (n : ℝ)) =
        -rhoMax * ((n : ℝ) - (i.1 : ℝ)) := by ring
    rw [hweight]
    exact le_iSup_of_le i.1 (le_iSup_of_le hilo (le_iSup_of_le hihi
      (le_iSup_of_le i.2 (le_iSup_of_le hiindex le_rfl))))
  have hmaxBound :
      ∫⁻ x, ENNReal.ofReal
          (((Finset.Icc jStar n).sigma ZT).sup' hs fun i =>
            (3 : ℝ) ^ (rhoMax * ((i.1 : ℝ) - (n : ℝ))) * u i.1 i.2 x) ^ Q ∂P ≤
        ENNReal.ofReal
            ((((2 * (d : ℝ)) ^ Q⁻¹ *
                ((1 - etaX)⁻¹ * ‖toFullBlockMat (relMean P q b t)‖)) *
              CW * (3 : ℝ) ^ (-rhoMax * ((n : ℝ) - (b : ℝ)))) ^ Q) *
          (ENNReal.ofReal
              ((2 + Real.sqrt d * Khop) ^ d *
                (3 : ℝ) ^ ((n - b) * (d : ℤ))) *
            centeredHistory P Q rhoMax q jStar b) := by
    exact (lintegral_mono fun x => ENNReal.rpow_le_rpow (hfinite x) hQ.le).trans hsup
  have hK0 : 0 ≤ (2 * (d : ℝ)) ^ Q⁻¹ :=
    Real.rpow_nonneg (by positivity) _
  have hKhop0 : 0 ≤ Khop := le_trans zero_le_one hKhop
  have hcount0 : 0 ≤ (2 + Real.sqrt d * Khop) ^ d := by positivity
  have hnorm0 : 0 ≤ ‖toFullBlockMat (relMean P q b t)‖ := norm_nonneg _
  have hcoeffEq :
      ((((2 * (d : ℝ)) ^ Q⁻¹ *
            ((1 - etaX)⁻¹ * ‖toFullBlockMat (relMean P q b t)‖)) *
          CW * (3 : ℝ) ^ (-rhoMax * ((n : ℝ) - (b : ℝ)))) ^ Q) *
        ((2 + Real.sqrt d * Khop) ^ d *
          (3 : ℝ) ^ ((n - b) * (d : ℤ))) =
      ((2 * (d : ℝ)) ^ Q⁻¹ * (1 - etaX)⁻¹ * CW) ^ Q *
        (2 + Real.sqrt d * Khop) ^ d *
          (((3 : ℝ) ^ (-(rhoMax - (d : ℝ) / Q) *
              ((n : ℝ) - (b : ℝ))) *
            ‖toFullBlockMat (relMean P q b t)‖) ^ Q) := by
    rw [Real.mul_rpow
        (mul_nonneg (mul_nonneg hK0 (mul_nonneg hinv0 hnorm0)) hCW0)
        (Real.rpow_nonneg h3.le _),
      show (2 * (d : ℝ)) ^ Q⁻¹ *
          ((1 - etaX)⁻¹ * ‖toFullBlockMat (relMean P q b t)‖) * CW =
        (((2 * (d : ℝ)) ^ Q⁻¹ * (1 - etaX)⁻¹ * CW) *
          ‖toFullBlockMat (relMean P q b t)‖) by ring,
      Real.mul_rpow (mul_nonneg (mul_nonneg hK0 hinv0) hCW0) hnorm0,
      Real.mul_rpow (Real.rpow_nonneg h3.le _) hnorm0,
      ← Real.rpow_mul h3.le, ← Real.rpow_mul h3.le,
      ← Real.rpow_intCast (3 : ℝ) ((n - b) * (d : ℤ))]
    push_cast
    have hpow : (3 : ℝ) ^ (-rhoMax * ((n : ℝ) - (b : ℝ)) * Q) *
          (3 : ℝ) ^ (((n : ℝ) - (b : ℝ)) * (d : ℝ)) =
        (3 : ℝ) ^ (-(rhoMax - (d : ℝ) / Q) *
          ((n : ℝ) - (b : ℝ)) * Q) := by
      rw [← Real.rpow_add h3]
      congr 1
      field_simp
      ring
    rw [show (((2 * (d : ℝ)) ^ Q⁻¹ * (1 - etaX)⁻¹ * CW) ^ Q *
          ‖toFullBlockMat (relMean P q b t)‖ ^ Q *
          (3 : ℝ) ^ (-rhoMax * ((n : ℝ) - (b : ℝ)) * Q)) *
            ((2 + Real.sqrt d * Khop) ^ d *
              (3 : ℝ) ^ (((n : ℝ) - (b : ℝ)) * (d : ℝ))) =
        ((2 * (d : ℝ)) ^ Q⁻¹ * (1 - etaX)⁻¹ * CW) ^ Q *
          (2 + Real.sqrt d * Khop) ^ d *
          ‖toFullBlockMat (relMean P q b t)‖ ^ Q *
          ((3 : ℝ) ^ (-rhoMax * ((n : ℝ) - (b : ℝ)) * Q) *
            (3 : ℝ) ^ (((n : ℝ) - (b : ℝ)) * (d : ℝ))) by ring,
      hpow]
    ring
  have hfacBase : (2 * (d : ℝ)) ^ Q⁻¹ * (1 - etaX)⁻¹ * CW ≤
      (2 * (d : ℝ)) ^ Q⁻¹ * (4 / 3 : ℝ) * CW := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hinv43 hK0) hCW0
  have hfacPow :
      ((2 * (d : ℝ)) ^ Q⁻¹ * (1 - etaX)⁻¹ * CW) ^ Q ≤
        ((2 * (d : ℝ)) ^ Q⁻¹ * (4 / 3 : ℝ) * CW) ^ Q :=
    Real.rpow_le_rpow (mul_nonneg (mul_nonneg hK0 hinv0) hCW0) hfacBase hQ.le
  have hroot := inherited_coefficient_le (d := d) (g := g) (Q := Q)
    (rhoMax := rhoMax) (a := a) (l0 := l0) hg hQ hadef hbn ht hPm
  have hroot0 : 0 ≤
      ((3 : ℝ) ^ (-(rhoMax - (d : ℝ) / Q) *
          ((n : ℝ) - (b : ℝ))) *
        ‖toFullBlockMat (relMean P q b t)‖) ^ Q :=
    Real.rpow_nonneg (mul_nonneg (Real.rpow_nonneg h3.le _) hnorm0) _
  have hgain0 : 0 ≤ frakH Q (relMean P q b t) := zero_le_frakH hQ.le hPm
  have hbr0 : 0 ≤ (3 : ℝ) ^ (-a * ((t : ℝ) - (b : ℝ))) *
      (1 + frakH Q (relMean P q b t)) :=
    mul_nonneg (Real.rpow_nonneg h3.le _) (by linarith only [hgain0])
  let Cinh : ℝ :=
    ((2 * (d : ℝ)) ^ Q⁻¹ * (4 / 3 : ℝ) * CW) ^ Q *
      (2 + Real.sqrt d * Khop) ^ d
  have hCinh0 : 0 ≤ Cinh :=
    mul_nonneg (Real.rpow_nonneg
      (mul_nonneg (mul_nonneg hK0 (by norm_num : (0 : ℝ) ≤ 4 / 3)) hCW0) _)
      hcount0
  have hcoef :
      ((((2 * (d : ℝ)) ^ Q⁻¹ *
            ((1 - etaX)⁻¹ * ‖toFullBlockMat (relMean P q b t)‖)) *
          CW * (3 : ℝ) ^ (-rhoMax * ((n : ℝ) - (b : ℝ)))) ^ Q) *
        ((2 + Real.sqrt d * Khop) ^ d *
          (3 : ℝ) ^ ((n - b) * (d : ℤ))) ≤
      Cinh * (3 : ℝ) ^ (a * l0) *
        ((3 : ℝ) ^ (-a * ((t : ℝ) - (b : ℝ))) *
          (1 + frakH Q (relMean P q b t))) := by
    rw [hcoeffEq]
    have hfacCount := mul_le_mul_of_nonneg_right hfacPow hcount0
    have hfirst := mul_le_mul_of_nonneg_right hfacCount hroot0
    have hsecond := mul_le_mul_of_nonneg_left hroot hCinh0
    exact hfirst.trans (by simpa only [Cinh, mul_assoc] using hsecond)
  have hactual0 : 0 ≤
      (((2 * (d : ℝ)) ^ Q⁻¹ *
          ((1 - etaX)⁻¹ * ‖toFullBlockMat (relMean P q b t)‖)) *
        CW * (3 : ℝ) ^ (-rhoMax * ((n : ℝ) - (b : ℝ)))) ^ Q :=
    Real.rpow_nonneg (by positivity) _
  have hprofile : ENNReal.ofReal
        ((3 : ℝ) ^ (-a * ((t : ℝ) - (b : ℝ))) *
          (1 + frakH Q (relMean P q b t))) *
        centeredHistory P Q rhoMax q jStar b ≤
      portableProfile P Q a rhoMax q jStar b t := by
    rw [portableProfile, portableHistory]
    exact le_trans (mul_le_mul' le_rfl (le_add_right le_rfl))
      (le_add_right (le_add_right le_rfl))
  change ∫⁻ x, ENNReal.ofReal
      (((Finset.Icc jStar n).sigma ZT).sup' hs fun i =>
        (3 : ℝ) ^ (rhoMax * ((i.1 : ℝ) - (n : ℝ))) * u i.1 i.2 x) ^ Q ∂P ≤ _
  refine hmaxBound.trans ?_
  rw [← mul_assoc, ← ENNReal.ofReal_mul hactual0]
  refine (mul_le_mul' (ENNReal.ofReal_le_ofReal hcoef) le_rfl).trans ?_
  rw [show Cinh * (3 : ℝ) ^ (a * l0) *
        ((3 : ℝ) ^ (-a * ((t : ℝ) - (b : ℝ))) *
          (1 + frakH Q (relMean P q b t))) =
      (Cinh * (3 : ℝ) ^ (a * l0)) *
        ((3 : ℝ) ^ (-a * ((t : ℝ) - (b : ℝ))) *
          (1 + frakH Q (relMean P q b t))) by ring,
    ENNReal.ofReal_mul (mul_nonneg hCinh0 (Real.rpow_nonneg h3.le _)), mul_assoc]
  exact mul_le_mul' le_rfl hprofile

end

end Transport
end HighContrast
end Homogenization
