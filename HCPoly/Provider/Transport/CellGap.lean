/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Transport.CellUpperMean

/-!
# The gap of the upper comparison at a target cell

Every estimate downstream of the transport's target cell reads the mean `K_W` of
the upper comparison only through the gap functional `𝔤_Q(K_W)`.  This file
computes it: the printed display `e.two.grid.whitney.mean.bound`.

The domination of the upper mean by the transported combination turns, on
traces, into a scalar perturbation of the gain, and the gain absorbs an
additive perturbation at the cost of a constant: writing
`u = tr(\widehat P_W - I)` and `v` for the trace of the source term,

`(1 + u + v)^Q - 1 ≤ 2^Q((1 + u)^Q - 1) + 2^Q(v + v^Q)`,

the two summands `v` and `v^Q` being exactly the two printed source terms.  On
the small branch the estimate is the product bound `1+u+v ≤ (1+u)(1+v)` together
with the convexity of the gain at one; on the large branch it is the power-mean
split, whose scale-free residue is charged to `v^Q`.

Composing the perturbation with the near-isometric comparison and the convexity
of the gain gives the printed display: the gap of the upper mean is a constant
times the weighted gain of the selected cells, plus the same constant times the
bridge error, plus the same constant times the two source terms.  When the
target cell carries no selected cell only the source terms survive.
-/

namespace Homogenization
namespace HighContrast
namespace Transport

open scoped MatrixOrder Matrix.Norms.L2Operator Matrix

noncomputable section

section Blocks

variable {d : ℕ}

/-! ## The gain under an additive perturbation -/

/-- **The gain absorbs an additive perturbation.**  For nonnegative `u` and `v`
the gain at `u + v` is at most a constant times the gain at `u` plus the same
constant times `v + v^Q`.  Below one the estimate is the product bound
`1 + u + v ≤ (1+u)(1+v)` together with the convexity of the gain; above one it
is the power-mean split, whose scale-free residue is charged to `v^Q`. -/
private theorem rpow_gain_add_le {Q u v : ℝ} (hQ : 1 ≤ Q) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (1 + (u + v)) ^ Q - 1 ≤ 2 ^ Q * ((1 + u) ^ Q - 1) + 2 ^ Q * (v + v ^ Q) := by
  have hQ0 : (0 : ℝ) ≤ Q := by linarith only [hQ]
  have hE0 : (0 : ℝ) ≤ (2 : ℝ) ^ Q := Real.rpow_nonneg (by norm_num) _
  have hA0 : (0 : ℝ) ≤ (1 + u) ^ Q - 1 := by
    have h1 : (1 : ℝ) ^ Q ≤ (1 + u) ^ Q :=
      Real.rpow_le_rpow zero_le_one (by linarith only [hu]) hQ0
    rw [Real.one_rpow] at h1
    linarith only [h1]
  have hvQ0 : (0 : ℝ) ≤ v ^ Q := Real.rpow_nonneg hv _
  rcases le_or_gt v 1 with hv1 | hv1
  · have hprod : 1 + (u + v) ≤ (1 + u) * (1 + v) := by
      have huv : 0 ≤ u * v := mul_nonneg hu hv
      linarith only [huv]
    have hpow : (1 + (u + v)) ^ Q ≤ (1 + u) ^ Q * (1 + v) ^ Q := by
      have h := Real.rpow_le_rpow (by linarith only [hu, hv]) hprod hQ0
      rwa [Real.mul_rpow (by linarith only [hu]) (by linarith only [hv])] at h
    have hB : (1 + v) ^ Q ≤ (2 : ℝ) ^ Q :=
      Real.rpow_le_rpow (by linarith only [hv]) (by linarith only [hv1]) hQ0
    have hcvx := rpow_sub_one_le_div_mul (Q := Q) (t := v) (T := 1) hQ hv hv1 one_pos
    rw [div_one] at hcvx
    norm_num at hcvx
    have hfac : (1 + v) ^ Q * ((1 + u) ^ Q - 1) ≤ (2 : ℝ) ^ Q * ((1 + u) ^ Q - 1) :=
      mul_le_mul_of_nonneg_right hB hA0
    have hres : v * ((2 : ℝ) ^ Q - 1) ≤ (2 : ℝ) ^ Q * v := by
      have h := mul_le_mul_of_nonneg_left (by linarith only [] : (2 : ℝ) ^ Q - 1 ≤ 2 ^ Q) hv
      linarith only [h]
    have htail : (2 : ℝ) ^ Q * v ≤ (2 : ℝ) ^ Q * (v + v ^ Q) :=
      mul_le_mul_of_nonneg_left (by linarith only [hvQ0]) hE0
    have hexp : (1 + u) ^ Q * (1 + v) ^ Q =
        (1 + v) ^ Q * ((1 + u) ^ Q - 1) + ((1 + v) ^ Q - 1) + 1 := by ring
    linarith only [hpow, hexp, hfac, hcvx, hres, htail]
  · have hD1 : (1 : ℝ) ≤ (2 : ℝ) ^ (Q - 1) :=
      Real.one_le_rpow (by norm_num) (by linarith only [hQ])
    have hE : (2 : ℝ) ^ Q = 2 * (2 : ℝ) ^ (Q - 1) := by
      rw [show Q = (Q - 1) + 1 by ring, Real.rpow_add (by norm_num), Real.rpow_one]
      ring_nf
    have hvQ1 : (1 : ℝ) ≤ v ^ Q := Real.one_le_rpow (by linarith only [hv1]) hQ0
    have hsplit : (1 + (u + v)) ^ Q ≤ (2 : ℝ) ^ (Q - 1) * ((1 + u) ^ Q + v ^ Q) := by
      have h := Recurrence.rpow_add_le_two_rpow_mul_add (a := 1 + u) (b := v) (s := Q)
        (by linarith only [hu]) hv hQ
      rwa [show (1 : ℝ) + u + v = 1 + (u + v) by ring] at h
    have hfac : (2 : ℝ) ^ (Q - 1) * ((1 + u) ^ Q - 1) ≤ (2 : ℝ) ^ Q * ((1 + u) ^ Q - 1) :=
      mul_le_mul_of_nonneg_right (by linarith only [hE, hD1]) hA0
    have hres : (2 : ℝ) ^ (Q - 1) - 1 ≤ ((2 : ℝ) ^ (Q - 1) - 1) * v ^ Q := by
      have h := mul_le_mul_of_nonneg_left hvQ1 (by linarith only [hD1] :
        (0 : ℝ) ≤ (2 : ℝ) ^ (Q - 1) - 1)
      linarith only [h]
    have htail : (2 : ℝ) ^ Q * v ^ Q ≤ (2 : ℝ) ^ Q * (v + v ^ Q) :=
      mul_le_mul_of_nonneg_left (by linarith only [hv, hv1]) hE0
    have hexp : (2 : ℝ) ^ (Q - 1) * ((1 + u) ^ Q + v ^ Q) =
        (2 : ℝ) ^ (Q - 1) * ((1 + u) ^ Q - 1) + ((2 : ℝ) ^ (Q - 1) - 1) * v ^ Q +
          (2 : ℝ) ^ (Q - 1) * v ^ Q + ((2 : ℝ) ^ (Q - 1) - 1) + 1 -
          ((2 : ℝ) ^ (Q - 1) - 1) * v ^ Q - ((2 : ℝ) ^ (Q - 1) - 1) +
          ((2 : ℝ) ^ (Q - 1) - 1) * v ^ Q + ((2 : ℝ) ^ (Q - 1) - 1) -
          ((2 : ℝ) ^ (Q - 1) - 1) * v ^ Q := by ring
    have hEv : (2 : ℝ) ^ Q * v ^ Q =
        (2 : ℝ) ^ (Q - 1) * v ^ Q + ((2 : ℝ) ^ (Q - 1) - 1) * v ^ Q + v ^ Q := by
      rw [hE]; ring
    linarith only [hsplit, hexp, hfac, hres, htail, hEv, hvQ0]

/-! ## The gain of the upper mean -/

/-- **The gain is monotone in the Loewner order above the identity.**  The gain
reads the block through its trace gap alone, and the trace is monotone. -/
theorem frakH_le_of_le {Q : ℝ} (hQ : 0 ≤ Q) {H K : BlockMat d}
    (hIH : (1 : FullBlockMat d) ≤ toFullBlockMat H)
    (hHK : toFullBlockMat H ≤ toFullBlockMat K) : frakH Q H ≤ frakH Q K := by
  have hH0 : 0 ≤ blockTrace H - 2 * (d : ℝ) := zero_le_trace_gap hIH
  have htr : blockTrace H ≤ blockTrace K := by
    have hnn := (Matrix.le_iff.mp hHK).trace_nonneg
    rw [Matrix.trace_sub] at hnn
    have hHval : Matrix.trace (toFullBlockMat H) = blockTrace H := rfl
    have hKval : Matrix.trace (toFullBlockMat K) = blockTrace K := rfl
    rw [hHval, hKval] at hnn
    linarith only [hnn]
  have hmono : (1 + (blockTrace H - 2 * (d : ℝ))) ^ Q ≤
      (1 + (blockTrace K - 2 * (d : ℝ))) ^ Q :=
    Real.rpow_le_rpow (by linarith only [hH0]) (by linarith only [htr]) hQ
  rw [frakH, frakH]
  linarith only [hmono]

/-- **The gain of the upper mean.**  The domination of the upper mean by the
transported combination costs one factor `2^Q` on the gain and adds the two
source terms. -/
theorem frakH_cell_le {Q : ℝ} (hQ : 1 ≤ Q) {KW Phat : BlockMat d} {eps : ℝ}
    (heps : 0 ≤ eps) (hIK : (1 : FullBlockMat d) ≤ toFullBlockMat KW)
    (hPhat0 : 0 ≤ blockTrace Phat - 2 * (d : ℝ))
    (h : toFullBlockMat KW ≤ toFullBlockMat Phat + eps • (1 : FullBlockMat d)) :
    frakH Q KW ≤ 2 ^ Q * frakH Q Phat +
      2 ^ Q * (eps * (2 * (d : ℝ)) + (eps * (2 * (d : ℝ))) ^ Q) := by
  have hd0 : (0 : ℝ) ≤ 2 * (d : ℝ) := by positivity
  have hv0 : (0 : ℝ) ≤ eps * (2 * (d : ℝ)) := mul_nonneg heps hd0
  have hK0 : 0 ≤ blockTrace KW - 2 * (d : ℝ) := zero_le_trace_gap hIK
  have htr := blockTrace_le_of_upper_mean_domination h
  have hQ0 : (0 : ℝ) ≤ Q := by linarith only [hQ]
  have hmono : (1 + (blockTrace KW - 2 * (d : ℝ))) ^ Q ≤
      (1 + ((blockTrace Phat - 2 * (d : ℝ)) + eps * (2 * (d : ℝ)))) ^ Q :=
    Real.rpow_le_rpow (by linarith only [hK0]) (by linarith only [htr]) hQ0
  have hgain := rpow_gain_add_le (Q := Q) (u := blockTrace Phat - 2 * (d : ℝ))
    (v := eps * (2 * (d : ℝ))) hQ hPhat0 hv0
  rw [frakH, frakH]
  linarith only [hmono, hgain]

/-! ## The printed displays -/

/-- **`e.two.grid.whitney.mean.bound`.**  The gap functional of the upper mean
of a target cell is a constant times the weighted gain of the selected cells,
plus the same constant times the bridge error, plus the same constant times the
two source terms.

The upper mean is the transported convex combination corrected for the unfilled
mass and perturbed by the mean of the normalized source residual; the
correction is subtracted from a positive matrix, and the residual is bounded by
`eps`.  The chain is the domination, the comparability of the two gain
functions, the near-isometric comparison, and the convexity of the gain. -/
theorem cell_gap {ι : Type*} (s : Finset ι) (hd : 1 ≤ d) {Q : ℝ} (hQ : 1 ≤ Q)
    {theta : ι → ℝ} {Pa : ι → BlockMat d} {Pbar Mblk Phat KW Rm : BlockMat d}
    {S : FullBlockMat d} {eta eps : ℝ}
    (hth : ∀ α ∈ s, 0 ≤ theta α) (hm : ∑ α ∈ s, theta α ≤ 1)
    (hPa : ∀ α ∈ s, (1 : FullBlockMat d) ≤ toFullBlockMat (Pa α))
    (hPbar : toFullBlockMat Pbar =
      ∑ α ∈ s, theta α • toFullBlockMat (Pa α) +
        (1 - ∑ α ∈ s, theta α) • (1 : FullBlockMat d))
    (heta : 0 ≤ eta) (heta3 : eta ≤ 1 / 3) (heps : 0 ≤ eps)
    (hS : Sᵀ * S ≤ (1 + eta) • (1 : FullBlockMat d))
    (hR : toFullBlockMat Rm ≤ eps • (1 : FullBlockMat d))
    (hM : toFullBlockMat Mblk = Sᵀ * toFullBlockMat Pbar * S - 1)
    (hPhat : toFullBlockMat Phat = 1 + toFullBlockMat (blockPosPart Mblk))
    (hKW : toFullBlockMat KW =
      Sᵀ * toFullBlockMat Pbar * S - (1 - ∑ α ∈ s, theta α) • (Sᵀ * S) +
        toFullBlockMat Rm)
    (hIK : (1 : FullBlockMat d) ≤ toFullBlockMat KW) :
    gapG Q KW ≤ 2 * 2 ^ Q * (1 + 2 * (d : ℝ)) ^ Q *
      ((∑ α ∈ s, theta α * frakH Q (Pa α)) + 3 * eta + (eps + eps ^ Q)) := by
  have hQ0 : (0 : ℝ) ≤ Q := by linarith only [hQ]
  have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hE0 : (0 : ℝ) ≤ (2 : ℝ) ^ Q := Real.rpow_nonneg (by norm_num) _
  have hK0 : (0 : ℝ) ≤ (1 + 2 * (d : ℝ)) ^ Q := Real.rpow_nonneg (by linarith only [hdR]) _
  -- the combination lies above the identity, and its gain is convex
  have hPbarI : (1 : FullBlockMat d) ≤ toFullBlockMat Pbar := by
    rw [hPbar]
    have hsum : (1 : FullBlockMat d) ≤
        ∑ α ∈ s, theta α • (1 : FullBlockMat d) + (1 - ∑ α ∈ s, theta α) • 1 := by
      rw [← Finset.sum_smul, ← add_smul]
      simp
    refine hsum.trans (add_le_add ?_ le_rfl)
    refine Finset.sum_le_sum fun α hα => ?_
    exact Matrix.le_iff.mpr
      (by simpa [smul_sub] using (Matrix.le_iff.mp (hPa α hα)).smul (hth α hα))
  have hpacket := positive_packet s hQ theta hth hm Pbar Pa hPa hPbar
  -- the near isometry, the domination, and the two gain functions
  have hnear := near_isometry (Q := Q) hQ hd heta heta3 hPbarI hS hM hPhat
  have hPhat0 : 0 ≤ blockTrace Phat - 2 * (d : ℝ) := by
    have hMherm : (toFullBlockMat Mblk).IsHermitian := by
      rw [hM]
      exact (posSemidef_transpose_conj (posDef_of_one_le hPbarI).posSemidef S).isHermitian.sub
        Matrix.isHermitian_one
    exact zero_le_trace_gap_transported hMherm hPhat
  have hdom := upper_mean_domination (mW := ∑ α ∈ s, theta α) hm hPbarI hR hM hPhat hKW
  have hcell := frakH_cell_le hQ heps hIK hPhat0 hdom
  have hgap := gapG_le_two_mul_frakH (Q := Q) hQ hIK
  -- the source terms of the perturbation are below the printed pair
  have hsrc : eps * (2 * (d : ℝ)) + (eps * (2 * (d : ℝ))) ^ Q ≤
      (1 + 2 * (d : ℝ)) ^ Q * (eps + eps ^ Q) := by
    have hbase : (1 : ℝ) ≤ (1 + 2 * (d : ℝ)) ^ Q := by
      refine Real.one_le_rpow ?_ hQ0
      linarith only [hdR]
    have hlin : 2 * (d : ℝ) ≤ (1 + 2 * (d : ℝ)) ^ Q := by
      have h := Real.rpow_le_rpow (by linarith only [hdR] : (0 : ℝ) ≤ 1 + 2 * (d : ℝ))
        (le_refl (1 + 2 * (d : ℝ))) hQ0
      have hone : (1 + 2 * (d : ℝ)) ^ (1 : ℝ) ≤ (1 + 2 * (d : ℝ)) ^ Q :=
        Real.rpow_le_rpow_of_exponent_le (by linarith only [hdR]) hQ
      rw [Real.rpow_one] at hone
      linarith only [hone, h]
    have hterm1 : eps * (2 * (d : ℝ)) ≤ (1 + 2 * (d : ℝ)) ^ Q * eps := by
      have h := mul_le_mul_of_nonneg_left hlin heps
      linarith only [h]
    have hterm2 : (eps * (2 * (d : ℝ))) ^ Q ≤ (1 + 2 * (d : ℝ)) ^ Q * eps ^ Q := by
      have hbase : (2 * (d : ℝ)) ^ Q ≤ (1 + 2 * (d : ℝ)) ^ Q :=
        Real.rpow_le_rpow (by positivity) (by linarith only [hdR]) hQ0
      have hmul := mul_le_mul_of_nonneg_left hbase (Real.rpow_nonneg heps Q)
      rw [Real.mul_rpow heps (by positivity)]
      linarith only [hmul]
    have hexp : (1 + 2 * (d : ℝ)) ^ Q * (eps + eps ^ Q) =
        (1 + 2 * (d : ℝ)) ^ Q * eps + (1 + 2 * (d : ℝ)) ^ Q * eps ^ Q := by ring
    linarith only [hterm1, hterm2, hexp]
  -- assemble
  have hcombine : frakH Q Phat ≤ (1 + 2 * (d : ℝ)) ^ Q *
      ((∑ α ∈ s, theta α * frakH Q (Pa α)) + 3 * eta) := by
    have h := mul_le_mul_of_nonneg_left hpacket hK0
    linarith only [hnear, h]
  have hstep : frakH Q KW ≤ 2 ^ Q * ((1 + 2 * (d : ℝ)) ^ Q *
      ((∑ α ∈ s, theta α * frakH Q (Pa α)) + 3 * eta + (eps + eps ^ Q))) := by
    have h1 := mul_le_mul_of_nonneg_left hcombine hE0
    have h2 := mul_le_mul_of_nonneg_left hsrc hE0
    have hexp : 2 ^ Q * ((1 + 2 * (d : ℝ)) ^ Q *
        ((∑ α ∈ s, theta α * frakH Q (Pa α)) + 3 * eta + (eps + eps ^ Q))) =
        2 ^ Q * ((1 + 2 * (d : ℝ)) ^ Q *
          ((∑ α ∈ s, theta α * frakH Q (Pa α)) + 3 * eta)) +
          2 ^ Q * ((1 + 2 * (d : ℝ)) ^ Q * (eps + eps ^ Q)) := by ring
    linarith only [hcell, h1, h2, hexp]
  have hfinal := mul_le_mul_of_nonneg_left hstep (by norm_num : (0 : ℝ) ≤ 2)
  have hassoc : 2 * (2 ^ Q * ((1 + 2 * (d : ℝ)) ^ Q *
      ((∑ α ∈ s, theta α * frakH Q (Pa α)) + 3 * eta + (eps + eps ^ Q)))) =
      2 * 2 ^ Q * (1 + 2 * (d : ℝ)) ^ Q *
        ((∑ α ∈ s, theta α * frakH Q (Pa α)) + 3 * eta + (eps + eps ^ Q)) := by ring
  linarith only [hgap, hfinal, hassoc]

/-- **The gap at an early whole-source level.**  When the target cell carries no
selected cell the upper mean is the identity perturbed by the source residual
alone, and only the two source terms survive on the right. -/
theorem cell_gap_early (hd : 1 ≤ d) {Q : ℝ} (hQ : 1 ≤ Q) {KW : BlockMat d} {eps : ℝ}
    (heps : 0 ≤ eps) (hIK : (1 : FullBlockMat d) ≤ toFullBlockMat KW)
    (h : toFullBlockMat KW ≤ 1 + eps • (1 : FullBlockMat d)) :
    gapG Q KW ≤ 2 * 2 ^ Q * (1 + 2 * (d : ℝ)) ^ Q * (eps + eps ^ Q) := by
  have hQ0 : (0 : ℝ) ≤ Q := by linarith only [hQ]
  have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hE0 : (0 : ℝ) ≤ (2 : ℝ) ^ Q := Real.rpow_nonneg (by norm_num) _
  have hv0 : (0 : ℝ) ≤ eps * (2 * (d : ℝ)) := by positivity
  have hK0 : 0 ≤ blockTrace KW - 2 * (d : ℝ) := zero_le_trace_gap hIK
  have htr := blockTrace_le_of_upper_mean_domination
    (KW := KW) (Phat := ofFullBlockMat (1 : FullBlockMat d)) (eps := eps)
    (by rwa [toFullBlockMat_ofFullBlockMat])
  have hone : blockTrace (ofFullBlockMat (1 : FullBlockMat d)) = 2 * (d : ℝ) := by
    rw [blockTrace, toFullBlockMat_ofFullBlockMat, Matrix.trace_one]
    simp [Fintype.card_sum, two_mul]
  rw [hone] at htr
  have hmono : (1 + (blockTrace KW - 2 * (d : ℝ))) ^ Q ≤ (1 + eps * (2 * (d : ℝ))) ^ Q :=
    Real.rpow_le_rpow (by linarith only [hK0]) (by linarith only [htr]) hQ0
  have hgain := rpow_gain_add_le (Q := Q) (u := 0) (v := eps * (2 * (d : ℝ))) hQ le_rfl hv0
  simp only [zero_add, add_zero, Real.one_rpow] at hgain
  have hfrak : frakH Q KW ≤ 2 ^ Q * (eps * (2 * (d : ℝ)) + (eps * (2 * (d : ℝ))) ^ Q) := by
    rw [frakH]
    linarith only [hmono, hgain]
  have hsrc : eps * (2 * (d : ℝ)) + (eps * (2 * (d : ℝ))) ^ Q ≤
      (1 + 2 * (d : ℝ)) ^ Q * (eps + eps ^ Q) := by
    have hlin : 2 * (d : ℝ) ≤ (1 + 2 * (d : ℝ)) ^ Q := by
      have hone' : (1 + 2 * (d : ℝ)) ^ (1 : ℝ) ≤ (1 + 2 * (d : ℝ)) ^ Q :=
        Real.rpow_le_rpow_of_exponent_le (by linarith only [hdR]) hQ
      rw [Real.rpow_one] at hone'
      linarith only [hone']
    have hterm1 : eps * (2 * (d : ℝ)) ≤ (1 + 2 * (d : ℝ)) ^ Q * eps := by
      have h' := mul_le_mul_of_nonneg_left hlin heps
      linarith only [h']
    have hterm2 : (eps * (2 * (d : ℝ))) ^ Q ≤ (1 + 2 * (d : ℝ)) ^ Q * eps ^ Q := by
      have hbase : (2 * (d : ℝ)) ^ Q ≤ (1 + 2 * (d : ℝ)) ^ Q :=
        Real.rpow_le_rpow (by positivity) (by linarith only [hdR]) hQ0
      have hmul := mul_le_mul_of_nonneg_left hbase (Real.rpow_nonneg heps Q)
      rw [Real.mul_rpow heps (by positivity)]
      linarith only [hmul]
    have hexp : (1 + 2 * (d : ℝ)) ^ Q * (eps + eps ^ Q) =
        (1 + 2 * (d : ℝ)) ^ Q * eps + (1 + 2 * (d : ℝ)) ^ Q * eps ^ Q := by ring
    linarith only [hterm1, hterm2, hexp]
  have hgapc := gapG_le_two_mul_frakH (Q := Q) hQ hIK
  have hstep := mul_le_mul_of_nonneg_left hsrc hE0
  have hassoc : 2 ^ Q * ((1 + 2 * (d : ℝ)) ^ Q * (eps + eps ^ Q)) * 2 =
      2 * 2 ^ Q * (1 + 2 * (d : ℝ)) ^ Q * (eps + eps ^ Q) := by ring
  linarith only [hgapc, hfrak, hstep, hassoc]

end Blocks

end

end Transport
end HighContrast
end Homogenization