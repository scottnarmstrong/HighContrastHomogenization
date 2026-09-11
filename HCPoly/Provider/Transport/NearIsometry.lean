/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Transport.GainConvexity
import HCPoly.Provider.Transport.TraceOrder

/-!
# The near-isometric comparison of the transport

This is the second half of the matrix calculation the proof of
`p.two.grid.transport` isolates and uses at every target cell.
The convex combination `P̄` of the previous module lives on the old grid; the
target cell lives on the new one, and the two normalizations differ by the
bridge congruence `S`.  The display `e.two.grid.whitney.mean.bound` says
that transporting `P̄` costs a factor depending only on `d` and `Q` plus one
*additive* multiple of the bridge error — the error never multiplies the gain.

The mechanism is the splitting
`S^tP̄S - I = S^t(P̄ - I)S + (S^tS - I)`.  The first term is positive and its
trace is at most `(1 + η)tr(P̄ - I)`; the second is bounded above by `η` times
the identity.  So the whole matrix is dominated by a positive matrix of trace at
most `(1 + η)tr(P̄ - I) + 2dη`, and the trace of a spectral positive part is at
most the trace of any positive matrix above it.

The passage from the trace bound to the gain bound is scalar and uses the
convexity of the gain twice: once to absorb the factor `1 + 2dη` into a
constant, and once to see the remaining `(1 + 2dη)^Q - 1` as a multiple of `η`.
-/

namespace Homogenization
namespace HighContrast
namespace Transport

open scoped MatrixOrder Matrix.Norms.L2Operator Matrix

noncomputable section

section Blocks

variable {d : ℕ}

/-- The doubled identity has trace `2d`. -/
private theorem trace_one_blockCoord :
    Matrix.trace (1 : FullBlockMat d) = 2 * (d : ℝ) := by
  rw [Matrix.trace_one]
  simp [Fintype.card_sum, two_mul]

/-- The trace gap of the transported block is the trace of the positive
part. -/
private theorem trace_gap_eq_trace_posPart {Mblk Phat : BlockMat d}
    (hPhat : toFullBlockMat Phat = 1 + toFullBlockMat (blockPosPart Mblk)) :
    blockTrace Phat - 2 * (d : ℝ) =
      Matrix.trace (cfc (fun x : ℝ => max x 0) (toFullBlockMat Mblk)) := by
  have hval : blockTrace Phat = Matrix.trace (toFullBlockMat Phat) := rfl
  rw [hval, hPhat, Matrix.trace_add, trace_one_blockCoord, blockPosPart,
    toFullBlockMat_ofFullBlockMat]
  ring

/-- The transported block minus the identity is symmetric. -/
private theorem isHermitian_transported {Pbar Mblk : BlockMat d} {S : FullBlockMat d}
    (hPbar : (1 : FullBlockMat d) ≤ toFullBlockMat Pbar)
    (hM : toFullBlockMat Mblk = Sᵀ * toFullBlockMat Pbar * S - 1) :
    (toFullBlockMat Mblk).IsHermitian := by
  have hone : (0 : FullBlockMat d) ≤ 1 := by
    refine Matrix.le_iff.mpr ?_
    simpa using (Matrix.PosSemidef.one : (1 : FullBlockMat d).PosSemidef)
  have hPps : (toFullBlockMat Pbar).PosSemidef := by
    have h0 := Matrix.le_iff.mp (hone.trans hPbar)
    simpa using h0
  rw [hM]
  exact (posSemidef_transpose_conj hPps S).isHermitian.sub Matrix.isHermitian_one

/-- The trace gap of the transported block is nonnegative. -/
theorem zero_le_trace_gap_transported {Mblk Phat : BlockMat d}
    (hMherm : (toFullBlockMat Mblk).IsHermitian)
    (hPhat : toFullBlockMat Phat = 1 + toFullBlockMat (blockPosPart Mblk)) :
    0 ≤ blockTrace Phat - 2 * (d : ℝ) := by
  rw [trace_gap_eq_trace_posPart hPhat]
  exact zero_le_trace_posPart hMherm

/-- **The trace half of `e.two.grid.whitney.mean.bound`.**  Transporting the
the combination across the bridge inflates its trace gap by the factor `1 + η` and
adds `2dη`; nothing else is paid. -/
theorem near_isometry_trace {Pbar Mblk Phat : BlockMat d} {S : FullBlockMat d} {eta : ℝ}
    (heta : 0 ≤ eta) (hPbar : (1 : FullBlockMat d) ≤ toFullBlockMat Pbar)
    (hS : Sᵀ * S ≤ (1 + eta) • (1 : FullBlockMat d))
    (hM : toFullBlockMat Mblk = Sᵀ * toFullBlockMat Pbar * S - 1)
    (hPhat : toFullBlockMat Phat = 1 + toFullBlockMat (blockPosPart Mblk)) :
    blockTrace Phat - 2 * (d : ℝ) ≤
      (1 + eta) * (blockTrace Pbar - 2 * (d : ℝ)) + 2 * (d : ℝ) * eta := by
  set W : FullBlockMat d := toFullBlockMat Pbar - 1 with hW
  have hWps : W.PosSemidef := Matrix.le_iff.mp hPbar
  have hWtr : Matrix.trace W = blockTrace Pbar - 2 * (d : ℝ) := by
    rw [hW, Matrix.trace_sub, trace_one_blockCoord]
    rfl
  have hsplit : toFullBlockMat Mblk = Sᵀ * W * S + (Sᵀ * S - 1) := by
    rw [hM, hW, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
    abel
  set N : FullBlockMat d := Sᵀ * W * S + eta • (1 : FullBlockMat d) with hN
  have hconjps : (Sᵀ * W * S).PosSemidef := posSemidef_transpose_conj hWps S
  have hNps : N.PosSemidef := hconjps.add ((Matrix.PosSemidef.one).smul heta)
  have hle : toFullBlockMat Mblk ≤ N := by
    rw [hsplit, hN]
    refine Matrix.le_iff.mpr ?_
    have hrw : Sᵀ * W * S + eta • (1 : FullBlockMat d) - (Sᵀ * W * S + (Sᵀ * S - 1)) =
        (1 + eta) • (1 : FullBlockMat d) - Sᵀ * S := by
      rw [add_smul, one_smul]
      abel
    rw [hrw]
    exact Matrix.le_iff.mp hS
  have hposPart := trace_posPart_le_of_le (isHermitian_transported hPbar hM) hNps hle
  have hNtr : Matrix.trace N = Matrix.trace (Sᵀ * W * S) + 2 * (d : ℝ) * eta := by
    rw [hN, Matrix.trace_add, Matrix.trace_smul, trace_one_blockCoord, smul_eq_mul]
    ring
  have hconjtr : Matrix.trace (Sᵀ * W * S) ≤ (1 + eta) * Matrix.trace W :=
    trace_conj_le_mul_trace (by linarith only [heta]) hWps hS
  rw [trace_gap_eq_trace_posPart hPhat, ← hWtr]
  calc Matrix.trace (cfc (fun x : ℝ => max x 0) (toFullBlockMat Mblk))
      ≤ Matrix.trace N := hposPart
    _ = Matrix.trace (Sᵀ * W * S) + 2 * (d : ℝ) * eta := hNtr
    _ ≤ (1 + eta) * Matrix.trace W + 2 * (d : ℝ) * eta := by
        linarith only [hconjtr]

/-- **`e.two.grid.whitney.mean.bound`.**  The gain of the transported
combination is at most a constant depending only on `d` and `Q` times the gain
of the combination, plus the same constant times the bridge error.  The error is
additive: it never multiplies the gain.

The constant is exhibited as `(1 + 2d)^Q`, and the bridge error enters with a
further factor three. -/
theorem near_isometry {Q : ℝ} (hQ : 1 ≤ Q) (hd : 1 ≤ d)
    {Pbar Mblk Phat : BlockMat d} {S : FullBlockMat d} {eta : ℝ}
    (heta : 0 ≤ eta) (heta3 : eta ≤ 1 / 3)
    (hPbar : (1 : FullBlockMat d) ≤ toFullBlockMat Pbar)
    (hS : Sᵀ * S ≤ (1 + eta) • (1 : FullBlockMat d))
    (hM : toFullBlockMat Mblk = Sᵀ * toFullBlockMat Pbar * S - 1)
    (hPhat : toFullBlockMat Phat = 1 + toFullBlockMat (blockPosPart Mblk)) :
    frakH Q Phat ≤
      (1 + 2 * (d : ℝ)) ^ Q * frakH Q Pbar + 3 * (1 + 2 * (d : ℝ)) ^ Q * eta := by
  have hQ0 : (0 : ℝ) ≤ Q := by linarith only [hQ]
  have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  set b : ℝ := blockTrace Pbar - 2 * (d : ℝ) with hb
  set p : ℝ := blockTrace Phat - 2 * (d : ℝ) with hp
  have hb0 : 0 ≤ b := by
    have hps : (toFullBlockMat Pbar - 1).PosSemidef := Matrix.le_iff.mp hPbar
    have := hps.trace_nonneg
    rwa [Matrix.trace_sub, trace_one_blockCoord] at this
  have hp0 : 0 ≤ p :=
    zero_le_trace_gap_transported (isHermitian_transported hPbar hM) hPhat
  have hptr : p ≤ (1 + eta) * b + 2 * (d : ℝ) * eta :=
    near_isometry_trace heta hPbar hS hM hPhat
  -- the estimate factorizes through the two nonnegative scalars
  set K : ℝ := (1 + 2 * (d : ℝ) * eta) ^ Q with hK
  have hbase : 0 ≤ 1 + 2 * (d : ℝ) * eta := by positivity
  have hfac : 1 + ((1 + eta) * b + 2 * (d : ℝ) * eta) ≤ (1 + b) * (1 + 2 * (d : ℝ) * eta) := by
    have hkey : 0 ≤ eta * b * (2 * (d : ℝ) - 1) := by
      have : (0 : ℝ) ≤ 2 * (d : ℝ) - 1 := by linarith only [hdR]
      positivity
    nlinarith only [hkey]
  have hstep : (1 + p) ^ Q ≤ (1 + b) ^ Q * K := by
    have h1 : (1 + p) ^ Q ≤ ((1 + b) * (1 + 2 * (d : ℝ) * eta)) ^ Q :=
      Real.rpow_le_rpow (by linarith only [hp0]) (by linarith only [hptr, hfac]) hQ0
    rwa [Real.mul_rpow (by linarith only [hb0]) hbase] at h1
  -- the constant and the linear bridge term
  have hKle : K ≤ (1 + 2 * (d : ℝ)) ^ Q := by
    refine Real.rpow_le_rpow hbase ?_ hQ0
    nlinarith only [heta3, heta, hdR]
  have hKone : K - 1 ≤ 3 * (1 + 2 * (d : ℝ)) ^ Q * eta := by
    have hT : (0 : ℝ) < 2 * (d : ℝ) / 3 := by positivity
    have htT : 2 * (d : ℝ) * eta ≤ 2 * (d : ℝ) / 3 := by
      nlinarith only [heta3, hdR]
    have ht : (0 : ℝ) ≤ 2 * (d : ℝ) * eta := by positivity
    have hcvx := rpow_sub_one_le_div_mul (Q := Q) hQ ht htT hT
    have hratio : 2 * (d : ℝ) * eta / (2 * (d : ℝ) / 3) = 3 * eta := by
      have hdne : (d : ℝ) ≠ 0 := by linarith only [hdR]
      field_simp
    rw [hratio] at hcvx
    have hTle : (1 + 2 * (d : ℝ) / 3) ^ Q - 1 ≤ (1 + 2 * (d : ℝ)) ^ Q := by
      have hmono : (1 + 2 * (d : ℝ) / 3) ^ Q ≤ (1 + 2 * (d : ℝ)) ^ Q :=
        Real.rpow_le_rpow (by positivity) (by linarith only [hdR]) hQ0
      linarith only [hmono]
    have h3eta : 0 ≤ 3 * eta := by linarith only [heta]
    calc K - 1 ≤ 3 * eta * ((1 + 2 * (d : ℝ) / 3) ^ Q - 1) := hcvx
      _ ≤ 3 * eta * (1 + 2 * (d : ℝ)) ^ Q := mul_le_mul_of_nonneg_left hTle h3eta
      _ = 3 * (1 + 2 * (d : ℝ)) ^ Q * eta := by ring
  -- assemble
  have hgain0 : 0 ≤ (1 + b) ^ Q - 1 := by
    have h1 : (1 : ℝ) ^ Q ≤ (1 + b) ^ Q :=
      Real.rpow_le_rpow zero_le_one (by linarith only [hb0]) hQ0
    rw [Real.one_rpow] at h1
    linarith only [h1]
  have hKnn : 0 ≤ K := Real.rpow_nonneg hbase Q
  have hfinal : (1 + p) ^ Q - 1 ≤
      (1 + 2 * (d : ℝ)) ^ Q * ((1 + b) ^ Q - 1) + 3 * (1 + 2 * (d : ℝ)) ^ Q * eta := by
    have hsplit : (1 + b) ^ Q * K - 1 = K * ((1 + b) ^ Q - 1) + (K - 1) := by ring
    have hmul : K * ((1 + b) ^ Q - 1) ≤ (1 + 2 * (d : ℝ)) ^ Q * ((1 + b) ^ Q - 1) :=
      mul_le_mul_of_nonneg_right hKle hgain0
    linarith only [hstep, hsplit, hmul, hKone]
  simpa [frakH, hb, hp] using hfinal

end Blocks

end

end Transport
end HighContrast
end Homogenization
