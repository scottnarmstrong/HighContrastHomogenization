/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Recurrence.SchattenSpectral

/-!
# Traces under the Loewner order

The matrix layer the transport's near-isometric comparison rests on.  Three
facts are needed, and none of them is in the ambient library.

First, the trace pairing sees the spectral order: the trace of a product of two
positive semidefinite matrices is nonnegative, so the trace of `WV` is at most
the spectral size of `V` times the trace of `W`.

Second, a congruence carries the spectral bound across: `S^tS` and `SS^t` have
the same spectral size, by the `C⋆` identity, so a Loewner bound on the first is
one on the second, and the trace of `S^tWS` is at most that bound times the
trace of `W`.

Third, the trace of the spectral positive part of a symmetric matrix is at most
the trace of any positive semidefinite matrix above it.  Read in the eigenbasis
of the lower matrix, this is a diagonal comparison: the eigenvalues are the
diagonal entries of the congruence of the lower matrix, the congruence of the
majorant has nonnegative diagonal, and the trace is invariant under the
congruence.
-/

namespace Homogenization
namespace HighContrast
namespace Transport

open scoped MatrixOrder Matrix.Norms.L2Operator Matrix

noncomputable section

section Matrices

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## Congruences of positive matrices -/

omit [DecidableEq n] in
/-- A real congruence of a positive semidefinite matrix is positive
semidefinite. -/
theorem posSemidef_transpose_conj {W : Matrix n n ℝ} (hW : W.PosSemidef)
    (S : Matrix n n ℝ) : (Sᵀ * W * S).PosSemidef := by
  have h := hW.conjTranspose_mul_mul_same S
  rwa [conjTranspose_eq_transpose' S] at h

omit [DecidableEq n] in
/-- The Gram matrix of a real matrix is positive semidefinite. -/
theorem posSemidef_transpose_mul_self (S : Matrix n n ℝ) : (Sᵀ * S).PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self S
  rwa [conjTranspose_eq_transpose' S] at h

omit [DecidableEq n] in
/-- The reversed Gram matrix of a real matrix is positive semidefinite. -/
theorem posSemidef_self_mul_transpose (S : Matrix n n ℝ) : (S * Sᵀ).PosSemidef := by
  have h := Matrix.posSemidef_self_mul_conjTranspose S
  rwa [conjTranspose_eq_transpose' S] at h

/-! ## Traces under the Loewner order -/

/-- The Loewner order compares diagonal entries. -/
private theorem diag_le_of_le {A B : Matrix n n ℝ} (h : A ≤ B) (i : n) : A i i ≤ B i i := by
  have hPS : (B - A).PosSemidef := Matrix.le_iff.mp h
  have hq := hPS.dotProduct_mulVec_nonneg (Pi.single i (1 : ℝ))
  simp at hq
  linarith only [hq]

/-- The trace of a product of two positive semidefinite matrices is
nonnegative: the product has the same trace as the positive semidefinite
congruence `W^{1/2}VW^{1/2}`. -/
private theorem zero_le_trace_mul {W V : Matrix n n ℝ} (hW : W.PosSemidef)
    (hV : V.PosSemidef) : 0 ≤ Matrix.trace (W * V) := by
  obtain ⟨hrootps, hroot⟩ := matSqrt_spec hW
  have hnn := (hV.conjTranspose_mul_mul_same (matSqrt W)).trace_nonneg
  rw [hrootps.isHermitian] at hnn
  have hcyc : Matrix.trace (matSqrt W * V * matSqrt W) = Matrix.trace (W * V) := by
    rw [Matrix.trace_mul_cycle, hroot]
  rwa [hcyc] at hnn

/-- **The spectral bound moves through a trace pairing.**  For positive
semidefinite `W` and `V`, the trace of `WV` is at most the spectral size of `V`
times the trace of `W`. -/
private theorem trace_mul_le_norm_mul_trace {W V : Matrix n n ℝ} (hW : W.PosSemidef)
    (hV : V.PosSemidef) : Matrix.trace (W * V) ≤ ‖V‖ * Matrix.trace W := by
  have hdiff : ((‖V‖ • (1 : Matrix n n ℝ)) - V).PosSemidef :=
    Matrix.le_iff.mp (le_norm_smul_one hV)
  have hnn := zero_le_trace_mul hW hdiff
  rw [Matrix.mul_sub, Matrix.trace_sub, Matrix.mul_smul, Matrix.mul_one,
    Matrix.trace_smul, smul_eq_mul] at hnn
  linarith only [hnn]

/-- **The two Gram matrices of a congruence carry the same spectral bound.**
The `C⋆` identity `‖SS^t‖ = ‖S‖² = ‖S^tS‖` turns a Loewner bound on one into a
Loewner bound on the other. -/
theorem self_mul_transpose_le_smul_one {S : Matrix n n ℝ} {c : ℝ} (hc : 0 ≤ c)
    (h : Sᵀ * S ≤ c • (1 : Matrix n n ℝ)) : S * Sᵀ ≤ c • (1 : Matrix n n ℝ) := by
  have hps : (S * Sᵀ).PosSemidef := posSemidef_self_mul_transpose S
  have hnormT : ‖Sᵀ * S‖ ≤ c := norm_le_of_le_smul_one (posSemidef_transpose_mul_self S) hc h
  have hnorm : ‖S * Sᵀ‖ = ‖Sᵀ * S‖ := by
    rw [← conjTranspose_eq_transpose' S, ← Matrix.star_eq_conjTranspose,
      CStarRing.norm_self_mul_star, CStarRing.norm_star_mul_self]
  refine (le_norm_smul_one hps).trans ?_
  rw [hnorm]
  refine Matrix.le_iff.mpr ?_
  have hrw : c • (1 : Matrix n n ℝ) - ‖Sᵀ * S‖ • 1 = (c - ‖Sᵀ * S‖) • (1 : Matrix n n ℝ) := by
    rw [sub_smul]
  rw [hrw]
  exact (Matrix.PosSemidef.one).smul (sub_nonneg.mpr hnormT)

/-- **The congruence of a positive matrix has controlled trace.**  If the Gram
matrix of `S` is at most `c` times the identity, then the trace of `S^tWS` is at
most `c` times the trace of `W`, for every positive semidefinite `W`. -/
theorem trace_conj_le_mul_trace {S W : Matrix n n ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hW : W.PosSemidef) (h : Sᵀ * S ≤ c • (1 : Matrix n n ℝ)) :
    Matrix.trace (Sᵀ * W * S) ≤ c * Matrix.trace W := by
  have hps : (S * Sᵀ).PosSemidef := posSemidef_self_mul_transpose S
  have hcyc : Matrix.trace (Sᵀ * W * S) = Matrix.trace (W * (S * Sᵀ)) := by
    rw [Matrix.trace_mul_cycle, Matrix.trace_mul_comm]
  have hnorm : ‖S * Sᵀ‖ ≤ c :=
    norm_le_of_le_smul_one hps hc (self_mul_transpose_le_smul_one hc h)
  rw [hcyc]
  exact (trace_mul_le_norm_mul_trace hW hps).trans
    (mul_le_mul_of_nonneg_right hnorm hW.trace_nonneg)

/-! ## The trace of a positive part -/

/-- **The trace of the positive part is monotone against a positive majorant.**
If a symmetric matrix lies below a positive semidefinite one, the trace of its
spectral positive part is at most the trace of the majorant.  Read in the
eigenbasis of the lower matrix, this is the comparison of diagonal entries: the
`i`-th eigenvalue is a diagonal entry of the congruence of the lower matrix, the
congruence of the majorant has nonnegative diagonal, and the trace is invariant
under the congruence. -/
theorem trace_posPart_le_of_le {M N : Matrix n n ℝ} (hM : M.IsHermitian)
    (hN : N.PosSemidef) (h : M ≤ N) :
    Matrix.trace (cfc (fun x : ℝ => max x 0) M) ≤ Matrix.trace N := by
  set U : Matrix n n ℝ := (hM.eigenvectorUnitary : Matrix n n ℝ) with hUdef
  have hU1 : Uᴴ * U = 1 := by
    simpa [hUdef, Matrix.star_eq_conjTranspose] using
      Unitary.coe_star_mul_self hM.eigenvectorUnitary
  have hU2 : U * Uᴴ = 1 := by
    simpa [hUdef, Matrix.star_eq_conjTranspose] using
      Unitary.coe_mul_star_self hM.eigenvectorUnitary
  have hspec : M = U * Matrix.diagonal hM.eigenvalues * Uᴴ := by
    conv_lhs => rw [hM.spectral_theorem]
    simp [hUdef, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose]
  have hdiag : Uᴴ * M * U = Matrix.diagonal hM.eigenvalues := by
    conv_lhs => rw [hspec]
    calc Uᴴ * (U * Matrix.diagonal hM.eigenvalues * Uᴴ) * U
        = (Uᴴ * U) * Matrix.diagonal hM.eigenvalues * (Uᴴ * U) := by noncomm_ring
      _ = Matrix.diagonal hM.eigenvalues := by rw [hU1, Matrix.one_mul, Matrix.mul_one]
  have hcong : Uᴴ * M * U ≤ Uᴴ * N * U := conj_le_conj U h
  have hNc : (Uᴴ * N * U).PosSemidef := hN.conjTranspose_mul_mul_same U
  have hentry : ∀ i, max (hM.eigenvalues i) 0 ≤ (Uᴴ * N * U) i i := by
    intro i
    have hle : hM.eigenvalues i ≤ (Uᴴ * N * U) i i := by
      have hd := diag_le_of_le hcong i
      rwa [hdiag, Matrix.diagonal_apply_eq] at hd
    have hnn : 0 ≤ (Uᴴ * N * U) i i := by
      have hq := hNc.dotProduct_mulVec_nonneg (Pi.single i (1 : ℝ))
      simpa using hq
    exact max_le hle hnn
  have htrN : Matrix.trace (Uᴴ * N * U) = Matrix.trace N := by
    rw [Matrix.trace_mul_cycle, hU2, Matrix.one_mul]
  rw [Recurrence.trace_cfc_eq_sum_eigenvalues hM]
  calc ∑ i, max (hM.eigenvalues i) 0 ≤ ∑ i, (Uᴴ * N * U) i i :=
        Finset.sum_le_sum fun i _ => hentry i
    _ = Matrix.trace N := htrN

/-- The trace of a spectral positive part is nonnegative. -/
theorem zero_le_trace_posPart {M : Matrix n n ℝ} (hM : M.IsHermitian) :
    0 ≤ Matrix.trace (cfc (fun x : ℝ => max x 0) M) := by
  rw [Recurrence.trace_cfc_eq_sum_eigenvalues hM]
  exact Finset.sum_nonneg fun i _ => le_max_right _ _

end Matrices

end

end Transport
end HighContrast
end Homogenization
