import HCPoly.Entry.Analysis.SchattenCongruence
import HCPoly.Entry.Annealed.AdaptedIntegrability
import HCPoly.Entry.Annealed.LogDetOrder
import HCPoly.Entry.Multiscale.ProfileIdentities
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Normalization transport

`p.fixed.geometry.parent.child.recurrence`: the transport matrix is the product of the
child mean square root and the parent mean inverse square root. Its squared
L2 operator norm is exactly the normalized mean operator norm. The sharp
Schatten congruence bound and the actual mean order give the exponential
loss bound. Both means are proved positive definite before cancellation;
no integrability, positivity, or order premise is added to the recurrence.
-/

open Homogenization.HighContrast (CoeffSpace adaptedMean matSqrt matSqrt_spec normalizedBlock)
namespace Homogenization.HighContrast.Annealed

open MeasureTheory Geometry Set
open scoped Matrix.Norms.L2Operator MatrixOrder Matrix

noncomputable section

variable {d : ℕ}

/-! ## Reproved matSqrt cancellation, generalized to any finite real carrier

`HCPoly.Entry.Geometry.GeometryUpdateBounds.matSqrt_mul_matSqrt_inv`/`matSqrt_inv_mul_matSqrt` are
`private` and specific to `Mat d`; the congruence identity below needs both directions at
`FullBlockMat d = Matrix (BlockCoord d) (BlockCoord d) ℝ`, a different carrier. Reproved here,
generalized to any finite index type, rather than reaching into that file's private
namespace. -/

private theorem posDef_sqrt_full {ι : Type*} [Fintype ι] [DecidableEq ι] {m : Matrix ι ι ℝ}
    (hm : m.PosDef) : (CFC.sqrt m).PosDef :=
  Matrix.IsStrictlyPositive.posDef
    (IsStrictlyPositive.sqrt m (Matrix.isStrictlyPositive_iff_posDef.mpr hm))

private theorem cfc_sqrt_inv_full {ι : Type*} [Fintype ι] [DecidableEq ι] {m : Matrix ι ι ℝ}
    (hm : m.PosDef) : (CFC.sqrt m)⁻¹ = CFC.sqrt m⁻¹ := by
  rw [eq_comm,
    CFC.sqrt_eq_iff _ _ hm.inv.posSemidef.nonneg
      (Matrix.nonneg_iff_posSemidef.1 (CFC.sqrt_nonneg m)).inv.nonneg,
    ← sq, Matrix.inv_pow', CFC.sq_sqrt m]

theorem matSqrt_mul_matSqrt_inv_full {ι : Type*} [Fintype ι] [DecidableEq ι] {m : Matrix ι ι ℝ}
    (hm : m.PosDef) : matSqrt m * matSqrt m⁻¹ = 1 := by
  rw [matSqrt_eq_cfc_sqrt hm.posSemidef, matSqrt_eq_cfc_sqrt hm.inv.posSemidef,
    ← cfc_sqrt_inv_full hm]
  exact Matrix.mul_nonsing_inv (CFC.sqrt m)
    ((Matrix.isUnit_iff_isUnit_det (CFC.sqrt m)).mp (posDef_sqrt_full hm).isUnit)

theorem matSqrt_inv_mul_matSqrt_full {ι : Type*} [Fintype ι] [DecidableEq ι] {m : Matrix ι ι ℝ}
    (hm : m.PosDef) : matSqrt m⁻¹ * matSqrt m = 1 := by
  rw [matSqrt_eq_cfc_sqrt hm.posSemidef, matSqrt_eq_cfc_sqrt hm.inv.posSemidef,
    ← cfc_sqrt_inv_full hm]
  exact Matrix.nonsing_inv_mul (CFC.sqrt m)
    ((Matrix.isUnit_iff_isUnit_det (CFC.sqrt m)).mp (posDef_sqrt_full hm).isUnit)

/-! ## Group 3 item 1: the deterministic congruence identity -/

/-- The printed change-of-normalization matrix `𝐀hom_j^{1/2} 𝐀hom_{j+h}^{-1/2}`. -/
def transportMatrix (Aj Ajh : BlockMat d) : FullBlockMat d :=
  matSqrt (toFullBlockMat Aj) * matSqrt (toFullBlockMat Ajh)⁻¹

/-- The change-of-normalization congruence identity, for every block `X`, given both adapted
means positive definite: a deterministic matrix identity, no probabilistic hypothesis. -/
theorem normalizedBlock_transport_congr {Aj Ajh : BlockMat d}
    (hAj : (toFullBlockMat Aj).PosDef) (hAjh : (toFullBlockMat Ajh).PosDef) (X : BlockMat d) :
    toFullBlockMat (normalizedBlock X Ajh) =
      (transportMatrix Aj Ajh)ᵀ * toFullBlockMat (normalizedBlock X Aj) * transportMatrix Aj Ajh := by
  have hT : (transportMatrix Aj Ajh)ᵀ =
      matSqrt (toFullBlockMat Ajh)⁻¹ * matSqrt (toFullBlockMat Aj) := by
    unfold transportMatrix
    rw [Matrix.transpose_mul,
      ← Matrix.conjTranspose_eq_transpose_of_trivial (matSqrt (toFullBlockMat Ajh)⁻¹),
      ← Matrix.conjTranspose_eq_transpose_of_trivial (matSqrt (toFullBlockMat Aj)),
      (Multiscale.matSqrt_inv_posDef_full hAjh).isHermitian.eq,
      (matSqrt_eq_cfc_sqrt hAj.posSemidef ▸ posDef_sqrt_full hAj : (matSqrt (toFullBlockMat Aj)).PosDef).isHermitian.eq]
  rw [show toFullBlockMat (normalizedBlock X Ajh) =
      matSqrt (toFullBlockMat Ajh)⁻¹ * toFullBlockMat X * matSqrt (toFullBlockMat Ajh)⁻¹ from
    by rw [normalizedBlock, toFullBlockMat_ofFullBlockMat],
    hT,
    show toFullBlockMat (normalizedBlock X Aj) =
      matSqrt (toFullBlockMat Aj)⁻¹ * toFullBlockMat X * matSqrt (toFullBlockMat Aj)⁻¹ from
    by rw [normalizedBlock, toFullBlockMat_ofFullBlockMat],
    show transportMatrix Aj Ajh = matSqrt (toFullBlockMat Aj) * matSqrt (toFullBlockMat Ajh)⁻¹
      from rfl]
  have hassoc : matSqrt (toFullBlockMat Ajh)⁻¹ * matSqrt (toFullBlockMat Aj) *
        (matSqrt (toFullBlockMat Aj)⁻¹ * toFullBlockMat X * matSqrt (toFullBlockMat Aj)⁻¹) *
        (matSqrt (toFullBlockMat Aj) * matSqrt (toFullBlockMat Ajh)⁻¹) =
      matSqrt (toFullBlockMat Ajh)⁻¹ *
        ((matSqrt (toFullBlockMat Aj) * matSqrt (toFullBlockMat Aj)⁻¹) * toFullBlockMat X *
          (matSqrt (toFullBlockMat Aj)⁻¹ * matSqrt (toFullBlockMat Aj))) *
        matSqrt (toFullBlockMat Ajh)⁻¹ := by
    noncomm_ring
  rw [hassoc, matSqrt_mul_matSqrt_inv_full hAj, matSqrt_inv_mul_matSqrt_full hAj]
  simp only [one_mul, mul_one]

/-! ## Group 3 item 2: the operator-norm identity -/

/-- `‖B‖² = |P^q_{j,j+h}|`: the square of the transport matrix's operator norm is exactly the
operator norm of the transported normalized mean, via the C⋆-identity `‖BᵀB‖ = ‖B‖²` (an
**equality**, not merely the fallback inequality). -/
theorem transportMatrix_sq_opNorm_eq (P : Measure (CoeffSpace d)) (q : Mat d) (j h : ℤ)
    (hAj : (toFullBlockMat (adaptedMean P q j)).PosDef)
    (hAjh : (toFullBlockMat (adaptedMean P q (j + h))).PosDef) :
    ‖transportMatrix (adaptedMean P q j) (adaptedMean P q (j + h))‖ ^ 2 =
      blockOpNorm (normalizedMean P q j (j + h)) := by
  set Aj := adaptedMean P q j
  set Ajh := adaptedMean P q (j + h)
  set B := transportMatrix Aj Ajh with hB
  have hBtB : Bᵀ * B = toFullBlockMat (normalizedMean P q j (j + h)) := by
    have hT : Bᵀ = matSqrt (toFullBlockMat Ajh)⁻¹ * matSqrt (toFullBlockMat Aj) := by
      rw [hB]; unfold transportMatrix
      rw [Matrix.transpose_mul,
        ← Matrix.conjTranspose_eq_transpose_of_trivial (matSqrt (toFullBlockMat Ajh)⁻¹),
        ← Matrix.conjTranspose_eq_transpose_of_trivial (matSqrt (toFullBlockMat Aj)),
        (Multiscale.matSqrt_inv_posDef_full hAjh).isHermitian.eq,
      (matSqrt_eq_cfc_sqrt hAj.posSemidef ▸ posDef_sqrt_full hAj : (matSqrt (toFullBlockMat Aj)).PosDef).isHermitian.eq]
    rw [hT, hB]
    unfold transportMatrix normalizedMean normalizedBlock
    rw [toFullBlockMat_ofFullBlockMat]
    have hassoc : matSqrt (toFullBlockMat Ajh)⁻¹ * matSqrt (toFullBlockMat Aj) *
          (matSqrt (toFullBlockMat Aj) * matSqrt (toFullBlockMat Ajh)⁻¹) =
        matSqrt (toFullBlockMat Ajh)⁻¹ *
          (matSqrt (toFullBlockMat Aj) * matSqrt (toFullBlockMat Aj)) *
          matSqrt (toFullBlockMat Ajh)⁻¹ := by
      noncomm_ring
    rw [hassoc, (matSqrt_spec hAj.posSemidef).2]
  have hnorm : ‖Bᵀ * B‖ = ‖B‖ ^ 2 := by
    have h := CStarRing.norm_star_mul_self (x := B)
    rw [show (star B : FullBlockMat d) = Bᵀ from rfl] at h
    rw [h]; ring
  rw [← hnorm, hBtB]
  rfl

/-- Change normalization using the exact operator norm of the transport matrix. -/
theorem lqSchattenNorm_normalizedBlock_congr_le {d : ℕ}
    {P : Measure (CoeffSpace d)} {N : ℝ} (hN : 1 ≤ N)
    {Aj Ak : BlockMat d} (hAj : (toFullBlockMat Aj).PosDef)
    (hAk : (toFullBlockMat Ak).PosDef) (X : CoeffSpace d → BlockMat d)
    (hX : MemLqSchatten P N (fun a => normalizedBlock (X a) Aj)) :
    lqSchattenNorm P N (fun a => normalizedBlock (X a) Ak) ≤
      ‖transportMatrix Aj Ak‖ ^ 2 * lqSchattenNorm P N (fun a => normalizedBlock (X a) Aj) := by
  have heq (a : CoeffSpace d) : normalizedBlock (X a) Ak =
      ofFullBlockMat ((transportMatrix Aj Ak)ᵀ *
        toFullBlockMat (normalizedBlock (X a) Aj) * transportMatrix Aj Ak) := by
    rw [← normalizedBlock_transport_congr hAj hAk, ofFullBlockMat_toFullBlockMat]
  simp_rw [heq]
  exact Analysis.lqSchattenNorm_congr_le hN hX _

/-- Transport between ordered actual means costs at most the exponential determinant loss. -/
theorem lqSchattenNorm_normalizedBlock_transport_le (d : ℕ) (hd : 2 ≤ d)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (γ : ℝ) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ K S)
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (m : Mat d) (hm : m.PosDef)
    (j : ℤ) (hn : ℕ) (hj : (jStar : ℤ) ≤ j) {N : ℝ} (hN : 1 ≤ N)
    (X : CoeffSpace d → BlockMat d)
    (hX : MemLqSchatten P N (fun a => normalizedBlock (X a)
      (adaptedMean P (explicitRoundedGrid jStar m) j))) :
    lqSchattenNorm P N (fun a => normalizedBlock (X a)
        (adaptedMean P (explicitRoundedGrid jStar m) (j + hn))) ≤
      Real.exp (logDetLoss P (explicitRoundedGrid jStar m) j (j + hn)) *
        lqSchattenNorm P N (fun a => normalizedBlock (X a)
          (adaptedMean P (explicitRoundedGrid jStar m) j)) := by
  have hAj := adaptedMean_posDef d hd P γ E Ψ K S hstat hdag jStar hjStar m hm j
  have hAk := adaptedMean_posDef d hd P γ E Ψ K S hstat hdag jStar hjStar m hm (j + hn)
  obtain ⟨_, _, _, hnorm, _, _⟩ := adaptedMean_order_consequences d hd P γ E Ψ K S
    hstat hdag jStar hjStar m hm j (j + hn) hj (by omega)
  have hnn : 0 ≤ lqSchattenNorm P N (fun a =>
      normalizedBlock (X a) (adaptedMean P (explicitRoundedGrid jStar m) j)) := by
    rw [(hX.lqSchattenNorm_eq_eLpNorm_toReal hN).2.2]
    exact ENNReal.toReal_nonneg
  calc
    _ ≤ ‖transportMatrix (adaptedMean P (explicitRoundedGrid jStar m) j)
        (adaptedMean P (explicitRoundedGrid jStar m) (j + hn))‖ ^ 2 *
        lqSchattenNorm P N (fun a => normalizedBlock (X a)
          (adaptedMean P (explicitRoundedGrid jStar m) j)) :=
      lqSchattenNorm_normalizedBlock_congr_le hN hAj hAk X hX
    _ ≤ _ := by
      rw [transportMatrix_sq_opNorm_eq P (explicitRoundedGrid jStar m) j hn hAj hAk]
      exact mul_le_mul_of_nonneg_right hnorm hnn


end

end Homogenization.HighContrast.Annealed
