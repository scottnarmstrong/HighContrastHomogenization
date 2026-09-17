import HCPoly.Entry.Multiscale.ResponseInputs.AdaptedWeakRouteH65bMeasurable
import HCPoly.Entry.Multiscale.ResponseTransferHelpers

open Homogenization.HighContrast (CoeffSpace blockScale blockSub coarseBlock normalizedBlock)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

/-! ## The all-scale Loewner bound on every triadic subcell

`b130_coarseBlock_le_one_add_respAllScaleMax` bounds only the terminal cell of the response grid
by `(1 + respAllScaleMax) E_t`.  The all-scale maximum (`p.response.transfer`) is a
supremum over every depth, so the same Loewner bound holds on every triadic subcell, with the
depth-`n` weight `3 ^ (respRho γ * n)` made explicit: the weighted normalized recentred block of
the depth-`n` cell enters the defining set of the maximum, so the depth-`n` spectral bound is
`3 ^ (respRho γ * n) * respAllScaleMax`. -/

/-- Cauchy--Schwarz against the L2 operator norm: for any real square matrix `N` and real vector
`v`, the quadratic form `v ⬝ᵥ (N *ᵥ v)` is dominated by `‖N‖ * (v ⬝ᵥ v)`. -/
private theorem hc3_dot_mulVec_le_opNorm {n : Type*} [Fintype n] [DecidableEq n]
    (N : Matrix n n ℝ) (v : n → ℝ) : v ⬝ᵥ (N *ᵥ v) ≤ ‖N‖ * (v ⬝ᵥ v) := by
  have hsq := vecSq_mulVec_le N v
  have hvv : (0 : ℝ) ≤ v ⬝ᵥ v := b130_dotProduct_self_nonneg v
  rcases eq_or_lt_of_le (norm_nonneg N) with h0 | hpos
  · have hN : N = 0 := norm_eq_zero.mp h0.symm
    subst hN
    simp
  · have hexp : (0 : ℝ) ≤ (‖N‖ • v - N *ᵥ v) ⬝ᵥ (‖N‖ • v - N *ᵥ v) :=
      b130_dotProduct_self_nonneg _
    have hexpand : (‖N‖ • v - N *ᵥ v) ⬝ᵥ (‖N‖ • v - N *ᵥ v) =
        ‖N‖ * ‖N‖ * (v ⬝ᵥ v) - 2 * ‖N‖ * (v ⬝ᵥ (N *ᵥ v)) + (N *ᵥ v) ⬝ᵥ (N *ᵥ v) := by
      simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul,
        smul_eq_mul, dotProduct_comm (N *ᵥ v) v]
      ring
    rw [hexpand] at hexp
    nlinarith [hexp, hsq, hpos]

/-- The operator-norm Loewner envelope of an arbitrary doubled block: every doubled block is
dominated by its L2 operator norm times the doubled identity.  This is the nonemptiness witness
that reads the infimum defining `blockSpecBound` as a Loewner upper bound. -/
private theorem hc3_loewner_le_blockOpNorm {d : ℕ} (N : BlockMat d) :
    BlockMatLoewnerLE N (blockScale (blockOpNorm N) (Book.Ch02.blockIdentity d)) := by
  intro X
  have h := hc3_dot_mulVec_le_opNorm (toFullBlockMat N) (toFullBlockVec X)
  have hL : blockVecDot X (blockMatVecMul N X) =
      toFullBlockVec X ⬝ᵥ (toFullBlockMat N *ᵥ toFullBlockVec X) := by
    rw [← dotProduct_toFullBlockVec, toFullBlockVec_blockMatVecMul]
  have hR : blockVecDot X (blockMatVecMul (blockScale (blockOpNorm N)
      (Book.Ch02.blockIdentity d)) X) =
      blockOpNorm N * (toFullBlockVec X ⬝ᵥ toFullBlockVec X) := by
    rw [b130_qform_blockScale, b130_qform_identity]
  rw [hL, hR]
  unfold blockOpNorm at h ⊢
  linarith

/-- The all-scale Loewner bound on every triadic subcell (`p.response.transfer`):
for `P`-a.e. sample `a`, every depth-`n` cell of the response grid is Loewner-dominated by
`(1 + 3 ^ (respRho γ * n) * respAllScaleMax) · respMean`, with the depth weight explicit. -/
theorem coarseBlock_subcell_le_one_add_scaled_respAllScaleMax (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (E : BlockMat d) (Ψ : ℝ → ℝ) (Kg : ℝ) (Src : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ Kg Src)
    (jStar : ℕ) (hj : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ) :
    ∀ᵐ a ∂P, ∀ (n : ℕ), ∀ z ∈ triadicIndexBox d n,
      BlockMatLoewnerLE
        (coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z) a)
        (blockScale (1 + (3 : ℝ) ^ (respRho γ * (n : ℝ)) * respAllScaleMax P γ jStar F t a)
          (respMean P jStar F t)) := by
  let : NeZero d := ⟨by omega⟩
  have hEt : (toFullBlockMat (respMean P jStar F t)).PosDef :=
    Annealed.adaptedMean_posDef d hd P γ E Ψ Kg Src hstat hdag jStar hj (explicitCanonicalMetric F) hm t
  filter_upwards [b130_pathwise_envelope hd γ hγ P E Ψ Kg Src hstat hdag jStar hj F hm t]
    with a ha
  obtain ⟨C, _hC0, _hL0, hterms⟩ := ha
  intro n z hz
  -- the defining set of the all-scale maximum is bounded above by the envelope constant `C`
  have hbdd : BddAbove {y : ℝ | ∃ n : ℕ, ∃ z ∈ triadicIndexBox d n, y =
      (3 : ℝ) ^ (-(respRho γ * (n : ℝ))) *
        blockSpecBound (blockSub
          (normalizedBlock (coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z) a)
            (respMean P jStar F t)) (Book.Ch02.blockIdentity d))} := by
    refine ⟨C, ?_⟩
    rintro y ⟨m, w, hw, rfl⟩
    exact hterms m w hw
  -- the depth-`n`, cell-`z` weighted term is a member of that set
  have hmem : (3 : ℝ) ^ (-(respRho γ * (n : ℝ))) *
        blockSpecBound (blockSub
          (normalizedBlock (coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z) a)
            (respMean P jStar F t)) (Book.Ch02.blockIdentity d)) ∈
      {y : ℝ | ∃ n : ℕ, ∃ z ∈ triadicIndexBox d n, y =
        (3 : ℝ) ^ (-(respRho γ * (n : ℝ))) *
          blockSpecBound (blockSub
            (normalizedBlock (coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z) a)
              (respMean P jStar F t)) (Book.Ch02.blockIdentity d))} :=
    ⟨n, z, hz, rfl⟩
  have hle : (3 : ℝ) ^ (-(respRho γ * (n : ℝ))) *
        blockSpecBound (blockSub
          (normalizedBlock (coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z) a)
            (respMean P jStar F t)) (Book.Ch02.blockIdentity d)) ≤
      respAllScaleMax P γ jStar F t a :=
    le_csSup hbdd hmem
  -- multiply by the positive depth weight `3 ^ (respRho γ * n)`
  have hspec : blockSpecBound (blockSub
        (normalizedBlock (coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z) a)
          (respMean P jStar F t)) (Book.Ch02.blockIdentity d)) ≤
      (3 : ℝ) ^ (respRho γ * (n : ℝ)) * respAllScaleMax P γ jStar F t a := by
    have hpos : 0 < (3 : ℝ) ^ (respRho γ * (n : ℝ)) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have hcancel : (3 : ℝ) ^ (respRho γ * (n : ℝ)) *
        (3 : ℝ) ^ (-(respRho γ * (n : ℝ))) = 1 := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      have hexp : respRho γ * (n : ℝ) + -(respRho γ * (n : ℝ)) = 0 := by ring
      rw [hexp, Real.rpow_zero]
    calc blockSpecBound (blockSub
          (normalizedBlock (coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z) a)
            (respMean P jStar F t)) (Book.Ch02.blockIdentity d))
        = (3 : ℝ) ^ (respRho γ * (n : ℝ)) *
            ((3 : ℝ) ^ (-(respRho γ * (n : ℝ))) *
              blockSpecBound (blockSub
                (normalizedBlock
                  (coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z) a)
                  (respMean P jStar F t)) (Book.Ch02.blockIdentity d))) := by
          rw [← mul_assoc, hcancel, one_mul]
      _ ≤ (3 : ℝ) ^ (respRho γ * (n : ℝ)) * respAllScaleMax P γ jStar F t a :=
          mul_le_mul_of_nonneg_left hle hpos.le
  -- back to a Loewner bound, then un-normalize
  have hwit : BlockMatLoewnerLE (blockSub
        (normalizedBlock (coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z) a)
          (respMean P jStar F t)) (Book.Ch02.blockIdentity d))
      (blockScale (blockOpNorm (blockSub
        (normalizedBlock (coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z) a)
          (respMean P jStar F t)) (Book.Ch02.blockIdentity d)))
        (Book.Ch02.blockIdentity d)) :=
    hc3_loewner_le_blockOpNorm _
  have hfin : BlockMatLoewnerLE
      (normalizedBlock (coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z) a)
        (respMean P jStar F t))
      (blockScale (1 + (3 : ℝ) ^ (respRho γ * (n : ℝ)) * respAllScaleMax P γ jStar F t a)
        (Book.Ch02.blockIdentity d)) :=
    b130_le_one_add_specBound _ _ _ (norm_nonneg _) hwit hspec
  exact b130_le_scale_of_normalizedBlock_le hEt hfin

end

end Homogenization.HighContrast.Multiscale
