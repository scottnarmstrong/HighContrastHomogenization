import HCPoly.Entry.Multiscale.ResponseInputs.AdaptedAlgebraComparison

/-!
# Decomposition of `adapted_response_core`, part 1: the predicate bundles and the
centred-energy estimate

The predicate bundles that carry the output of one step of the decomposition of
`adapted_response_core` into the hypotheses of the next, together with the centred-energy
estimate.
-/

open Homogenization.HighContrast (CoeffSpace aspectRatio blockScale matSqrt schurSigma)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

variable {d : ℕ}

/-! ## Bundles -/

/-- The calibrated-block sandwich `e.response.calibrated.blocks`
(`e.response.calibrated.blocks`):
`C^{-1} M_0 <= Ehat_t^± <= C kappa_t^{1/2} M_0` and `Ehat_s^± <= C kappa_s^{1/2} M_0`. -/
def RespCalibrated (C : ℝ) (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d)
    (s t : ℤ) : Prop :=
  BlockMatLoewnerLE (blockScale C⁻¹ (respM0 F)) (respEhatMinus P jStar F t) ∧
    BlockMatLoewnerLE (blockScale C⁻¹ (respM0 F)) (respEhatPlus P jStar F t) ∧
    BlockMatLoewnerLE (respEhatMinus P jStar F t)
      (blockScale (C * Real.sqrt (respKappa P jStar F t)) (respM0 F)) ∧
    BlockMatLoewnerLE (respEhatPlus P jStar F t)
      (blockScale (C * Real.sqrt (respKappa P jStar F t)) (respM0 F)) ∧
    BlockMatLoewnerLE (respEhatMinus P jStar F s)
      (blockScale (C * Real.sqrt (respKappa P jStar F s)) (respM0 F)) ∧
    BlockMatLoewnerLE (respEhatPlus P jStar F s)
      (blockScale (C * Real.sqrt (respKappa P jStar F s)) (respM0 F))

/-- The energy and defect bounds `e.response.energy.and.defect`
(`e.response.energy.and.defect`). -/
def RespEnergyDefect (C : ℝ) (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d)
    (s t : ℤ) (e : Vec d) : Prop :=
  0 ≤ respEJMinus P jStar F t e ∧ 0 ≤ respEJPlus P jStar F t e ∧
    respEJMinus P jStar F t e = (1 / 2 : ℝ) * respLsqMinus P jStar F t e - 1 ∧
    respEJPlus P jStar F t e = (1 / 2 : ℝ) * respLsqPlus P jStar F t e - 1 ∧
    respEJMinus P jStar F t e ≤ C * Real.sqrt (respKappa P jStar F s) ∧
    respEJPlus P jStar F t e ≤ C * Real.sqrt (respKappa P jStar F s) ∧
    0 ≤ respTauMinus P jStar F s t e ∧ 0 ≤ respTauPlus P jStar F s t e ∧
    respTauMinus P jStar F s t e ≤
      C * (respRatio P jStar F s t - 1) * Real.sqrt (respKappa P jStar F s) ∧
    respTauPlus P jStar F s t e ≤
      C * (respRatio P jStar F s t - 1) * Real.sqrt (respKappa P jStar F s)

/-- The load and mean bounds `e.response.load.and.mean`:
`|M_0^{1/2}x^±|^2 <= C kappa_s^{1/2}` and `|M_0^{1/2}Y^±|^2 <= C kappa_s`. -/
def RespLoadMean (C : ℝ) (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d)
    (s t : ℤ) (e : Vec d) : Prop :=
  blockVecDot (blockMatVecMul (blockSqrt (respM0 F)) (respxMinus P jStar F t e))
      (blockMatVecMul (blockSqrt (respM0 F)) (respxMinus P jStar F t e)) ≤
    C * Real.sqrt (respKappa P jStar F s) ∧
  blockVecDot (blockMatVecMul (blockSqrt (respM0 F)) (respxPlus P jStar F t e))
      (blockMatVecMul (blockSqrt (respM0 F)) (respxPlus P jStar F t e)) ≤
    C * Real.sqrt (respKappa P jStar F s) ∧
  blockVecDot (blockMatVecMul (blockSqrt (respM0 F)) (respYMinus P jStar F t e))
      (blockMatVecMul (blockSqrt (respM0 F)) (respYMinus P jStar F t e)) ≤
    C * respKappa P jStar F s ∧
  blockVecDot (blockMatVecMul (blockSqrt (respM0 F)) (respYPlus P jStar F t e))
      (blockMatVecMul (blockSqrt (respM0 F)) (respYPlus P jStar F t e)) ≤
    C * respKappa P jStar F s

/-- The source-smallness pair `e.response.source.smallness`
(`e.response.source.smallness`), with `Pi = aspectRatio E` and
`e(m)^2 = ‖m‖ ‖m⁻¹‖` for `m = explicitCanonicalMetric F`. -/
def RespSourceSmall (d : ℕ) (γ C η : ℝ) (E F : BlockMat d) (jStar : ℕ) (s t : ℤ) : Prop :=
  C * aspectRatio E * (‖explicitCanonicalMetric F‖ * ‖(explicitCanonicalMetric F)⁻¹‖) *
        (3 : ℝ) ^ (-(rhoMax d γ * ((t : ℝ) - (jStar : ℝ)))) ≤ η ^ ((1 : ℝ) / (bigQ d γ : ℝ)) ∧
    C * aspectRatio E * (‖explicitCanonicalMetric F‖ * ‖(explicitCanonicalMetric F)⁻¹‖) *
        (3 : ℝ) ^ (-((3 : ℝ) / 2 * ((s : ℝ) - (jStar : ℝ)))) ≤ 1

/-- The generation-`n` summand of the source load `L_s` (`p.response.transfer`): the
printed weight `3^{-3n/2}` times the flat average over the generation-`(s-n)` cells of
`(|b_{s-n,z}^{1/2} P| + |(S_{*,s-n,z})^{-1/2} Q|)^2`.  `respSourceLoad` is the sum of this family
over `n`. -/
noncomputable def respSourceLoadSummand (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d) (s : ℤ)
    (b : CoeffSpace d → CoeffField d) (Y : BlockVec d) (n : ℕ) : ℝ :=
  (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) *
    ((((triadicIndexBox d n).card : ℝ))⁻¹ *
      ∑ z ∈ triadicIndexBox d n,
        (Real.sqrt (vecDot Y.1 (matVecMul
              (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) z) b).upperLeft
              Y.1)) +
          Real.sqrt (vecDot Y.2 (matVecMul
              (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) z) b).lowerRight
              Y.2))) ^ 2)

/-- The source load is the sum of its generation summands. -/
theorem respSourceLoad_eq_tsum_summand (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d)
    (s : ℤ) (b : CoeffSpace d → CoeffField d) (Y : BlockVec d) :
    respSourceLoad P jStar F s b Y = ∑' n : ℕ, respSourceLoadSummand P jStar F s b Y n := rfl

/-- The source-load bound `L_s^± <= C kappa_s^{3/2}` (`p.response.transfer`).
-- READING: `kappa_s^{3/2}` is written `(sqrt kappa_s)^3`.

The two summability conjuncts are not decoration.  `respSourceLoad` is a `tsum`, whose value on a
non-summable family is `0`, and the two inequalities above then hold vacuously; the estimate of
`e.response.cutoff.estimate` divides by `L_s^±` in the sense that it pairs against it, and is false
at the junk value.  The printed proof of the bound establishes convergence on the way ("the series
converges because `gamma < 3/2`"), so the summability belongs here, where `L_s^±` is produced. -/
def RespLoadBound (C : ℝ) (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d)
    (s t : ℤ) (e : Vec d) : Prop :=
  0 ≤ respLsMinus P jStar F s t e ∧ 0 ≤ respLsPlus P jStar F s t e ∧
    respLsMinus P jStar F s t e ≤ C * Real.sqrt (respKappa P jStar F s) ^ 3 ∧
    respLsPlus P jStar F s t e ≤ C * Real.sqrt (respKappa P jStar F s) ^ 3 ∧
    Summable (respSourceLoadSummand P jStar F s (respCoeffMinus F) (respYMinus P jStar F t e)) ∧
    Summable (respSourceLoadSummand P jStar F s (respCoeffPlus F) (respYPlus P jStar F t e))

/-- The weak-norm estimate `e.response.weak.estimate`:
`(W^±)^{1/2} <= C (3^{-alpha H} + C_H eta^{1/(2Q)}) kappa_s^{1/2}`. -/
def RespWeakBound (C : ℝ) (CH : ℕ → ℝ) (d : ℕ) (γ : ℝ) (P : Measure (CoeffSpace d)) (jStar : ℕ)
    (F : BlockMat d) (H : ℕ) (η : ℝ) (s t : ℤ) (e : Vec d) : Prop :=
  0 ≤ respWMinus P jStar F t e ∧ 0 ≤ respWPlus P jStar F t e ∧
    Real.sqrt (respWMinus P jStar F t e) ≤
      C * ((3 : ℝ) ^ (-(respAlpha γ * (H : ℝ))) +
        CH H * η ^ ((1 : ℝ) / (2 * (bigQ d γ : ℝ)))) * Real.sqrt (respKappa P jStar F s) ∧
    Real.sqrt (respWPlus P jStar F t e) ≤
      C * ((3 : ℝ) ^ (-(respAlpha γ * (H : ℝ))) +
        CH H * η ^ ((1 : ℝ) / (2 * (bigQ d γ : ℝ)))) * Real.sqrt (respKappa P jStar F s)

/-- The cutoff estimate `e.response.cutoff.estimate`. -/
def RespCutoffBound (C : ℝ) (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d) (H : ℕ)
    (s t : ℤ) (e : Vec d) : Prop :=
  |respCenteredJMinus P jStar F t e| ≤
      C * (respTauMinus P jStar F s t e +
        Real.sqrt (respTauMinus P jStar F s t e * respEJMinus P jStar F t e) +
        Real.sqrt (respTauMinus P jStar F s t e * respLsMinus P jStar F s t e) +
        (3 : ℝ) ^ (-(H : ℝ)) * (respEJMinus P jStar F t e +
          Real.sqrt (respEJMinus P jStar F t e * respLsMinus P jStar F s t e)) +
        respWMinus P jStar F t e) ∧
    |respCenteredJPlus P jStar F t e| ≤
      C * (respTauPlus P jStar F s t e +
        Real.sqrt (respTauPlus P jStar F s t e * respEJPlus P jStar F t e) +
        Real.sqrt (respTauPlus P jStar F s t e * respLsPlus P jStar F s t e) +
        (3 : ℝ) ^ (-(H : ℝ)) * (respEJPlus P jStar F t e +
          Real.sqrt (respEJPlus P jStar F t e * respLsPlus P jStar F s t e)) +
        respWPlus P jStar F t e)

/-! ## The centred-energy estimate -/

/-- The centred-energy estimate `e.response.by.centered.energies`:
`kappa_t - 1 <= 12 d sup_{|e|=1}(|Jtilde^-(e)| + |Jtilde^+(e)|)`, stated with an explicit
bound `M` instead of a supremum.

Route: the trace identity of `p.response.transfer`
(`response_by_centered_energies_aux_centered_sum` and
`response_by_centered_energies_aux_basis_trace`), both trace terms nonnegative (`p.response.transfer`,
`response_by_centered_energies_trace_rTrT_nonneg`), the passage from the trace estimate to the
Loewner estimate `b_t <= (1 + d M) S_*` (`response_by_centered_energies_loewner_of_trace`), and
then `e.matrix.block.comparison` (`e.matrix.block.comparison`) with `h = h_t`.

-- READING: the docstring of `Analysis.schurSigma_le_corrected`
together with `coupled_schur_le` as the in-tree form of `e.matrix.block.comparison`.  That is
not what those two prove: `coupled_schur_le` goes from an imbalance bound to a corrected-Schur
bound, i.e. the converse implication, and the only `6` in this direction is the
aspect-ratio six of `Analysis.refBlock_le_six_aspectRatio_smul_swapConj`.  The printed
`F <= (1+6(theta-1)) F^sharp` is therefore proved here from scratch, at `h = h_t`, as
`response_by_centered_energies_block_comparison`.

The printed `12 d` is `2 * 6 * d`: this proof gives `kappa_t - 1 <= 6 d M`, and `M >= 0`
supplies the remaining factor two. -/
theorem response_by_centered_energies (d : ℕ) (_hd : 2 ≤ d) (γ : ℝ)
    (_hγ : γ ∈ Set.Ico (0 : ℝ) 1) (S : SelectionData) (_hS : S.Selects d γ)
    (ε σ Cglob Cprof Csrc Bresp : ℝ) (H : ℕ) (P : Measure (CoeffSpace d)) (E : BlockMat d)
    (Ψ : ℝ → ℝ) (Kg : ℝ) (Src : CoeffSpace d → ℝ) (B : ℝ) (jStar : ℕ) (F : BlockMat d)
    (s t : ℤ)
    (_raw : RawOutput d γ S ε σ Cglob Cprof Csrc H Bresp P E Ψ Kg Src B jStar F s t)
    (M : ℝ)
    (_hM : ∀ e : Vec d, vecDot e e = 1 →
      |respCenteredJMinus P jStar F t e| + |respCenteredJPlus P jStar F t e| ≤ M) :
    respKappa P jStar F t - 1 ≤ 12 * (d : ℝ) * M := by
  have := _raw.prob
  let : NeZero d := ⟨by omega⟩
  have hm : (explicitCanonicalMetric F).PosDef := Geometry.explicitCanonicalMetric_posDef _raw.symm _raw.pos
  have hEt : (toFullBlockMat (respMean P jStar F t)).PosDef :=
    Annealed.adaptedMean_posDef d _hd P γ E Ψ Kg Src _raw.stat _raw.ell jStar _raw.hj
      (explicitCanonicalMetric F) hm t
  have hsT : IsSymmetricBlockMat (respMean P jStar F t) :=
    Annealed.isSymmetricBlockMat_annealedBlock P _
  have hbT : Book.Ch02.BlockPosDef (respMean P jStar F t) :=
    blockPosDef_of_toFullBlockMat_posDef _ hEt
  have hoT : BlockMatLoewnerLE (ofFullBlockMat (toFullBlockMat (blockSwap d) *
      (toFullBlockMat (respMean P jStar F t))⁻¹ * toFullBlockMat (blockSwap d)))
      (respMean P jStar F t) :=
    Analysis.adaptedMean_swapConj_le _hd P γ E Ψ Kg Src _raw.stat _raw.ell jStar _raw.hj
      (explicitCanonicalMetric F) hm t
  have hM0 : 0 ≤ M := by
    have i0 : Fin d := ⟨0, by omega⟩
    have he : vecDot (Pi.single i0 (1 : ℝ)) (Pi.single i0 (1 : ℝ)) = 1 := by
      simp [vecDot, Pi.single_apply]
    have h := _hM _ he
    linarith [abs_nonneg (respCenteredJMinus P jStar F t (Pi.single i0 (1 : ℝ))),
      abs_nonneg (respCenteredJPlus P jStar F t (Pi.single i0 (1 : ℝ)))]
  have hmpos : (respM (respMean P jStar F t)).PosDef := response_by_centered_energies_respM_posDef hsT hbT
  have hsum := response_by_centered_energies_aux_response_sum (respMean P jStar F t) hsT hbT
    (respCenteredJMinus P jStar F t) (respCenteredJPlus P jStar F t) (fun _ => rfl) M _hM
  have ht1 : ∑ i : Fin d, vecDot (respP (respMean P jStar F t) (Pi.single i 1))
      (matVecMul (schurSigma (respMean P jStar F t) * (respMean P jStar F t).lowerRight - 1)
        (respQ (respMean P jStar F t) (Pi.single i 1))) =
      Matrix.trace (schurSigma (respMean P jStar F t) *
        (respMean P jStar F t).lowerRight - 1) :=
    response_by_centered_energies_aux_basis_trace
      (m := respM (respMean P jStar F t)) hmpos _
  have ht2 : ∑ i : Fin d, vecDot (respP (respMean P jStar F t) (Pi.single i 1))
      (matVecMul (respSym (respMean P jStar F t) * (respMean P jStar F t).lowerRight *
        respSym (respMean P jStar F t) * (respMean P jStar F t).lowerRight)
        (respQ (respMean P jStar F t) (Pi.single i 1))) =
      Matrix.trace (respSym (respMean P jStar F t) * (respMean P jStar F t).lowerRight *
        respSym (respMean P jStar F t) * (respMean P jStar F t).lowerRight) :=
    response_by_centered_energies_aux_basis_trace
      (m := respM (respMean P jStar F t)) hmpos _
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ht1, ht2] at hsum
  have htr1 : Matrix.trace (schurSigma (respMean P jStar F t) *
      (respMean P jStar F t).lowerRight - 1) =
      Matrix.trace (schurSigma (respMean P jStar F t) *
        (respMean P jStar F t).lowerRight) - (d : ℝ) := by
    rw [Matrix.trace_sub, Matrix.trace_one, Fintype.card_fin]
  have hnn := response_by_centered_energies_trace_rTrT_nonneg hsT hbT
  have hconj := response_by_centered_energies_trace_conj hsT hbT
  have hc : Matrix.trace (matSqrt (respMean P jStar F t).lowerRight *
      respBlockB (respMean P jStar F t) *
      matSqrt (respMean P jStar F t).lowerRight) - (d : ℝ) ≤ (d : ℝ) * M := by
    rw [hconj]
    rw [htr1] at hsum
    linarith
  have hL := response_by_centered_energies_loewner_of_trace hsT hbT hoT hc
  have hθ : (1 : ℝ) ≤ 1 + (d : ℝ) * M := by
    have := mul_nonneg (Nat.cast_nonneg (α := ℝ) d) hM0
    linarith
  have hcmp := response_by_centered_energies_block_comparison hsT hbT hoT hθ hL
  have hκ : respKappa P jStar F t ≤ 1 + 6 * ((1 + (d : ℝ) * M) - 1) := hcmp
  have hdM : 0 ≤ (d : ℝ) * M := mul_nonneg (Nat.cast_nonneg (α := ℝ) d) hM0
  linarith

end Homogenization.HighContrast.Multiscale
