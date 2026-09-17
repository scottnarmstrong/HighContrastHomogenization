import HCPoly.Entry.Multiscale.ResponseInputs.AdaptedWeakRouteH65a

open Homogenization.HighContrast (CoeffSpace adaptedCellCenter blockScale blockSub coarseBlock
  matSqrt normalizedBlock toFullBlockMat_eq_blockMatEntry)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ}

/-! Block E: **step (ii)** -- the depth-`0` extraction. -/

/-- `A ≤ c I` gives `A - I ≤ c I` (the subtracted identity is positive semidefinite). -/
private theorem b130_sub_identity_le (A : BlockMat d) (c : ℝ)
    (h : BlockMatLoewnerLE A (blockScale c (Book.Ch02.blockIdentity d))) :
    BlockMatLoewnerLE (blockSub A (Book.Ch02.blockIdentity d))
      (blockScale c (Book.Ch02.blockIdentity d)) := by
  intro X
  have hid := b130_qform_identity X
  have hq0 : (0 : ℝ) ≤ toFullBlockVec X ⬝ᵥ toFullBlockVec X := b130_dotProduct_self_nonneg _
  have hfull : toFullBlockMat A =
      toFullBlockMat (blockSub A (Book.Ch02.blockIdentity d)) +
        toFullBlockMat (Book.Ch02.blockIdentity d) := by
    rw [b130_toFullBlockMat_blockSub, sub_add_cancel]
  have hsplit := b130_qform_add_of_full A (blockSub A (Book.Ch02.blockIdentity d))
    (Book.Ch02.blockIdentity d) hfull X
  have hA := h X
  rw [b130_qform_blockScale, hid] at hA
  rw [b130_qform_blockScale, hid]
  rw [hid] at hsplit
  linarith

/-- **step (ii).**  `A_t(a) ≤ (1 + M(a)) E_t` for `P`-a.e. `a`.  The `sSup`
defining `M` is over a set that is a.e. bounded above by Block D, so `le_csSup` applies and the
junk value `0` is excluded. -/
private theorem b130_coarseBlock_le_one_add_respAllScaleMax (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (E : BlockMat d) (Ψ : ℝ → ℝ) (Kg : ℝ) (Src : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ Kg Src)
    (jStar : ℕ) (hj : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ) :
    ∀ᵐ a ∂P, BlockMatLoewnerLE (coarseBlock (respCell jStar F t) a)
      (blockScale (1 + respAllScaleMax P γ jStar F t a) (respMean P jStar F t)) := by
  let : NeZero d := ⟨by omega⟩
  have hEt : (toFullBlockMat (respMean P jStar F t)).PosDef :=
    Annealed.adaptedMean_posDef d hd P γ E Ψ Kg Src hstat hdag jStar hj (explicitCanonicalMetric F) hm t
  filter_upwards [b130_pathwise_envelope hd γ hγ P E Ψ Kg Src hstat hdag jStar hj F hm t]
    with a ha
  obtain ⟨C, hC0, hL0, hterms⟩ := ha
  -- (a) the defining set of `respAllScaleMax` is bounded above by `C`
  have hbdd : BddAbove {y : ℝ | ∃ n : ℕ, ∃ z ∈ triadicIndexBox d n, y =
      (3 : ℝ) ^ (-(respRho γ * (n : ℝ))) *
        blockSpecBound (blockSub
          (normalizedBlock (coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z) a)
            (respMean P jStar F t)) (Book.Ch02.blockIdentity d))} := by
    refine ⟨C, ?_⟩
    rintro y ⟨n, z, hz, rfl⟩
    exact hterms n z hz
  -- (b) the `n = 0`, `z = 0` member
  have hmem : blockSpecBound (blockSub
      (normalizedBlock (coarseBlock (respCell jStar F t) a) (respMean P jStar F t))
      (Book.Ch02.blockIdentity d)) ∈
      {y : ℝ | ∃ n : ℕ, ∃ z ∈ triadicIndexBox d n, y =
        (3 : ℝ) ^ (-(respRho γ * (n : ℝ))) *
          blockSpecBound (blockSub
            (normalizedBlock (coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z) a)
              (respMean P jStar F t)) (Book.Ch02.blockIdentity d))} := by
    refine ⟨0, 0, b130_zero_mem_triadicIndexBox 0, ?_⟩
    have h1 : t - ((0 : ℕ) : ℤ) = t := by simp
    have h2 : (3 : ℝ) ^ (-(respRho γ * ((0 : ℕ) : ℝ))) = 1 := by
      rw [Nat.cast_zero, mul_zero, neg_zero, Real.rpow_zero]
    rw [h1, b130_adaptedCellAtCenter_zero, h2, one_mul]
    rfl
  have hle : blockSpecBound (blockSub
      (normalizedBlock (coarseBlock (respCell jStar F t) a) (respMean P jStar F t))
      (Book.Ch02.blockIdentity d)) ≤ respAllScaleMax P γ jStar F t a :=
    le_csSup hbdd hmem
  -- (c) back from the spectral bound to the Loewner bound
  have hnorm : BlockMatLoewnerLE
      (normalizedBlock (coarseBlock (respCell jStar F t) a) (respMean P jStar F t))
      (blockScale C (Book.Ch02.blockIdentity d)) :=
    h5rc_normalizedBlock_le_scale _ _ hEt _ hL0
  have hwit := b130_sub_identity_le _ C hnorm
  have hfin := b130_le_one_add_specBound _ C _ hC0 hwit hle
  exact b130_le_scale_of_normalizedBlock_le hEt hfin

/-! Block F: the load normalization `p · q^∓ = 1`, transcribed from the sorry-free
`private` helpers of `AdaptedSwarm.lean`. -/

-- transcribed: AdaptedSwarm.lean (private)
private theorem b130_vecDot_add (x y z : Vec d) :
    vecDot x (y + z) = vecDot x y + vecDot x z := by
  simp [vecDot, mul_add, Finset.sum_add_distrib]

-- transcribed: AdaptedSwarm.lean (private)
private theorem b130_vecDot_skew_self (h : Mat d) (hh : matTranspose h = -h) (x : Vec d) :
    vecDot x (matVecMul h x) = 0 := by
  have hv : vecDot x (matVecMul h x) = x ⬝ᵥ h *ᵥ x := rfl
  have key : x ⬝ᵥ h *ᵥ x = -(x ⬝ᵥ h *ᵥ x) := by
    calc x ⬝ᵥ h *ᵥ x = x ᵥ* h ⬝ᵥ x := by rw [Matrix.dotProduct_mulVec]
      _ = hᵀ *ᵥ x ⬝ᵥ x := by rw [Matrix.mulVec_transpose]
      _ = (-h) *ᵥ x ⬝ᵥ x := by rw [show (hᵀ : Mat d) = -h from hh]
      _ = -(h *ᵥ x ⬝ᵥ x) := by rw [Matrix.neg_mulVec, neg_dotProduct]
      _ = -(x ⬝ᵥ h *ᵥ x) := by rw [dotProduct_comm]
  rw [hv]; linarith

-- transcribed: AdaptedSwarm.lean (private)
private theorem b130_vecDot_respP_respQ {A : BlockMat d} (hM : (respM A).PosDef) (e : Vec d) :
    vecDot (respP A e) (respQ A e) = vecDot e e := by
  have hherm : (matSqrt (respM A))ᵀ = matSqrt (respM A) := by
    have h := GeoMean.matSqrtHerm' hM.posSemidef
    rwa [GeoMean.conjTranspose_eq_transpose'] at h
  have hcancel : matSqrt (respM A) * matSqrt (respM A)⁻¹ = 1 := (GeoMean.sqrtCancel hM).1
  calc vecDot (respP A e) (respQ A e)
      = matSqrt (respM A)⁻¹ *ᵥ e ⬝ᵥ matSqrt (respM A) *ᵥ e := rfl
    _ = (matSqrt (respM A)⁻¹ *ᵥ e) ᵥ* matSqrt (respM A) ⬝ᵥ e := by
        rw [Matrix.dotProduct_mulVec]
    _ = (matSqrt (respM A))ᵀ *ᵥ (matSqrt (respM A)⁻¹ *ᵥ e) ⬝ᵥ e := by
        rw [Matrix.mulVec_transpose]
    _ = (matSqrt (respM A) * matSqrt (respM A)⁻¹) *ᵥ e ⬝ᵥ e := by
        rw [hherm, Matrix.mulVec_mulVec]
    _ = vecDot e e := by rw [hcancel, Matrix.one_mulVec]; rfl

-- transcribed: AdaptedSwarm.lean (private)
private theorem b130_respSkew_isSkew (A : BlockMat d) :
    matTranspose (respSkew A) = -(respSkew A) := by
  simp only [respSkew, matTranspose, Matrix.transpose_smul, Matrix.transpose_sub,
    Matrix.transpose_transpose]
  module

-- transcribed: AdaptedSwarm.lean (private)
private theorem b130_vecDot_respP_respqMinus (P : Measure (CoeffSpace d)) (jStar : ℕ)
    (F : BlockMat d) (t : ℤ) (e : Vec d) (he : vecDot e e = 1)
    (hM : (respM (respMean P jStar F t)).PosDef)
    (hg : matTranspose (respg F) = -(respg F)) :
    vecDot (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) = 1 := by
  have h2 := b130_respSkew_isSkew (respMean P jStar F t)
  have hskew : matTranspose (respg F - respSkew (respMean P jStar F t))
      = -(respg F - respSkew (respMean P jStar F t)) := by
    simp only [matTranspose, Matrix.transpose_sub] at hg h2 ⊢
    rw [hg, h2]; abel
  rw [respqMinus, b130_vecDot_add, b130_vecDot_respP_respQ hM, he,
    b130_vecDot_skew_self _ hskew, add_zero]

-- transcribed: AdaptedSwarm.lean (private)
private theorem b130_vecDot_respP_respqPlus (P : Measure (CoeffSpace d)) (jStar : ℕ)
    (F : BlockMat d) (t : ℤ) (e : Vec d) (he : vecDot e e = 1)
    (hM : (respM (respMean P jStar F t)).PosDef)
    (hg : matTranspose (respg F) = -(respg F)) :
    vecDot (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) = 1 := by
  have h2 := b130_respSkew_isSkew (respMean P jStar F t)
  have hskew : matTranspose (respSkew (respMean P jStar F t) - respg F)
      = -(respSkew (respMean P jStar F t) - respg F) := by
    simp only [matTranspose, Matrix.transpose_sub] at hg h2 ⊢
    rw [hg, h2]; abel
  rw [respqPlus, b130_vecDot_add, b130_vecDot_respP_respQ hM, he,
    b130_vecDot_skew_self _ hskew, add_zero]

-- transcribed: AdaptedSwarm.lean `blockPosDef_of_full` (private)
private theorem b130_blockPosDef_of_full {A : BlockMat d}
    (hA : (toFullBlockMat A).PosDef) : Book.Ch02.BlockPosDef A := by
  intro X hX
  have hfull_ne : toFullBlockVec X ≠ 0 := by
    intro hfull
    apply hX
    rw [← ofFullBlockVec_toFullBlockVec X, hfull]
    rfl
  have hq := hA.dotProduct_mulVec_pos hfull_ne
  rw [← dotProduct_toFullBlockVec X (blockMatVecMul A X), toFullBlockVec_blockMatVecMul]
  simpa only [star_trivial] using hq

/-- The pathwise optimizer energy is the quadratic form of the recentred coarse block,
`ℰ_t^2 = 2J_t = x^-·A^b_t(a)x^-` (paper `p.response.transfer`), and the depth-`0` term of
`M` gives the one-sided bound `A_t(a) ≤ (1 + M(a)) E_t` (`blockSpecBound`, congruence by
`respG` via `coarseBlockMatrix_sub_skew_eq_blockCongr`, `Ehat = blockCongr respG E_t`),
so `ℰ_t^2 ≤ (1 + M(a)) (L^-)^2`.  Only a.e. in `a`: the junk value `sSup = 0` of an unbounded set
must be excluded, and it is -- by `b130_coarseBlock_le_one_add_respAllScaleMax` below, whose
`BddAbove` comes from `Source.bounded_source_envelope`
(`HCPoly/Entry/Source/BoundedWindowFiniteness.lean`) applied to the bounded window `U_t`, fed by
`raw.stat` and `raw.ell`. -/
theorem weakOptimizerEnergy_sq_le_minus (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) (S : SelectionData) (hS : S.Selects d γ) :
    ∀ (ε σ Cglob Cprof Csrc Bresp : ℝ) (H : ℕ) (P : Measure (CoeffSpace d)) (E : BlockMat d)
      (Ψ : ℝ → ℝ) (Kg : ℝ) (Src : CoeffSpace d → ℝ) (B : ℝ) (jStar : ℕ) (F : BlockMat d)
      (s t : ℤ),
      RawOutput d γ S ε σ Cglob Cprof Csrc H Bresp P E Ψ Kg Src B jStar F s t →
      ∀ e : Vec d, vecDot e e = 1 →
        ∀ (u : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t)),
          (∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
            (respqMinus P jStar F t e) (respCoeffMinus F a) (u a)) →
          ∀ᵐ a ∂P, weakOptimizerEnergy (respCell jStar F t) (respCoeffMinus F a) (u a) ^ 2 ≤
            (1 + respAllScaleMax P γ jStar F t a) * respLsqMinus P jStar F t e := by
  have _hSUsed := hS
  let : NeZero d := ⟨by omega⟩
  intro _ε _σ _Cglob _Cprof _Csrc _Bresp _H P E Ψ Kg Src _B jStar F _s t raw e he u hu
  have := raw.prob
  have hm : (explicitCanonicalMetric F).PosDef := Geometry.explicitCanonicalMetric_posDef raw.symm raw.pos
  have hq : IsUnit (respGrid jStar F) := isUnit_respGrid_of_rawOutput raw
  have hEt : (toFullBlockMat (respMean P jStar F t)).PosDef :=
    Annealed.adaptedMean_posDef d hd P γ E Ψ Kg Src raw.stat raw.ell jStar raw.hj
      (explicitCanonicalMetric F) hm t
  have hM : (respM (respMean P jStar F t)).PosDef :=
    response_by_centered_energies_respM_posDef
      (Annealed.isSymmetricBlockMat_annealedBlock P _) (b130_blockPosDef_of_full hEt)
  have hpq : vecDot (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) = 1 :=
    b130_vecDot_respP_respqMinus P jStar F t e he hM (respg_isSkew F)
  filter_upwards [b130_coarseBlock_le_one_add_respAllScaleMax hd γ hγ P E Ψ Kg Src
    raw.stat raw.ell jStar raw.hj F hm t] with a hA
  -- step (i): the maximizer energy identity (already in the tree)
  have hi : weakOptimizerEnergy (respCell jStar F t) (respCoeffMinus F a) (u a) ^ 2 =
      blockVecDot (-respP (respMean P jStar F t) e, respqMinus P jStar F t e)
          (blockMatVecMul
            (coarseBlockMatrix (respCell jStar F t) (respCoeffMinus F a))
            (-respP (respMean P jStar F t) e, respqMinus P jStar F t e))
        - 2 * vecDot (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) :=
    weakOptimizerEnergy_sq_eq_blockQuadratic_respCoeffMinus (respGrid jStar F) hq t F a
      (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (u a) (hu a)
  -- step (iii): the congruence by `G`
  have hcongr : coarseBlockMatrix (respCell jStar F t) (respCoeffMinus F a)
      = blockCongr (respG F) (coarseBlock (respCell jStar F t) a) :=
    coarseBlockMatrix_sub_skew_eq_blockCongr (respg_isSkew F)
      (hasQuadraticMu_adaptedCell (respGrid jStar F) hq t a)
  -- step (iv): un-normalization, by evaluating the Loewner bound at `G x^-`
  set x : BlockVec d := respxMinus P jStar F t e with hx
  have hLo := hA (blockMatVecMul (respG F) x)
  rw [b130_qform_blockScale] at hLo
  have hLHS : blockVecDot x (blockMatVecMul
      (coarseBlockMatrix (respCell jStar F t) (respCoeffMinus F a)) x)
      = blockVecDot (blockMatVecMul (respG F) x)
          (blockMatVecMul (coarseBlock (respCell jStar F t) a)
            (blockMatVecMul (respG F) x)) := by
    rw [hcongr, blockVecDot_blockCongr]
  have hRHS : respLsqMinus P jStar F t e
      = blockVecDot (blockMatVecMul (respG F) x)
          (blockMatVecMul (respMean P jStar F t) (blockMatVecMul (respG F) x)) := by
    rw [respLsqMinus, ← hx, respEhatMinus, blockVecDot_blockCongr]
  rw [hi]
  rw [show ((-respP (respMean P jStar F t) e, respqMinus P jStar F t e) : BlockVec d) = x from rfl,
    hLHS, hpq]
  rw [hRHS]
  linarith [hLo]

/-- The `+` counterpart of the preceding estimate. -/
theorem weakOptimizerEnergy_sq_le_plus (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) (S : SelectionData) (hS : S.Selects d γ) :
    ∀ (ε σ Cglob Cprof Csrc Bresp : ℝ) (H : ℕ) (P : Measure (CoeffSpace d)) (E : BlockMat d)
      (Ψ : ℝ → ℝ) (Kg : ℝ) (Src : CoeffSpace d → ℝ) (B : ℝ) (jStar : ℕ) (F : BlockMat d)
      (s t : ℤ),
      RawOutput d γ S ε σ Cglob Cprof Csrc H Bresp P E Ψ Kg Src B jStar F s t →
      ∀ e : Vec d, vecDot e e = 1 →
        ∀ (u : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t)),
          (∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
            (respqPlus P jStar F t e) (respCoeffPlus F a) (u a)) →
          ∀ᵐ a ∂P, weakOptimizerEnergy (respCell jStar F t) (respCoeffPlus F a) (u a) ^ 2 ≤
            (1 + respAllScaleMax P γ jStar F t a) * respLsqPlus P jStar F t e := by
  have _hSUsed := hS
  let : NeZero d := ⟨by omega⟩
  intro _ε _σ _Cglob _Cprof _Csrc _Bresp _H P E Ψ Kg Src _B jStar F _s t raw e he u hu
  have := raw.prob
  have hm : (explicitCanonicalMetric F).PosDef := Geometry.explicitCanonicalMetric_posDef raw.symm raw.pos
  have hq : IsUnit (respGrid jStar F) := isUnit_respGrid_of_rawOutput raw
  have hEt : (toFullBlockMat (respMean P jStar F t)).PosDef :=
    Annealed.adaptedMean_posDef d hd P γ E Ψ Kg Src raw.stat raw.ell jStar raw.hj
      (explicitCanonicalMetric F) hm t
  have hM : (respM (respMean P jStar F t)).PosDef :=
    response_by_centered_energies_respM_posDef
      (Annealed.isSymmetricBlockMat_annealedBlock P _) (b130_blockPosDef_of_full hEt)
  have hpq : vecDot (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) = 1 :=
    b130_vecDot_respP_respqPlus P jStar F t e he hM (respg_isSkew F)
  have hgnskew : matTranspose (-(respg F)) = -(-(respg F)) := by
    have hT : matTranspose (-(respg F)) = -matTranspose (respg F) := by
      simp only [matTranspose, Matrix.transpose_neg]
    rw [hT, respg_isSkew F]
  filter_upwards [b130_coarseBlock_le_one_add_respAllScaleMax hd γ hγ P E Ψ Kg Src
    raw.stat raw.ell jStar raw.hj F hm t] with a hA
  have hi : weakOptimizerEnergy (respCell jStar F t) (respCoeffPlus F a) (u a) ^ 2 =
      blockVecDot (-respP (respMean P jStar F t) e, respqPlus P jStar F t e)
          (blockMatVecMul
            (coarseBlockMatrix (respCell jStar F t) (respCoeffPlus F a))
            (-respP (respMean P jStar F t) e, respqPlus P jStar F t e))
        - 2 * vecDot (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) :=
    weakOptimizerEnergy_sq_eq_blockQuadratic_respCoeffPlus (respGrid jStar F) hq t F a
      (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (u a) (hu a)
  -- the adjoint congruence, `G_+ = D ∘ (shear by -g) = (shear by g) ∘ D`
  set Gp : BlockMat d :=
    ofFullBlockMat (toFullBlockMat (respG F) * toFullBlockMat (blockD d)) with hGp
  have hcongr : coarseBlockMatrix (respCell jStar F t) (respCoeffPlus F a)
      = blockCongr Gp (coarseBlock (respCell jStar F t) a) := by
    have h1 : respCoeffPlus F a
        = fun y => (adjointCoeffField (⇑a.1 : CoeffField d)) y - (-(respg F)) := by
      funext y
      simp only [respCoeffPlus, adjointCoeffField, sub_neg_eq_add]
    have h2 := coarseBlockMatrix_sub_skew_eq_blockCongr (U := respCell jStar F t)
      (a := adjointCoeffField (⇑a.1 : CoeffField d)) hgnskew
      (hasQuadraticMu_adjointCoeffField
        (hasQuadraticMu_adaptedCell (respGrid jStar F) hq t a))
    have h3 : coarseBlockMatrix (respCell jStar F t) (adjointCoeffField (⇑a.1 : CoeffField d))
        = blockCongr (blockD d) (coarseBlock (respCell jStar F t) a) := by
      show coarseBlockMatrix (HighContrast.adaptedCell (respGrid jStar F) t)
          (adjointCoeffField (⇑a.1 : CoeffField d))
        = blockCongr (blockD d) (coarseBlock (HighContrast.adaptedCell (respGrid jStar F) t) a)
      rw [coarseBlockMatrix_adjointCoeffField_of_exists
        (exists_coarseBlockMatrix_of_hasQuadraticMu
          (hasQuadraticMu_adaptedCell (respGrid jStar F) hq t a)), ← blockCongr_blockD]
      rfl
    rw [h1, h2, h3, blockCongr_blockCongr, hGp]
    exact congrArg (fun M => blockCongr M (coarseBlock (respCell jStar F t) a))
      (congrArg ofFullBlockMat (blockD_mul_shear_neg (respg F)))
  set x : BlockVec d := respxPlus P jStar F t e with hx
  have hLo := hA (blockMatVecMul Gp x)
  rw [b130_qform_blockScale] at hLo
  have hLHS : blockVecDot x (blockMatVecMul
      (coarseBlockMatrix (respCell jStar F t) (respCoeffPlus F a)) x)
      = blockVecDot (blockMatVecMul Gp x)
          (blockMatVecMul (coarseBlock (respCell jStar F t) a) (blockMatVecMul Gp x)) := by
    rw [hcongr, blockVecDot_blockCongr]
  have hRHS : respLsqPlus P jStar F t e
      = blockVecDot (blockMatVecMul Gp x)
          (blockMatVecMul (respMean P jStar F t) (blockMatVecMul Gp x)) := by
    rw [respLsqPlus, ← hx, respEhatPlus, respEhatMinus, blockAdjoint, blockCongr_blockCongr,
      hGp, blockVecDot_blockCongr]
  rw [hi]
  rw [show ((-respP (respMean P jStar F t) e, respqPlus P jStar F t e) : BlockVec d) = x from rfl,
    hLHS, hpq]
  rw [hRHS]
  linarith [hLo]

/-- `0 ≤ M` (`Real.sSup_nonneg`: every member is `3^{-ρn} · blockSpecBound ≥ 0`,
`blockSpecBound` is an `sInf` of `{c | 0 ≤ c ∧ …}`, junk `0`). -/
theorem respAllScaleMax_nonneg (P : Measure (CoeffSpace d)) (γ : ℝ) (jStar : ℕ) (F : BlockMat d)
    (t : ℤ) (a : CoeffSpace d) : 0 ≤ respAllScaleMax P γ jStar F t a := by
  have hSpecBound_nonneg : ∀ Hb : BlockMat d, 0 ≤ blockSpecBound Hb :=
    fun Hb => Real.sInf_nonneg fun _ hx => hx.1
  refine Real.sSup_nonneg ?_
  rintro y ⟨n, z, _hz, rfl⟩
  exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) (hSpecBound_nonneg _)

/-- Pure real arithmetic of the split (`p.response.transfer`): on `{m > 1}`,
`m·(1+m) ≤ 2m^2 ≤ 2m^Q`; on `{m ≤ 1}`, `θ^2(1+m) ≤ 2θ^2`. -/
theorem energy_split_pointwise (m E L θ : ℝ) (Q : ℕ) (hQ : 2 ≤ Q) (hL : 0 ≤ L) (hm : 0 ≤ m)
    (hE : E ^ 2 ≤ (1 + m) * L) :
    ((if 1 < m then Real.sqrt m else θ) * E) ^ 2 ≤ 2 * L * (m ^ Q + θ ^ 2) := by
  have hmQnn : 0 ≤ m ^ Q := pow_nonneg hm Q
  by_cases hm1 : 1 < m
  · rw [if_pos hm1]
    have hmsq : Real.sqrt m ^ 2 = m := Real.sq_sqrt hm
    have hm2Q : m ^ 2 ≤ m ^ Q := pow_le_pow_right₀ hm1.le hQ
    have hm0 : (0:ℝ) < m := by linarith
    have hm1' : (0:ℝ) < m - 1 := by linarith
    have hmm2 : m ≤ m ^ 2 := by nlinarith [mul_pos hm0 hm1']
    have hstep : m * (1 + m) ≤ 2 * m ^ Q := by nlinarith [hmm2, hm2Q]
    calc (Real.sqrt m * E) ^ 2 = m * E ^ 2 := by rw [mul_pow, hmsq]
      _ ≤ m * ((1 + m) * L) := mul_le_mul_of_nonneg_left hE hm
      _ = (m * (1 + m)) * L := by ring
      _ ≤ (2 * m ^ Q) * L := mul_le_mul_of_nonneg_right hstep hL
      _ = 2 * L * m ^ Q := by ring
      _ ≤ 2 * L * (m ^ Q + θ ^ 2) := by nlinarith [mul_nonneg hL (sq_nonneg θ)]
  · rw [if_neg hm1]
    push Not at hm1
    calc (θ * E) ^ 2 = θ ^ 2 * E ^ 2 := by ring
      _ ≤ θ ^ 2 * ((1 + m) * L) := mul_le_mul_of_nonneg_left hE (sq_nonneg θ)
      _ ≤ θ ^ 2 * (2 * L) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by linarith) hL) (sq_nonneg θ)
      _ = 2 * L * θ ^ 2 := by ring
      _ ≤ 2 * L * (m ^ Q + θ ^ 2) := by nlinarith [mul_nonneg hL hmQnn]

/-! ### Local helpers.

`M = respAllScaleMax` is the supremum of the countable family indexed by the depth `n : ℕ`
and the finite index box `triadicIndexBox d n` (`AdaptedDefs.lean`), so its
measurability reduces, through `Measurable.sSup`
(`Mathlib/MeasureTheory/Constructions/BorelSpace/Order.lean`), to the measurability of one
member.  One member is `blockSpecBound` of the recentred normalized coarse block, and the two
ingredients are:

* `blockSpecBound` (`AdaptedDefs.lean`) is `ell^1`-Lipschitz in the flattened entries of its
  argument.  Its defining set `{c | 0 ≤ c ∧ H ≤ c I}` is closed (an intersection of half-lines,
  one per test vector), nonempty (the crude entrywise bound `h67_quad_le_entryAbsSum`) and
  bounded below, so `IsClosed.csInf_mem` makes the infimum ATTAINED — that is what upgrades the
  one-sided `blockSpecBound_le_of_loewner` of `AdaptedSwarm.lean` to the Lipschitz estimate
  `h67_blockSpecBound_le_add`, hence to continuity, hence to measurability.  No positive
  semidefiniteness and no symmetry of the argument is needed, which is what makes this usable on
  the RECENTRED block `normalizedBlock A E - I` (the mine's route through the operator norm,
  `HCPoly/Provider/Window/ScaleMeasurability.lean` `measurable_blockSize_coarseBlock` via
  `PortableHistory.blockSize_eq_norm`, is only available on positive blocks).
* the entries of `a ↦ coarseBlock (adaptedCellAtCenter q j w) a` are measurable, by
  `Annealed.measurable_coarseBlock_entry_adapted` (`AdaptedLocality.lean`) pushed to the
  global sigma-field by `Annealed.coeffSigma_le_global`; `normalizedBlock` is then a fixed
  bilinear expression in them.

MINE (rule 9): the old development proves the same shape for the POSITIVE carriers `blockSize`
/ `blockExcess` — `HCPoly/Provider/Window/ScaleMeasurability.lean`,
`HCPoly/Provider/Response/ProfileMaximumLp.lean` (`aemeasurable_blockSize_adaptedResponse`,
`aemeasurable_profileSourceMaximum`, the countable `AEMeasurable.iSup` over `(k, w)`) — and has
no counterpart for the one-sided `blockSpecBound` of a recentred (indefinite) block, which is why
the Lipschitz route below is written out here rather than transcribed. -/

/-- The quadratic form of a doubled block in the flattened coordinates. -/
private theorem h67_quad_expand (N : BlockMat d) (X : BlockVec d) :
    blockVecDot X (blockMatVecMul N X) =
      ∑ α : BlockCoord d, ∑ β : BlockCoord d,
        toFullBlockMat N α β * (toFullBlockVec X α * toFullBlockVec X β) := by
  rw [← dotProduct_toFullBlockVec, toFullBlockVec_blockMatVecMul]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => by ring

private theorem h67_quad_self (X : BlockVec d) :
    blockVecDot X X = ∑ α : BlockCoord d, toFullBlockVec X α * toFullBlockVec X α := by
  rw [← dotProduct_toFullBlockVec]
  simp only [dotProduct]

/-- The `ell^1` size of the flattened entries of a doubled block. -/
private def h67_entryAbsSum (N : BlockMat d) : ℝ :=
  ∑ α : BlockCoord d, ∑ β : BlockCoord d, |toFullBlockMat N α β|

private theorem h67_entryAbsSum_nonneg (N : BlockMat d) : 0 ≤ h67_entryAbsSum N :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem h67_toFullBlockMat_blockSub (A B : BlockMat d) (α β : BlockCoord d) :
    toFullBlockMat (blockSub A B) α β = toFullBlockMat A α β - toFullBlockMat B α β := by
  cases α <;> cases β <;> simp [toFullBlockMat, blockSub]

/-- The crude quadratic-form bound: the quadratic form of a doubled block is dominated by
the `ell^1` size of its entries times the squared length of the vector. -/
private theorem h67_quad_le_entryAbsSum (N : BlockMat d) (X : BlockVec d) :
    blockVecDot X (blockMatVecMul N X) ≤ h67_entryAbsSum N * blockVecDot X X := by
  have hS0 : 0 ≤ blockVecDot X X := by
    rw [h67_quad_self]
    exact Finset.sum_nonneg fun α _ => mul_self_nonneg _
  have hcoord : ∀ α : BlockCoord d,
      toFullBlockVec X α * toFullBlockVec X α ≤ blockVecDot X X := by
    intro α
    rw [h67_quad_self]
    exact Finset.single_le_sum (f := fun β : BlockCoord d =>
      toFullBlockVec X β * toFullBlockVec X β)
      (fun β _ => mul_self_nonneg _) (Finset.mem_univ α)
  have hterm : ∀ α β : BlockCoord d,
      toFullBlockMat N α β * (toFullBlockVec X α * toFullBlockVec X β) ≤
        |toFullBlockMat N α β| * blockVecDot X X := by
    intro α β
    have h1 : toFullBlockMat N α β * (toFullBlockVec X α * toFullBlockVec X β) ≤
        |toFullBlockMat N α β| * |toFullBlockVec X α * toFullBlockVec X β| :=
      le_trans (le_abs_self _) (by rw [abs_mul])
    have h2 : |toFullBlockVec X α * toFullBlockVec X β| ≤ blockVecDot X X := by
      rw [abs_mul]
      have hab : 2 * (|toFullBlockVec X α| * |toFullBlockVec X β|) ≤
          toFullBlockVec X α * toFullBlockVec X α +
            toFullBlockVec X β * toFullBlockVec X β := by
        nlinarith [sq_nonneg (|toFullBlockVec X α| - |toFullBlockVec X β|),
          abs_mul_abs_self (toFullBlockVec X α), abs_mul_abs_self (toFullBlockVec X β)]
      nlinarith [hcoord α, hcoord β, abs_nonneg (toFullBlockVec X α),
        abs_nonneg (toFullBlockVec X β)]
    exact h1.trans (mul_le_mul_of_nonneg_left h2 (abs_nonneg _))
  calc blockVecDot X (blockMatVecMul N X)
      = ∑ α : BlockCoord d, ∑ β : BlockCoord d,
          toFullBlockMat N α β * (toFullBlockVec X α * toFullBlockVec X β) :=
        h67_quad_expand N X
    _ ≤ ∑ α : BlockCoord d, ∑ β : BlockCoord d,
          |toFullBlockMat N α β| * blockVecDot X X :=
        Finset.sum_le_sum fun α _ => Finset.sum_le_sum fun β _ => hterm α β
    _ = h67_entryAbsSum N * blockVecDot X X := by
        rw [h67_entryAbsSum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun α _ => (Finset.sum_mul _ _ _).symm

private theorem h67_quad_scale_identity (c : ℝ) (X : BlockVec d) :
    blockVecDot X (blockMatVecMul (blockScale c (Book.Ch02.blockIdentity d)) X) =
      c * blockVecDot X X := by
  simp [blockScale, Book.Ch02.blockIdentity, Book.Ch02.blockDiag, blockMatVecMul, blockVecDot,
    matVecMul, vecDot, Matrix.one_apply, Finset.mul_sum, mul_add]
  refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun i _ => by ring)
    (Finset.sum_congr rfl fun i _ => by ring)

private theorem h67_loewner_iff (N : BlockMat d) (c : ℝ) :
    BlockMatLoewnerLE N (blockScale c (Book.Ch02.blockIdentity d)) ↔
      ∀ X : BlockVec d, blockVecDot X (blockMatVecMul N X) ≤ c * blockVecDot X X := by
  constructor
  · intro h X
    have := h X
    rw [h67_quad_scale_identity] at this
    linarith
  · intro h X
    rw [h67_quad_scale_identity]
    linarith [h X]

/-- The defining set of `blockSpecBound` is closed, nonempty and bounded below, so its
infimum is attained: `H ≤ |H_+| · I_{2d}`. -/
private theorem h67_blockSpecBound_mem (N : BlockMat d) :
    0 ≤ blockSpecBound N ∧
      BlockMatLoewnerLE N (blockScale (blockSpecBound N) (Book.Ch02.blockIdentity d)) := by
  set T : Set ℝ :=
    {c : ℝ | 0 ≤ c ∧ BlockMatLoewnerLE N (blockScale c (Book.Ch02.blockIdentity d))} with hT
  have hTeq : T = Set.Ici (0 : ℝ) ∩
      ⋂ X : BlockVec d,
        {c : ℝ | blockVecDot X (blockMatVecMul N X) ≤ c * blockVecDot X X} := by
    ext c
    simp only [hT, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_Ici, Set.mem_iInter,
      h67_loewner_iff]
  have hclosed : IsClosed T := by
    rw [hTeq]
    exact isClosed_Ici.inter (isClosed_iInter fun X =>
      isClosed_le continuous_const (continuous_id.mul continuous_const))
  have hne : T.Nonempty :=
    ⟨h67_entryAbsSum N, h67_entryAbsSum_nonneg N,
      (h67_loewner_iff N _).mpr fun X => h67_quad_le_entryAbsSum N X⟩
  have hbdd : BddBelow T := ⟨0, fun c hc => hc.1⟩
  exact hclosed.csInf_mem hne hbdd

private theorem h67_blockSpecBound_le (N : BlockMat d) {c : ℝ} (hc : 0 ≤ c)
    (h : BlockMatLoewnerLE N (blockScale c (Book.Ch02.blockIdentity d))) :
    blockSpecBound N ≤ c :=
  csInf_le ⟨0, fun _ hc' => hc'.1⟩ ⟨hc, h⟩

/-- `blockSpecBound` is `ell^1`-Lipschitz in the flattened entries. -/
private theorem h67_blockSpecBound_le_add (N N' : BlockMat d) :
    blockSpecBound N' ≤ blockSpecBound N + h67_entryAbsSum (blockSub N' N) := by
  obtain ⟨h0, hle⟩ := h67_blockSpecBound_mem N
  refine h67_blockSpecBound_le N' (by linarith [h67_entryAbsSum_nonneg (blockSub N' N)]) ?_
  refine (h67_loewner_iff N' _).mpr fun X => ?_
  have hN := (h67_loewner_iff N _).mp hle X
  have hD := h67_quad_le_entryAbsSum (blockSub N' N) X
  have hsplit : blockVecDot X (blockMatVecMul N' X) =
      blockVecDot X (blockMatVecMul N X) +
        blockVecDot X (blockMatVecMul (blockSub N' N) X) := by
    rw [h67_quad_expand, h67_quad_expand, h67_quad_expand, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun β _ => by
      rw [h67_toFullBlockMat_blockSub]; ring
  rw [hsplit]
  nlinarith [hN, hD]

/-- `blockSpecBound`, read on the flattened entries, is Lipschitz, hence continuous. -/
private theorem h67_continuous_blockSpecBound :
    Continuous fun e : BlockCoord d → BlockCoord d → ℝ =>
      blockSpecBound (ofFullBlockMat (Matrix.of e)) := by
  set K : NNReal := (Fintype.card (BlockCoord d) : NNReal) ^ 2 with hK
  refine (LipschitzWith.of_dist_le_mul (K := K) ?_).continuous
  intro e e'
  have habs : ∀ (f g : BlockCoord d → BlockCoord d → ℝ),
      h67_entryAbsSum (blockSub (ofFullBlockMat (Matrix.of f))
        (ofFullBlockMat (Matrix.of g))) ≤ (K : ℝ) * dist f g := by
    intro f g
    have hbound : ∀ α β : BlockCoord d, |f α β - g α β| ≤ dist f g := by
      intro α β
      have h1 : dist (f α β) (g α β) ≤ dist (f α) (g α) := dist_le_pi_dist (f α) (g α) β
      have h2 : dist (f α) (g α) ≤ dist f g := dist_le_pi_dist f g α
      rw [← Real.dist_eq]
      exact h1.trans h2
    have hstep : h67_entryAbsSum (blockSub (ofFullBlockMat (Matrix.of f))
        (ofFullBlockMat (Matrix.of g))) ≤
        ∑ _α : BlockCoord d, ∑ _β : BlockCoord d, dist f g := by
      refine Finset.sum_le_sum fun α _ => Finset.sum_le_sum fun β _ => ?_
      rw [h67_toFullBlockMat_blockSub]
      simpa using hbound α β
    refine hstep.trans_eq ?_
    simp [hK, Finset.sum_const, Finset.card_univ, sq, mul_assoc]
  have key : ∀ f g : BlockCoord d → BlockCoord d → ℝ,
      blockSpecBound (ofFullBlockMat (Matrix.of f)) ≤
        blockSpecBound (ofFullBlockMat (Matrix.of g)) + (K : ℝ) * dist f g := by
    intro f g
    linarith [h67_blockSpecBound_le_add (ofFullBlockMat (Matrix.of g))
      (ofFullBlockMat (Matrix.of f)), habs f g]
  have key2 := key e' e
  rw [dist_comm e' e] at key2
  rw [Real.dist_eq, abs_sub_le_iff]
  exact ⟨by linarith [key e e'], by linarith [key2]⟩

/-- Measurability of `blockSpecBound` along any entrywise measurable family of blocks. -/
private theorem h67_measurable_blockSpecBound {Ω : Type*} [MeasurableSpace Ω]
    (G : Ω → BlockMat d)
    (hG : ∀ α β : BlockCoord d, Measurable fun a => toFullBlockMat (G a) α β) :
    Measurable fun a => blockSpecBound (G a) := by
  have hrw : (fun a => blockSpecBound (G a)) =
      (fun e : BlockCoord d → BlockCoord d → ℝ =>
          blockSpecBound (ofFullBlockMat (Matrix.of e))) ∘
        fun a => fun α β => toFullBlockMat (G a) α β := by
    funext a
    simp only [Function.comp_apply]
    rw [show (Matrix.of fun α β => toFullBlockMat (G a) α β) = toFullBlockMat (G a) from rfl,
      ofFullBlockMat_toFullBlockMat]
  rw [hrw]
  exact h67_continuous_blockSpecBound.measurable.comp
    (measurable_pi_lambda _ fun α => measurable_pi_lambda _ fun β => hG α β)

/-- Every flattened entry of the coarse response on an aligned adapted cell is measurable for
the global coefficient sigma-field. -/
theorem h67_measurable_coarseBlock_entry [NeZero d] {q : Mat d} (hq : IsUnit q) (j : ℤ)
    (w : Fin d → ℤ) (α β : BlockCoord d) :
    Measurable fun a : CoeffSpace d =>
      toFullBlockMat (coarseBlock (adaptedCellAtCenter q j w) a) α β := by
  simpa only [toFullBlockMat_eq_blockMatEntry] using!
    (Annealed.measurable_coarseBlock_entry_adapted q hq j (adaptedCellCenter q j w)
      α β).mono (Annealed.coeffSigma_le_global _) le_rfl

/-- The normalized recentred block of the coarse response is entrywise measurable. -/
theorem h67_measurable_normalized_entry [NeZero d] {q : Mat d} (hq : IsUnit q) (j : ℤ)
    (w : Fin d → ℤ) (E : BlockMat d) (α β : BlockCoord d) :
    Measurable fun a : CoeffSpace d =>
      toFullBlockMat (blockSub
        (normalizedBlock (coarseBlock (adaptedCellAtCenter q j w) a) E)
        (Book.Ch02.blockIdentity d)) α β := by
  have hbase := h67_measurable_coarseBlock_entry hq j w
  have hnorm : Measurable fun a : CoeffSpace d =>
      toFullBlockMat (normalizedBlock (coarseBlock (adaptedCellAtCenter q j w) a) E) α β := by
    have hrw : (fun a : CoeffSpace d =>
        toFullBlockMat (normalizedBlock (coarseBlock (adaptedCellAtCenter q j w) a) E) α β) =
        fun a : CoeffSpace d => ∑ δ : BlockCoord d, (∑ ζ : BlockCoord d,
          matSqrt ((toFullBlockMat E)⁻¹) α ζ *
            toFullBlockMat (coarseBlock (adaptedCellAtCenter q j w) a) ζ δ) *
          matSqrt ((toFullBlockMat E)⁻¹) δ β := by
      funext a
      rw [normalizedBlock, toFullBlockMat_ofFullBlockMat, Matrix.mul_apply]
      exact Finset.sum_congr rfl fun δ _ => by rw [Matrix.mul_apply]
    rw [hrw]
    exact Finset.measurable_sum _ fun δ _ =>
      (Finset.measurable_sum _ fun ζ _ => (hbase ζ δ).const_mul _).mul_const _
  have hsub : (fun a : CoeffSpace d =>
      toFullBlockMat (blockSub
        (normalizedBlock (coarseBlock (adaptedCellAtCenter q j w) a) E)
        (Book.Ch02.blockIdentity d)) α β) =
      fun a : CoeffSpace d =>
        toFullBlockMat (normalizedBlock (coarseBlock (adaptedCellAtCenter q j w) a) E) α β -
          toFullBlockMat (Book.Ch02.blockIdentity d) α β := by
    funext a
    exact h67_toFullBlockMat_blockSub _ _ α β
  rw [hsub]
  exact hnorm.sub measurable_const

/-- **Measurability of `M`.**  `M` is the supremum of the countable family indexed
by the depth `n : ℕ` and the finite index box `triadicIndexBox d n`, each member measurable
through the coarse block of an aligned adapted cell. -/
theorem respAllScaleMax_measurable [NeZero d]
    (P : Measure (CoeffSpace d)) (γ : ℝ) (jStar : ℕ) (F : BlockMat d)
    (hq : IsUnit (respGrid jStar F)) (t : ℤ) :
    Measurable (respAllScaleMax P γ jStar F t) := by
  set g : ℕ × (Fin d → ℤ) → CoeffSpace d → ℝ := fun p a =>
    (3 : ℝ) ^ (-(respRho γ * (p.1 : ℝ))) *
      blockSpecBound (blockSub
        (normalizedBlock (coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (p.1 : ℤ)) p.2) a)
          (respMean P jStar F t)) (Book.Ch02.blockIdentity d)) with hg
  have hrw : respAllScaleMax P γ jStar F t =
      fun a => sSup ((fun p => g p a) ''
        {p : ℕ × (Fin d → ℤ) | p.2 ∈ triadicIndexBox d p.1}) := by
    funext a
    rw [respAllScaleMax]
    congr 1
    ext y
    constructor
    · rintro ⟨n, z, hz, rfl⟩
      exact ⟨(n, z), hz, rfl⟩
    · rintro ⟨⟨n, z⟩, hz, rfl⟩
      exact ⟨n, z, hz, rfl⟩
  rw [hrw]
  refine Measurable.sSup (Set.to_countable _) fun p _ => ?_
  exact (h67_measurable_blockSpecBound _ fun α β =>
    h67_measurable_normalized_entry hq _ _ _ α β).const_mul _



end

end Homogenization.HighContrast.Multiscale
