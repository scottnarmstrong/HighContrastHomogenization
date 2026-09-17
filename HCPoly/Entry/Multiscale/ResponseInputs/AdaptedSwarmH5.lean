import HCPoly.Entry.Multiscale.ResponseInputs.AdaptedSwarmH5Helpers

/-!
# AdaptedSwarm, part 8 of 11

Continuation of `HCPoly.Entry.Multiscale.ResponseInputs.AdaptedSwarm`, split at declaration boundaries so that
no module exceeds the 800-line isolation cap of
`scripts/check_isolation.py`.  Declaration statements, bodies and names
are unchanged; `private` is dropped only where a declaration is used from
a later part of the chain, since module privacy does not survive an import.
-/

open Homogenization.HighContrast (CoeffSpace adaptedCellCenter adaptedMean aspectRatio blockScale
  blockSub coarseBlock isSymmetricBlockMat_coarseBlockMatrix matSqrt normalizedBlock)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped ENNReal BigOperators
open scoped Matrix MatrixOrder

variable {d : ℕ}
/-! ## The two-sided response transfer estimate -/

/-! ## The two-sided carrier `respAllScaleAbs`

The ONE-SIDED all-scale maximum is `respAllScaleMax` (`AdaptedDefs.lean`).  The η-kernel twins
consume the TWO-SIDED `respAllScaleAbs` (`AdaptedDefs.lean`); `response_allscale_abs` below
discharges that premise.  The two-sided bound
has the one-sided bound's statement verbatim except for the carrier, so it is exactly the same
estimate with `respAllScaleAbs` in place of `respAllScaleMax`.

The route is the same one, two-sided at every step:

* the Step-5 split is the TRIANGLE INEQUALITY, not a Loewner comparison: `normalizedBlock` is
  linear in its first argument, so `N^q_{k,t}(z) - I = V^q_{k,t}(z) + (P^q_{k,t} - I)`
  (`h5abs_split_term_le`);
* the fluctuation summand `V^q_{k,t}(z)` is ALREADY carried by `blockOpNorm` in
  `fluctuationHistory` (`HCPoly/Entry/Setup/Histories.lean`), so `h5ra_scale_index_le` applies with
  no change at all;
* the mean summand `P^q_{k,t} - I` is positive semidefinite
  (`h5_normalizedBlock_gap_posSemidef` through `Annealed.adaptedMean_antitone`), and on a
  positive semidefinite block the spectral positive part IS the operator norm, so
  `h5_mean_part_le_determinantDrift` carries `blockOpNorm` on the left
  (`h5abs_mean_part_le_determinantDrift`);
* only the source branch `k < j_*` is genuinely one-sided.  There the lower side is free --
  `coarseBlock (adaptedCellAtCenter...) a >= 0`, hence `N^q_{k,t}(z) >= 0` and
  `N^q_{k,t}(z) - I >= -I` -- and costs the single extra summand `3^{-rho n} |I| <= 3^{-rho n}`.
  That branch runs only for `n > (t - j_*).toNat`, where
  `3^{-rho n} <= 3^{-rho_max (t - j_*)} <= eta^{1/Q} / C_s` by `RespSourceSmall`
  (`h5abs_source_term_le`), so the extra summand is `eta`-small -- which is exactly what the
  conclusion `<= C eta` needs.

No new analytic input is used.  The only positive
semidefiniteness invoked is `Annealed.blockPosDef_coarseBlock_adapted`
(`AdaptedDomainRecovery.lean`) at the aligned cell centre. -/

/-- `normalizedBlock` is additive in its first argument, flatly. -/
private theorem h5abs_full_normalizedBlock_sub (A B R : BlockMat d) :
    toFullBlockMat (normalizedBlock (blockSub A B) R) =
      toFullBlockMat (normalizedBlock A R) - toFullBlockMat (normalizedBlock B R) := by
  simp only [normalizedBlock, toFullBlockMat_ofFullBlockMat, h5_toFullBlockMat_blockSub,
    Matrix.mul_sub, Matrix.sub_mul]

/-- **The Step 5 split, two-sided** (`p.response.transfer`): since `normalizedBlock` is
linear in its first argument, the triangle inequality of the operator norm splits `N - I` into
the fluctuation part and the mean part with no Loewner comparison at all.  This is the
two-sided counterpart of `h5rc_split_term_le`. -/
private theorem h5abs_split_term_le (A Ak Et : BlockMat d) :
    blockOpNorm (blockSub (normalizedBlock A Et) (Book.Ch02.blockIdentity d)) ≤
      blockOpNorm (normalizedBlock (blockSub A Ak) Et) +
        blockOpNorm (blockSub (normalizedBlock Ak Et) (Book.Ch02.blockIdentity d)) := by
  have hsplit : toFullBlockMat (blockSub (normalizedBlock A Et) (Book.Ch02.blockIdentity d)) =
      toFullBlockMat (normalizedBlock (blockSub A Ak) Et) +
        toFullBlockMat (blockSub (normalizedBlock Ak Et) (Book.Ch02.blockIdentity d)) := by
    rw [h5_toFullBlockMat_blockSub, h5_toFullBlockMat_blockSub,
      h5abs_full_normalizedBlock_sub]
    abel
  show ‖toFullBlockMat (blockSub (normalizedBlock A Et) (Book.Ch02.blockIdentity d))‖ ≤ _
  rw [hsplit]
  exact norm_add_le _ _

/-- A normalized block of a positive semidefinite block is positive semidefinite. -/
private theorem h5abs_normalizedBlock_posSemidef {A R : BlockMat d}
    (hA : (toFullBlockMat A).PosSemidef) (hR : (toFullBlockMat R).PosDef) :
    (toFullBlockMat (normalizedBlock A R)).PosSemidef := by
  have hs : (matSqrt (toFullBlockMat R)⁻¹).IsHermitian :=
    (matSqrt_inv_posDef_full hR).isHermitian
  have hp := hA.conjTranspose_mul_mul_same (matSqrt (toFullBlockMat R)⁻¹)
  rw [hs.eq] at hp
  rw [normalizedBlock, toFullBlockMat_ofFullBlockMat]
  exact hp

/-- The coarse block of an ALIGNED adapted cell is positive semidefinite: `adaptedCellAtCenter q j w`
is `HighContrast.adaptedCellTranslate q j (adaptedCellCenter q j w)`, which is exactly what
`Annealed.blockPosDef_coarseBlock_adapted` (`AdaptedDomainRecovery.lean`) takes. -/
private theorem h5abs_coarseBlock_adaptedCellAtCenter_posSemidef [NeZero d] (q : Mat d)
    (hq : IsUnit q) (j : ℤ) (w : Fin d → ℤ) (a : CoeffSpace d) :
    (toFullBlockMat (coarseBlock (adaptedCellAtCenter q j w) a)).PosSemidef :=
  (Annealed.fullBlock_posDef_of_pos
    (isSymmetricBlockMat_coarseBlockMatrix (adaptedCellAtCenter q j w) (⇑a.1))
    (Annealed.blockPosDef_coarseBlock_adapted q hq j (adaptedCellCenter q j w) a)).posSemidef

/-- `‖I‖ ≤ 1` for the doubled identity in the `L²` operator norm; the `d = 0` case is the zero
space, where the norm is `0`. -/
private theorem h5abs_norm_one_le : ‖(1 : FullBlockMat d)‖ ≤ 1 := by
  rcases isEmpty_or_nonempty (BlockCoord d) with hi | hi
  · let := hi
    have he : (1 : FullBlockMat d) = 0 := Subsingleton.elim _ _
    rw [he, norm_zero]; norm_num
  · exact le_of_eq CStarRing.norm_one

/-- On a positive semidefinite block a Loewner bound `N ≼ c I` bounds the operator norm: the
converse of `h5rc_loewner_le_blockOpNorm`, and the only place positive semidefiniteness is
genuinely needed. -/
private theorem h5abs_blockOpNorm_le_of_loewner {N : BlockMat d}
    (hN : (toFullBlockMat N).PosSemidef) {c : ℝ} (hc : 0 ≤ c)
    (h : BlockMatLoewnerLE N (blockScale c (Book.Ch02.blockIdentity d))) :
    blockOpNorm N ≤ c := by
  show ‖toFullBlockMat N‖ ≤ c
  refine opNorm_le_of_psd_dot_le hN hc fun v => ?_
  have hX := h (ofFullBlockVec v)
  rw [h5rc_qform_blockScale] at hX
  have hid : blockVecDot (ofFullBlockVec v)
      (blockMatVecMul (Book.Ch02.blockIdentity d) (ofFullBlockVec v)) = v ⬝ᵥ v := by
    rw [← dotProduct_toFullBlockVec, toFullBlockVec_blockMatVecMul,
      h5rc_toFullBlockMat_blockIdentity, Matrix.one_mulVec, toFullBlockVec_ofFullBlockVec]
  have hL : blockVecDot (ofFullBlockVec v) (blockMatVecMul N (ofFullBlockVec v)) =
      v ⬝ᵥ (toFullBlockMat N *ᵥ v) := by
    rw [← dotProduct_toFullBlockVec, toFullBlockVec_blockMatVecMul,
      toFullBlockVec_ofFullBlockVec]
  rw [hid, hL] at hX
  linarith only [hX]

/-- On a positive semidefinite block the spectral positive part IS the operator norm; this is
the direction the mean part needs.  (The other direction is `h5rc_loewner_le_blockOpNorm`
through `blockSpecBound_le_of_loewner`, and holds for every block.) -/
private theorem h5abs_blockOpNorm_le_blockSpecBound (N : BlockMat d)
    (hN : (toFullBlockMat N).PosSemidef) : blockOpNorm N ≤ blockSpecBound N :=
  h5abs_blockOpNorm_le_of_loewner hN (blockSpecBound_nonneg N)
    (h5rc_blockSpecBound_attained N (blockOpNorm N) (norm_nonneg _)
      (h5rc_loewner_le_blockOpNorm N))

/-- **The source branch, two-sided**: from `0 ≼ N ≼ c I` the operator norm of `N - I` is at
most `c + 1`.  The lower Loewner side costs exactly `‖I‖ ≤ 1` and nothing else. -/
private theorem h5abs_blockOpNorm_sub_identity_le {N : BlockMat d}
    (hN : (toFullBlockMat N).PosSemidef) {c : ℝ} (hc : 0 ≤ c)
    (h : BlockMatLoewnerLE N (blockScale c (Book.Ch02.blockIdentity d))) :
    blockOpNorm (blockSub N (Book.Ch02.blockIdentity d)) ≤ c + 1 := by
  have h1 : ‖toFullBlockMat N‖ ≤ c := h5abs_blockOpNorm_le_of_loewner hN hc h
  have h2 : blockOpNorm (blockSub N (Book.Ch02.blockIdentity d)) ≤
      ‖toFullBlockMat N‖ + ‖(1 : FullBlockMat d)‖ := by
    show ‖toFullBlockMat (blockSub N (Book.Ch02.blockIdentity d))‖ ≤ _
    rw [h5_toFullBlockMat_blockSub, h5rc_toFullBlockMat_blockIdentity]
    exact norm_sub_le _ _
  have h3 := h5abs_norm_one_le (d := d)
  linarith

/-- **The mean part, two-sided** (`p.response.transfer`): `P^q_{k,t} - I` is
positive semidefinite, so `h5_mean_part_le_determinantDrift` holds verbatim with the full
operator norm in place of the spectral positive part. -/
private theorem h5abs_mean_part_le_determinantDrift (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (Src : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ K Src)
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (mt : Mat d) (hm : mt.PosDef)
    (k t : ℤ) (hk : (jStar : ℤ) ≤ k) (hkt : k ≤ t) :
    (3 : ℝ) ^ (-(respRho γ * ((t : ℝ) - (k : ℝ)))) *
        blockOpNorm (blockSub (normalizedMean P (Geometry.explicitRoundedGrid jStar mt) k t)
          (Book.Ch02.blockIdentity d))
      ≤ determinantDrift P γ (Geometry.explicitRoundedGrid jStar mt) jStar t := by
  have hpd : ∀ j : ℤ,
      (toFullBlockMat (adaptedMean P (Geometry.explicitRoundedGrid jStar mt) j)).PosDef := fun j =>
    Annealed.adaptedMean_posDef d hd P γ E Ψ K Src hstat hdag jStar hjStar mt hm j
  have hI : normalizedMean P (Geometry.explicitRoundedGrid jStar mt) t t =
      Book.Ch02.blockIdentity d :=
    Annealed.normalizedMean_self d hd P γ E Ψ K Src hstat hdag jStar hjStar mt hm t
  have hpsd : (toFullBlockMat (blockSub
      (normalizedMean P (Geometry.explicitRoundedGrid jStar mt) k t)
      (Book.Ch02.blockIdentity d))).PosSemidef := by
    rw [← hI]
    simpa only [normalizedMean] using
      h5_normalizedBlock_gap_posSemidef
        (adaptedMean P (Geometry.explicitRoundedGrid jStar mt) k)
        (adaptedMean P (Geometry.explicitRoundedGrid jStar mt) t)
        (adaptedMean P (Geometry.explicitRoundedGrid jStar mt) t) (hpd t)
        (hpd k).isHermitian (hpd t).isHermitian
        (Annealed.adaptedMean_antitone d hd P γ E Ψ K Src hstat hdag jStar hjStar mt hm k t
          hk hkt)
  refine le_trans (mul_le_mul_of_nonneg_left
    (h5abs_blockOpNorm_le_blockSpecBound _ hpsd)
    (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 3) _)) ?_
  exact h5_mean_part_le_determinantDrift d hd γ hγ P E Ψ K Src hstat hdag jStar hjStar mt hm
    k t hk hkt

/-- **The fluctuation-and-mean branch, two-sided** (`p.response.transfer`):
the two-sided counterpart of `h5rc_fluctuation_term_le`.  Both summands of the triangle split
are already two-sided -- the fluctuation part is `blockOpNorm` in `fluctuationHistory` itself,
and the mean part is positive semidefinite -- so this branch costs nothing extra at all. -/
theorem h5abs_fluctuation_term_le (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (E : BlockMat d) (Ψ : ℝ → ℝ) (Kg : ℝ) (Src : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ Kg Src)
    (jStar : ℕ) (hj : 2 * d ≤ 3 ^ jStar) (mt : Mat d) (hm : mt.PosDef)
    (t : ℤ) (ht : (jStar : ℤ) ≤ t) (a : CoeffSpace d) (n : ℕ)
    (hn : n ∈ Set.Icc 0 (t - (jStar : ℤ)).toNat) (z : Fin d → ℤ)
    (hz : z ∈ triadicIndexBox d n) :
    (3 : ℝ) ^ (-(respRho γ * (n : ℝ))) *
        blockOpNorm (blockSub (normalizedBlock (coarseBlock
          (adaptedCellAtCenter (Geometry.explicitRoundedGrid jStar mt) (t - (n : ℤ)) z) a)
          (adaptedMean P (Geometry.explicitRoundedGrid jStar mt) t)) (Book.Ch02.blockIdentity d)) ≤
      (⨆ j ∈ Set.Icc (jStar : ℤ) t,
        (3 : ℝ) ^ (-(bigQ d γ : ℝ) * rhoMax d γ * ((t : ℝ) - (j : ℝ))) *
          ⨆ y ∈ adaptedLatticeAtScale (Geometry.explicitRoundedGrid jStar mt) j ∩
              HighContrast.adaptedCell (Geometry.explicitRoundedGrid jStar mt) t,
            blockOpNorm (normalizedFluctuation P (Geometry.explicitRoundedGrid jStar mt) j t y a) ^
              bigQ d γ) ^ ((bigQ d γ : ℝ)⁻¹) +
        determinantDrift P γ (Geometry.explicitRoundedGrid jStar mt) jStar t := by
  have hQ0 : bigQ d γ ≠ 0 := by have := bigQ_two_le d hd γ hγ; omega
  obtain ⟨-, hn2⟩ := Set.mem_Icc.mp hn
  have hk1 : (jStar : ℤ) ≤ t - (n : ℤ) := by omega
  have hk2 : t - (n : ℤ) ≤ t := by omega
  have hwnn : (0 : ℝ) ≤ (3 : ℝ) ^ (-(respRho γ * (n : ℝ))) := Real.rpow_nonneg (by norm_num) _
  have hF00 : (0 : ℝ) ≤ ⨆ j ∈ Set.Icc (jStar : ℤ) t,
      (3 : ℝ) ^ (-(bigQ d γ : ℝ) * rhoMax d γ * ((t : ℝ) - (j : ℝ))) *
        ⨆ y ∈ adaptedLatticeAtScale (Geometry.explicitRoundedGrid jStar mt) j ∩
            HighContrast.adaptedCell (Geometry.explicitRoundedGrid jStar mt) t,
          blockOpNorm (normalizedFluctuation P (Geometry.explicitRoundedGrid jStar mt) j t y a) ^
            bigQ d γ :=
    Real.iSup_nonneg fun j => Real.iSup_nonneg fun _ =>
      mul_nonneg (Real.rpow_nonneg (by norm_num) _)
        (Real.iSup_nonneg fun y => Real.iSup_nonneg fun _ => pow_nonneg (norm_nonneg _) _)
  have hsplit := h5abs_split_term_le
    (coarseBlock (adaptedCellAtCenter (Geometry.explicitRoundedGrid jStar mt) (t - (n : ℤ)) z) a)
    (adaptedMean P (Geometry.explicitRoundedGrid jStar mt) (t - (n : ℤ)))
    (adaptedMean P (Geometry.explicitRoundedGrid jStar mt) t)
  have hmean := h5abs_mean_part_le_determinantDrift d hd γ hγ P E Ψ Kg Src hstat hdag
    jStar hj mt hm (t - (n : ℤ)) t hk1 hk2
  have hcast : (t : ℝ) - ((t - (n : ℤ) : ℤ) : ℝ) = (n : ℝ) := by push_cast; ring
  rw [hcast] at hmean
  simp only [normalizedMean] at hmean
  have hflc := h5ra_scale_index_le d hd γ hγ P E Ψ Kg Src hstat hdag jStar hj mt hm t ht
    a n hn z hz
  rw [h5rc_normalizedFluctuation_eq] at hflc
  have hfl : (3 : ℝ) ^ (-(respRho γ * (n : ℝ))) *
      blockOpNorm (normalizedBlock (blockSub (coarseBlock
        (adaptedCellAtCenter (Geometry.explicitRoundedGrid jStar mt) (t - (n : ℤ)) z) a)
        (adaptedMean P (Geometry.explicitRoundedGrid jStar mt) (t - (n : ℤ))))
        (adaptedMean P (Geometry.explicitRoundedGrid jStar mt) t)) ≤
      (⨆ j ∈ Set.Icc (jStar : ℤ) t,
        (3 : ℝ) ^ (-(bigQ d γ : ℝ) * rhoMax d γ * ((t : ℝ) - (j : ℝ))) *
          ⨆ y ∈ adaptedLatticeAtScale (Geometry.explicitRoundedGrid jStar mt) j ∩
              HighContrast.adaptedCell (Geometry.explicitRoundedGrid jStar mt) t,
            blockOpNorm (normalizedFluctuation P (Geometry.explicitRoundedGrid jStar mt) j t y a) ^
              bigQ d γ) ^ ((bigQ d γ : ℝ)⁻¹) := by
    refine h5rc_le_rpow_inv (bigQ d γ) hQ0 _ _ (mul_nonneg hwnn (norm_nonneg _)) hF00 ?_
    rw [h5rc_pow_weight]
    exact hflc
  refine le_trans (mul_le_mul_of_nonneg_left hsplit hwnn) ?_
  rw [mul_add]
  linarith [hfl, hmean]

/-- **The source branch, two-sided** (`p.response.transfer`): the two-sided
counterpart of `h5rc_source_term_le`.  The upper Loewner side is unchanged; the lower side is
`coarseBlock (adaptedCellAtCenter...) a >= 0` normalized by `E_t`, which costs the single extra
summand `3^{-rho n} |I| <= 3^{-rho n}`.  Because this branch runs only for
`n > (t - j_*).toNat`, `3^{-rho n} <= 3^{-rho_max (t - j_*)}` and `RespSourceSmall` makes that
at most `eta^{1/Q} / C_s` -- so the extra summand is `eta`-small, which is what the two-sided
conclusion needs. -/
theorem h5abs_source_term_le (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (E : BlockMat d) (Ψ : ℝ → ℝ) (Kg : ℝ) (Src : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ Kg Src)
    (jStar : ℕ) (hj : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ) (ht : (jStar : ℤ) ≤ t)
    (hcube : HighContrast.adaptedCell (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) t ⊆
      HighContrast.centeredCube d (2 * (jStar : ℤ)))
    (C₀ Cn Cs η : ℝ) (hC₀ : 0 < C₀) (hCn : 0 < Cn) (hCs : 0 < Cs)
    (X : CoeffSpace d → ℝ) (a : CoeffSpace d) (hXa : 0 < X a)
    (hpath : ∀ (mm : Mat d), mm.PosDef → ∀ (j : ℤ) (y : Vec d),
      HighContrast.adaptedCellTranslate (Geometry.explicitRoundedGrid jStar mm) j y ⊆
          HighContrast.centeredCube d (2 * (jStar : ℤ)) →
        BlockMatLoewnerLE (coarseBlock (HighContrast.adaptedCellTranslate
            (Geometry.explicitRoundedGrid jStar mm) j y) a)
          (blockScale (C₀ * Real.sqrt (‖mm‖ * ‖mm⁻¹‖) * X a *
            (3 : ℝ) ^ (γ * max ((jStar : ℝ) - (j : ℝ)) 0)) E))
    (hnormt : BlockMatLoewnerLE E (blockScale (Cn * aspectRatio E *
      Real.sqrt (‖explicitCanonicalMetric F‖ * ‖(explicitCanonicalMetric F)⁻¹‖))
      (adaptedMean P (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) t)))
    (hsrcsmall : Cs * aspectRatio E * (‖explicitCanonicalMetric F‖ * ‖(explicitCanonicalMetric F)⁻¹‖) *
      (3 : ℝ) ^ (-(rhoMax d γ * ((t : ℝ) - (jStar : ℝ)))) ≤
      η ^ ((1 : ℝ) / (bigQ d γ : ℝ)))
    (n : ℕ) (hn : (t - (jStar : ℤ)).toNat < n) (z : Fin d → ℤ)
    (hz : z ∈ triadicIndexBox d n) :
    (3 : ℝ) ^ (-(respRho γ * (n : ℝ))) *
        blockOpNorm (blockSub (normalizedBlock (coarseBlock
          (adaptedCellAtCenter (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) (t - (n : ℤ)) z) a)
          (adaptedMean P (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) t))
          (Book.Ch02.blockIdentity d)) ≤
      C₀ * Cn / Cs * η ^ ((1 : ℝ) / (bigQ d γ : ℝ)) * X a +
        η ^ ((1 : ℝ) / (bigQ d γ : ℝ)) / Cs := by
  let : NeZero d := ⟨by omega⟩
  have hwnn : (0 : ℝ) ≤ (3 : ℝ) ^ (-(respRho γ * (n : ℝ))) := Real.rpow_nonneg (by norm_num) _
  have hEt : (toFullBlockMat (adaptedMean P
      (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) t)).PosDef :=
    Annealed.adaptedMean_posDef d hd P γ E Ψ Kg Src hstat hdag jStar hj (explicitCanonicalMetric F) hm t
  have hee : (0 : ℝ) ≤ ‖explicitCanonicalMetric F‖ * ‖(explicitCanonicalMetric F)⁻¹‖ := by positivity
  have heesq : Real.sqrt (‖explicitCanonicalMetric F‖ * ‖(explicitCanonicalMetric F)⁻¹‖) *
      Real.sqrt (‖explicitCanonicalMetric F‖ * ‖(explicitCanonicalMetric F)⁻¹‖) =
      ‖explicitCanonicalMetric F‖ * ‖(explicitCanonicalMetric F)⁻¹‖ := Real.mul_self_sqrt hee
  have hsq0 : (0 : ℝ) ≤ Real.sqrt (‖explicitCanonicalMetric F‖ * ‖(explicitCanonicalMetric F)⁻¹‖) :=
    Real.sqrt_nonneg _
  have hPi : (0 : ℝ) < aspectRatio E := (Annealed.aspectRatio_pos_and_three_le hdag).1
  have hPi1 : (1 : ℝ) ≤ aspectRatio E := by
    linarith [(Annealed.aspectRatio_pos_and_three_le hdag).2]
  have hkap : (1 : ℝ) ≤ ‖explicitCanonicalMetric F‖ * ‖(explicitCanonicalMetric F)⁻¹‖ :=
    Geometry.one_le_norm_mul_norm_inv hm
  have hcell : HighContrast.adaptedCellTranslate
      (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) (t - (n : ℤ))
      (adaptedCellCenter (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F))
        (t - (n : ℤ)) z) ⊆ HighContrast.centeredCube d (2 * (jStar : ℤ)) := by
    rw [h5rc_adaptedCellTranslate_center]
    exact fun x hx => hcube (h5_adaptedCellAtCenter_subset_adaptedCell
      (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) t n hz hx)
  have hb := hpath (explicitCanonicalMetric F) hm (t - (n : ℤ))
    (adaptedCellCenter (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) (t - (n : ℤ)) z) hcell
  rw [h5rc_adaptedCellTranslate_center] at hb
  have hc1 : (0 : ℝ) ≤ C₀ * Real.sqrt (‖explicitCanonicalMetric F‖ * ‖(explicitCanonicalMetric F)⁻¹‖) *
      X a * (3 : ℝ) ^ (γ * max ((jStar : ℝ) - ((t - (n : ℤ) : ℤ) : ℝ)) 0) :=
    mul_nonneg (mul_nonneg (mul_nonneg hC₀.le hsq0) hXa.le)
      (Real.rpow_nonneg (by norm_num) _)
  have hc2 : (0 : ℝ) ≤ Cn * aspectRatio E *
      Real.sqrt (‖explicitCanonicalMetric F‖ * ‖(explicitCanonicalMetric F)⁻¹‖) :=
    mul_nonneg (mul_nonneg hCn.le hPi.le) hsq0
  -- the UPPER Loewner side: exactly the one-sided route of `h5rc_cell_specBound_le`
  have hup : BlockMatLoewnerLE
      (normalizedBlock (coarseBlock (adaptedCellAtCenter
        (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) (t - (n : ℤ)) z) a)
        (adaptedMean P (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) t))
      (blockScale ((C₀ * Real.sqrt (‖explicitCanonicalMetric F‖ * ‖(explicitCanonicalMetric F)⁻¹‖) * X a *
        (3 : ℝ) ^ (γ * max ((jStar : ℝ) - ((t - (n : ℤ) : ℤ) : ℝ)) 0)) *
        (Cn * aspectRatio E *
          Real.sqrt (‖explicitCanonicalMetric F‖ * ‖(explicitCanonicalMetric F)⁻¹‖)))
        (Book.Ch02.blockIdentity d)) :=
    h5rc_normalizedBlock_le_scale _ _ hEt _
      (hb.trans (h5rc_blockScale_mono E
        (adaptedMean P (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) t) _ _ hc1 hnormt))
  -- the LOWER side, free: the coarse block of an aligned cell is positive semidefinite
  have hpsd : (toFullBlockMat (normalizedBlock (coarseBlock (adaptedCellAtCenter
      (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) (t - (n : ℤ)) z) a)
      (adaptedMean P (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) t))).PosSemidef :=
    h5abs_normalizedBlock_posSemidef
      (h5abs_coarseBlock_adaptedCellAtCenter_posSemidef _
        (Geometry.isUnit_roundedGrid hj hm) (t - (n : ℤ)) z a) hEt
  have hopn := h5abs_blockOpNorm_sub_identity_le hpsd (mul_nonneg hc1 hc2) hup
  -- the weight comparison, verbatim from `h5rc_source_term_le`
  have hT0 : (0 : ℝ) ≤ (t : ℝ) - (jStar : ℝ) := by
    have h1 : ((jStar : ℤ) : ℝ) ≤ ((t : ℤ) : ℝ) := by exact_mod_cast ht
    push_cast at h1
    linarith
  have hn' : (t : ℝ) - (jStar : ℝ) + 1 ≤ (n : ℝ) := by
    have h2 : (t : ℤ) - (jStar : ℤ) + 1 ≤ (n : ℤ) := by omega
    have h3 : ((t : ℤ) : ℝ) - ((jStar : ℤ) : ℝ) + 1 ≤ ((n : ℤ) : ℝ) := by exact_mod_cast h2
    push_cast at h3
    linarith
  have hmaxeq : max ((jStar : ℝ) - ((t - (n : ℤ) : ℤ) : ℝ)) 0 =
      (jStar : ℝ) - (t : ℝ) + (n : ℝ) := by
    have hc : ((t - (n : ℤ) : ℤ) : ℝ) = (t : ℝ) - (n : ℝ) := by push_cast; ring
    rw [hc, max_eq_left (by linarith)]
    ring
  have hpw : (3 : ℝ) ^ (-(respRho γ * (n : ℝ))) *
      (3 : ℝ) ^ (γ * max ((jStar : ℝ) - ((t - (n : ℤ) : ℤ) : ℝ)) 0) ≤
      (3 : ℝ) ^ (-(rhoMax d γ * ((t : ℝ) - (jStar : ℝ)))) := by
    rw [hmaxeq, ← Real.rpow_add (by norm_num)]
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have hrho := h5_rhoMax_lt_respRho d hd γ hγ
    have hrhoeq : respRho γ = (1 + γ) / 2 := rfl
    have h1 : (0 : ℝ) ≤ (respRho γ - γ) * ((n : ℝ) - ((t : ℝ) - (jStar : ℝ)) - 1) :=
      mul_nonneg (by rw [hrhoeq]; linarith [hγ.2]) (by linarith)
    have h2 : (0 : ℝ) ≤ (respRho γ - rhoMax d γ) * ((t : ℝ) - (jStar : ℝ)) :=
      mul_nonneg (by linarith) hT0
    nlinarith [h1, h2, hγ.1, hγ.2]
  have hw3 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(rhoMax d γ * ((t : ℝ) - (jStar : ℝ)))) :=
    Real.rpow_nonneg (by norm_num) _
  -- the extra summand of the lower side is `eta`-small
  have hB : (3 : ℝ) ^ (-(respRho γ * (n : ℝ))) ≤ η ^ ((1 : ℝ) / (bigQ d γ : ℝ)) / Cs := by
    have hge1 : (1 : ℝ) ≤
        (3 : ℝ) ^ (γ * max ((jStar : ℝ) - ((t - (n : ℤ) : ℤ) : ℝ)) 0) := by
      have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
        (mul_nonneg hγ.1 (le_max_right ((jStar : ℝ) - ((t - (n : ℤ) : ℤ) : ℝ)) 0))
      rwa [Real.rpow_zero] at h
    have hstep : (3 : ℝ) ^ (-(respRho γ * (n : ℝ))) ≤
        (3 : ℝ) ^ (-(rhoMax d γ * ((t : ℝ) - (jStar : ℝ)))) := by
      refine le_trans ?_ hpw
      nlinarith [hwnn, hge1]
    rw [le_div_iff₀ hCs]
    have hpk : (1 : ℝ) ≤ aspectRatio E * (‖explicitCanonicalMetric F‖ * ‖(explicitCanonicalMetric F)⁻¹‖) := by
      nlinarith [hPi1, hkap]
    have hprod : (0 : ℝ) ≤ Cs * (3 : ℝ) ^ (-(rhoMax d γ * ((t : ℝ) - (jStar : ℝ)))) *
        (aspectRatio E * (‖explicitCanonicalMetric F‖ * ‖(explicitCanonicalMetric F)⁻¹‖) - 1) :=
      mul_nonneg (mul_nonneg hCs.le hw3) (by linarith)
    calc (3 : ℝ) ^ (-(respRho γ * (n : ℝ))) * Cs
        ≤ (3 : ℝ) ^ (-(rhoMax d γ * ((t : ℝ) - (jStar : ℝ)))) * Cs :=
          mul_le_mul_of_nonneg_right hstep hCs.le
      _ ≤ Cs * aspectRatio E * (‖explicitCanonicalMetric F‖ * ‖(explicitCanonicalMetric F)⁻¹‖) *
            (3 : ℝ) ^ (-(rhoMax d γ * ((t : ℝ) - (jStar : ℝ)))) := by nlinarith [hprod]
      _ ≤ η ^ ((1 : ℝ) / (bigQ d γ : ℝ)) := hsrcsmall
  -- the upper side, verbatim from `h5rc_source_term_le`
  have hA : (3 : ℝ) ^ (-(respRho γ * (n : ℝ))) *
      (C₀ * Real.sqrt (‖explicitCanonicalMetric F‖ * ‖(explicitCanonicalMetric F)⁻¹‖) * X a *
        (3 : ℝ) ^ (γ * max ((jStar : ℝ) - ((t - (n : ℤ) : ℤ) : ℝ)) 0) *
        (Cn * aspectRatio E *
          Real.sqrt (‖explicitCanonicalMetric F‖ * ‖(explicitCanonicalMetric F)⁻¹‖))) ≤
      C₀ * Cn / Cs * η ^ ((1 : ℝ) / (bigQ d γ : ℝ)) * X a := by
    have hss' : aspectRatio E * (‖explicitCanonicalMetric F‖ * ‖(explicitCanonicalMetric F)⁻¹‖) *
        (3 : ℝ) ^ (-(rhoMax d γ * ((t : ℝ) - (jStar : ℝ)))) ≤
        η ^ ((1 : ℝ) / (bigQ d γ : ℝ)) / Cs := by
      rw [le_div_iff₀ hCs]
      linarith [hsrcsmall]
    have hXCn : (0 : ℝ) ≤ C₀ * Cn * X a := mul_nonneg (mul_nonneg hC₀.le hCn.le) hXa.le
    have hstep1 : (3 : ℝ) ^ (-(respRho γ * (n : ℝ))) *
        (C₀ * Real.sqrt (‖explicitCanonicalMetric F‖ * ‖(explicitCanonicalMetric F)⁻¹‖) * X a *
          (3 : ℝ) ^ (γ * max ((jStar : ℝ) - ((t - (n : ℤ) : ℤ) : ℝ)) 0) *
          (Cn * aspectRatio E *
            Real.sqrt (‖explicitCanonicalMetric F‖ * ‖(explicitCanonicalMetric F)⁻¹‖))) =
        C₀ * Cn * X a * (aspectRatio E *
          (Real.sqrt (‖explicitCanonicalMetric F‖ * ‖(explicitCanonicalMetric F)⁻¹‖) *
            Real.sqrt (‖explicitCanonicalMetric F‖ * ‖(explicitCanonicalMetric F)⁻¹‖)) *
          ((3 : ℝ) ^ (-(respRho γ * (n : ℝ))) *
            (3 : ℝ) ^ (γ * max ((jStar : ℝ) - ((t - (n : ℤ) : ℤ) : ℝ)) 0))) := by ring
    rw [hstep1, heesq]
    have hstep2 : aspectRatio E * (‖explicitCanonicalMetric F‖ * ‖(explicitCanonicalMetric F)⁻¹‖) *
        ((3 : ℝ) ^ (-(respRho γ * (n : ℝ))) *
          (3 : ℝ) ^ (γ * max ((jStar : ℝ) - ((t - (n : ℤ) : ℤ) : ℝ)) 0)) ≤
        η ^ ((1 : ℝ) / (bigQ d γ : ℝ)) / Cs :=
      le_trans (mul_le_mul_of_nonneg_left hpw (mul_nonneg hPi.le hee)) hss'
    have hstep3 := mul_le_mul_of_nonneg_left hstep2 hXCn
    have hstep4 : C₀ * Cn * X a * (η ^ ((1 : ℝ) / (bigQ d γ : ℝ)) / Cs) =
        C₀ * Cn / Cs * η ^ ((1 : ℝ) / (bigQ d γ : ℝ)) * X a := by field_simp
    rw [hstep4] at hstep3
    exact hstep3
  refine le_trans (mul_le_mul_of_nonneg_left hopn hwnn) ?_
  linarith [hA, hB]

/-- `respAllScaleAbs` is nonnegative: every member of the defining set is, and `Real.sSup`
takes the junk value `0` on an unbounded set. -/
theorem respAllScaleAbs_nonneg (P : Measure (CoeffSpace d)) (γ : ℝ) (jStar : ℕ)
    (F : BlockMat d) (t : ℤ) (a : CoeffSpace d) :
    0 ≤ respAllScaleAbs P γ jStar F t a := by
  refine Real.sSup_nonneg ?_
  rintro y ⟨n, z, _hz, rfl⟩
  exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
    (by rw [blockOpNorm]; exact norm_nonneg _)

/-- **The bounded-supremum lemma for the two-sided all-scale maximum**, the twin of
`respAllScaleMax_le_of_forall`: a single nonnegative bound valid at every scale and index
bounds `A` pathwise, whether or not the family is bounded above. -/
theorem respAllScaleAbs_le_of_forall (P : Measure (CoeffSpace d)) (γ : ℝ) (jStar : ℕ)
    (F : BlockMat d) (t : ℤ) (a : CoeffSpace d) (M : ℝ) (hM : 0 ≤ M)
    (h : ∀ n : ℕ, ∀ z ∈ triadicIndexBox d n,
      (3 : ℝ) ^ (-(respRho γ * (n : ℝ))) *
        blockOpNorm (blockSub
          (normalizedBlock (coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z) a)
            (respMean P jStar F t)) (Book.Ch02.blockIdentity d)) ≤ M) :
    respAllScaleAbs P γ jStar F t a ≤ M := by
  refine Real.sSup_le ?_ hM
  rintro y ⟨n, z, hz, rfl⟩
  exact h n z hz

end Homogenization.HighContrast.Multiscale
