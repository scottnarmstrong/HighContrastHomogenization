import HCPoly.Entry.Multiscale.ResponseInputs.AdapterPartition

open Homogenization.HighContrast (CoeffSpace HasIntegrableCoarseBlock adaptedCellCenter
  adaptedMean annealedBlock aspectRatio blockPosDef_annealedBlock blockScale blockSub)
open Homogenization.HighContrast (adaptedCell adaptedCellTranslate centeredCube)
namespace Homogenization.HighContrast.Multiscale.Adapter

open MeasureTheory Geometry
open scoped Matrix.Norms.L2Operator

/-- The reverse companion of `normalize_forward`: if `A` is positive definite, `B ≤ M + c • E`,
`E ≤ k • A`, and `c * k ≤ δ`, then `B - δ • A ≤ M`. -/
theorem normalize_reverse {d : ℕ} {A B M E : BlockMat d} {c k δ : ℝ}
    (hA : Book.Ch02.BlockPosDef A) (hc : 0 ≤ c) (hδ : c * k ≤ δ)
    (hB : BlockMatLoewnerLE B (ofFullBlockMat (toFullBlockMat M + c • toFullBlockMat E)))
    (hE : BlockMatLoewnerLE E (blockScale k A)) :
    BlockMatLoewnerLE (blockSub B (blockScale δ A)) M := by
  intro v
  have hb := hB v
  rw [quadratic_add, quadratic_smul] at hb
  simp only [ofFullBlockMat_toFullBlockMat] at hb
  have he := mul_le_mul_of_nonneg_left (hE v) hc
  rw [Source.quadratic_blockScale] at he
  have hδv := mul_le_mul_of_nonneg_right hδ (quadratic_nonneg hA v)
  have hsub := blockVecDot_blockMatVecMul_ofFullBlockMat_sub B (blockScale δ A) v
  change blockVecDot v (blockMatVecMul (blockSub B (blockScale δ A)) v) = _ at hsub
  rw [hsub, mul_sub, Source.quadratic_blockScale]
  linarith

/-- E2 from the same capped partition, now with standard cells in the adapted
parent. The source normalization is still taken at the original generation t. -/
theorem reverse_comparison (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∃ Csrc C : ℝ, 0 < Csrc ∧ 0 < C ∧
      ∀ (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
        (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ),
        IsStationaryLaw P → CoarseEllipticityDagger P γ E Ψ K S →
        ∀ (J : ℕ), 2 * d ≤ 3 ^ J →
          ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (J : ℤ) →
          ∀ (m : Mat d), m.PosDef →
            ∀ t : ℤ, (J : ℤ) ≤ t →
              adaptedCell (explicitRoundedGrid J m) t ⊆ centeredCube d (2 * (J : ℤ)) →
              ∀ ℓ r : ℕ, 1 ≤ ℓ → 1 ≤ r →
                BlockMatLoewnerLE
                  (blockSub (adaptedMean P (explicitRoundedGrid J m) (t + (ℓ : ℤ) + (r : ℤ)))
                    (blockScale (C * aspectRatio E * (‖m‖ * ‖m⁻¹‖) * (3 : ℝ) ^ (-(r : ℝ)))
                      (adaptedMean P (explicitRoundedGrid J m) t)))
                  (adaptedMean P (1 : Mat d) (t + (ℓ : ℤ))) := by
  let : NeZero d := ⟨by omega⟩
  obtain ⟨Cs, Ca, hCs, hCa, hsource⟩ := aligned_source_bound d hd γ hγ
  obtain ⟨Cn, Cb, hCn, hCb, hnorm⟩ := Annealed.adaptedMean_refBlock_normalization d hd γ hγ
  let D : ℝ := 1 - (3 : ℝ) ^ (-(1 - γ))
  have hD : 0 < D := sub_pos.mpr (Annealed.bridge_fine_ratio_mem_Ico hγ.2).2
  let C : ℝ := Ca * (12 * (d : ℝ) * Real.sqrt d / D) * Cb
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨max Cs Cn, C, lt_max_of_lt_left hCs, hC, ?_⟩
  intro P hP E Ψ K S hstat hdag J hJ hsrc m hm t hJt hwindow ℓ r _hℓ _hr
  have hlog : 0 ≤ Real.logb 3 (2 * K) :=
    Real.logb_nonneg (by norm_num) (by linarith [hdag.one_lt_growthWitness])
  have hss := (Int.ceil_mono (mul_le_mul_of_nonneg_right (le_max_left Cs Cn) hlog)).trans hsrc
  have hsn := (Int.ceil_mono (mul_le_mul_of_nonneg_right (le_max_right Cs Cn) hlog)).trans hsrc
  let q := explicitRoundedGrid J m
  have hq : IsUnit q := isUnit_roundedGrid hJ hm
  have hwin1 : adaptedCell (explicitRoundedGrid J (1 : Mat d)) J ⊆ centeredCube d (2 * (J : ℤ)) := by
    rw [explicitRoundedGrid_one, identity_cell]
    exact Source.centeredCube_mono (by omega)
  have hsrcAll (j : ℤ) (w : Fin d → ℤ) :
      BlockMatLoewnerLE (annealedBlock P (adaptedCellAtCenter (1 : Mat d) j w))
        (blockScale (Ca * (3 : ℝ) ^ (γ * max ((J : ℝ) - (j : ℝ)) 0)) E) := by
    simpa only [explicitRoundedGrid_one] using
      hsource P E Ψ K S hstat hdag J hJ hss (1 : Mat d) (one_posDef d) hwin1 j w
  have hint (j : ℤ) (w : Fin d → ℤ) : HasIntegrableCoarseBlock P (adaptedCellAtCenter (1 : Mat d) j w) := by
    simpa only [explicitRoundedGrid_one] using!
      Annealed.hasIntegrableCoarseBlock_adapted d hd P γ E Ψ K S hstat hdag J hJ
        (1 : Mat d) (one_posDef d) j (adaptedCellCenter (1 : Mat d) j w)
  have hintM : HasIntegrableCoarseBlock P (adaptedCell (1 : Mat d) (t + ℓ)) := by
    simpa only [explicitRoundedGrid_one, adaptedCellTranslate, zero_add, Set.image_id'] using
      Annealed.hasIntegrableCoarseBlock_adapted d hd P γ E Ψ K S hstat hdag J hJ
        (1 : Mat d) (one_posDef d) (t + ℓ) 0
  have hM : Book.Ch02.BlockPosDef (adaptedMean P (1 : Mat d) (t + ℓ)) :=
    blockPosDef_annealedBlock hintM (fun a => by
      simpa only [adaptedCellTranslate, zero_add, Set.image_id', HighContrast.adaptedCell, HighContrast.centeredCube] using
        Annealed.blockPosDef_coarseBlock_adapted (1 : Mat d) isUnit_one (t + ℓ) 0 a)
  have hintA : HasIntegrableCoarseBlock P (adaptedCell q t) := by
    simpa only [adaptedCellTranslate, zero_add, Set.image_id'] using
      Annealed.hasIntegrableCoarseBlock_adapted d hd P γ E Ψ K S hstat hdag J hJ m hm t 0
  have hA : Book.Ch02.BlockPosDef (adaptedMean P q t) :=
    blockPosDef_annealedBlock hintA (fun a => by
      simpa only [adaptedCellTranslate, zero_add, Set.image_id', HighContrast.adaptedCell, HighContrast.centeredCube] using
        Annealed.blockPosDef_coarseBlock_adapted q hq t 0 a)
  have hintW : HasIntegrableCoarseBlock P (adaptedCellTranslate q (t + ℓ + r) 0) :=
    Annealed.hasIntegrableCoarseBlock_adapted d hd P γ E Ψ K S hstat hdag J hJ m hm (t + ℓ + r) 0
  have hInv : InverseNormLE ((1 : Mat d)⁻¹ * q) 2 :=
    relative_inverse_bound isUnit_one hq (by
      simpa only [Matrix.mul_one] using opNorm_roundedGrid_inv_le hJ hm)
  have hcap (w : Fin d → ℤ) :
      BlockMatLoewnerLE (annealedBlock P (adaptedCellAtCenter (1 : Mat d) (t + ℓ) w))
        (adaptedMean P (1 : Mat d) (t + ℓ)) := by
    have he := Annealed.annealedBlock_adaptedCellAtCenter P hstat J hJ (1 : Mat d) (one_posDef d)
      (t + ℓ) (by omega) w
    simp only [explicitRoundedGrid_one] at he
    rw [he]
    exact BlockMatLoewnerLE.refl _
  have hlow (j : ℤ) (hj : j < t + ℓ) (w : Fin d → ℤ) :
      BlockMatLoewnerLE (annealedBlock P (adaptedCellAtCenter (1 : Mat d) j w))
        (blockScale (Ca * (3 : ℝ) ^ (γ * (((t + (ℓ : ℤ) : ℤ) : ℝ) - j))) E) := by
    apply (hsrcAll j w).trans
    apply Source.blockScale_le_blockScale_of_pos hdag.refBlock_posDef
    apply mul_le_mul_of_nonneg_left _ hCa.le
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    apply mul_le_mul_of_nonneg_left _ hγ.1
    apply max_le
    · exact sub_le_sub_right (by exact_mod_cast (show (J : ℤ) ≤ t + ℓ by omega)) _
    · exact sub_nonneg.mpr (by exact_mod_cast hj.le)
  have hp := partition_comparison P (1 : Mat d) q isUnit_one hq 2 (by norm_num) hInv
    (t + ℓ + r) (t + ℓ) 0 γ hγ.2 (adaptedMean P (1 : Mat d) (t + ℓ)) E hM
    hdag.refBlock_posDef Ca hCa.le hintW hint hcap hlow
  have hexp : -(((t + (ℓ : ℤ) + (r : ℤ) : ℤ) : ℝ) - ((t + (ℓ : ℤ) : ℤ) : ℝ)) =
      -(r : ℝ) := by push_cast; ring
  simp only [hexp, adaptedCellTranslate, zero_add, Set.image_id'] at hp
  have hecc : Real.sqrt (‖m‖ * ‖m⁻¹‖) ≤ ‖m‖ * ‖m⁻¹‖ := by
    have he := Source.one_le_source_eccentricity hm
    have he2 := Real.sq_sqrt (mul_nonneg (norm_nonneg m) (norm_nonneg m⁻¹))
    nlinarith
  have hPi : 0 ≤ aspectRatio E := (Annealed.one_le_aspectRatio hdag).trans' zero_le_one
  have hδ : (Ca * ((6 * (d : ℝ) * 2 * Real.sqrt d) / D) * (3 : ℝ) ^ (-(r : ℝ))) *
      (Cb * aspectRatio E * Real.sqrt (‖m‖ * ‖m⁻¹‖)) ≤
      C * aspectRatio E * (‖m‖ * ‖m⁻¹‖) * (3 : ℝ) ^ (-(r : ℝ)) := by
    calc
      _ = C * aspectRatio E * Real.sqrt (‖m‖ * ‖m⁻¹‖) * (3 : ℝ) ^ (-(r : ℝ)) := by
        dsimp [C]
        ring
      _ ≤ _ := by gcongr
  exact normalize_reverse hA (by positivity) hδ hp
    (hnorm P E Ψ K S hstat hdag J hJ hsn m hm t hJt hwindow).2

end Homogenization.HighContrast.Multiscale.Adapter
