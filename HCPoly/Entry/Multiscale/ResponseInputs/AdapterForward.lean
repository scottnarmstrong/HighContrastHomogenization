import HCPoly.Entry.Multiscale.ResponseInputs.AdapterPartition

open Homogenization.HighContrast (CoeffSpace HasIntegrableCoarseBlock adaptedCellCenter
  adaptedMean annealedBlock aspectRatio blockPosDef_annealedBlock blockScale)
open Homogenization.HighContrast (adaptedCell adaptedCellTranslate centeredCube)
namespace Homogenization.HighContrast.Multiscale.Adapter

open MeasureTheory Geometry
open scoped Matrix.Norms.L2Operator

/-- If `B ≤ A + c • E` and `E ≤ k • A`, then `B ≤ (1 + c * k) • A`: substituting the second
bound into the first and collecting the `A` terms. -/
theorem normalize_forward {d : ℕ} {A B E : BlockMat d} {c k : ℝ}
    (hc : 0 ≤ c)
    (hB : BlockMatLoewnerLE B (ofFullBlockMat (toFullBlockMat A + c • toFullBlockMat E)))
    (hE : BlockMatLoewnerLE E (blockScale k A)) :
    BlockMatLoewnerLE B (blockScale (1 + c * k) A) := by
  intro v
  have hb := hB v
  rw [quadratic_add, quadratic_smul] at hb
  simp only [ofFullBlockMat_toFullBlockMat] at hb
  have he := mul_le_mul_of_nonneg_left (hE v) hc
  rw [Source.quadratic_blockScale] at he ⊢
  nlinarith

/-- E1, with the unused unit-range assumption omitted from this support export. -/
theorem forward_comparison (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
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
              ∀ ℓ : ℕ, 1 ≤ ℓ →
                BlockMatLoewnerLE (adaptedMean P (1 : Mat d) (t + (ℓ : ℤ)))
                  (blockScale (1 + C * aspectRatio E * (‖m‖ * ‖m⁻¹‖) * (3 : ℝ) ^ (-(ℓ : ℝ)))
                    (adaptedMean P (explicitRoundedGrid J m) t)) := by
  let : NeZero d := ⟨by omega⟩
  obtain ⟨Cs, Ca, hCs, hCa, hsource⟩ := aligned_source_bound d hd γ hγ
  obtain ⟨Cn, Cb, hCn, hCb, hnorm⟩ := Annealed.adaptedMean_refBlock_normalization d hd γ hγ
  let D : ℝ := 1 - (3 : ℝ) ^ (-(1 - γ))
  have hD : 0 < D := sub_pos.mpr (Annealed.bridge_fine_ratio_mem_Ico hγ.2).2
  let C : ℝ := Ca * (12 * (d : ℝ) * Real.sqrt d / D) * Cb
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨max Cs Cn, C, lt_max_of_lt_left hCs, hC, ?_⟩
  intro P hP E Ψ K S hstat hdag J hJ hsrc m hm t hJt hwindow ℓ _hℓ
  have hlog : 0 ≤ Real.logb 3 (2 * K) :=
    Real.logb_nonneg (by norm_num) (by linarith [hdag.one_lt_growthWitness])
  have hss := (Int.ceil_mono (mul_le_mul_of_nonneg_right (le_max_left Cs Cn) hlog)).trans hsrc
  have hsn := (Int.ceil_mono (mul_le_mul_of_nonneg_right (le_max_right Cs Cn) hlog)).trans hsrc
  let q := explicitRoundedGrid J m
  have hq : IsUnit q := isUnit_roundedGrid hJ hm
  have hwinJ : adaptedCell q J ⊆ centeredCube d (2 * (J : ℤ)) :=
    (Set.image_mono (Source.centeredCube_mono hJt)).trans hwindow
  have hsrcAll := hsource P E Ψ K S hstat hdag J hJ hss m hm hwinJ
  have hint (r : ℤ) (w : Fin d → ℤ) : HasIntegrableCoarseBlock P (adaptedCellAtCenter q r w) :=
    Annealed.hasIntegrableCoarseBlock_adapted d hd P γ E Ψ K S hstat hdag J hJ m hm r
      (adaptedCellCenter q r w)
  have hintA : HasIntegrableCoarseBlock P (adaptedCell q t) := by
    simpa only [adaptedCellTranslate, zero_add, Set.image_id'] using
      Annealed.hasIntegrableCoarseBlock_adapted d hd P γ E Ψ K S hstat hdag J hJ m hm t 0
  have hA : Book.Ch02.BlockPosDef (adaptedMean P q t) :=
    blockPosDef_annealedBlock hintA (fun a => by
      simpa only [adaptedCellTranslate, zero_add, Set.image_id', HighContrast.adaptedCell, HighContrast.centeredCube] using
        Annealed.blockPosDef_coarseBlock_adapted q hq t 0 a)
  have hintW : HasIntegrableCoarseBlock P (adaptedCellTranslate (1 : Mat d) (t + ℓ) 0) := by
    simpa only [explicitRoundedGrid_one] using Annealed.hasIntegrableCoarseBlock_adapted d hd P γ E Ψ K S
      hstat hdag J hJ (1 : Mat d) (one_posDef d) (t + ℓ) 0
  have hInv : InverseNormLE (q⁻¹ * (1 : Mat d)) (2 * Real.sqrt (‖m‖ * ‖m⁻¹‖)) :=
    relative_inverse_bound hq isUnit_one (by
      simpa only [inv_one, Matrix.one_mul] using opNorm_roundedGrid_le hJ hm)
  have hcap (w : Fin d → ℤ) :
      BlockMatLoewnerLE (annealedBlock P (adaptedCellAtCenter q t w)) (adaptedMean P q t) := by
    rw [Annealed.annealedBlock_adaptedCellAtCenter P hstat J hJ m hm t hJt w]
    exact BlockMatLoewnerLE.refl _
  have hlow (r : ℤ) (hr : r < t) (w : Fin d → ℤ) :
      BlockMatLoewnerLE (annealedBlock P (adaptedCellAtCenter q r w))
        (blockScale (Ca * (3 : ℝ) ^ (γ * ((t : ℝ) - r))) E) := by
    apply (hsrcAll r w).trans
    apply Source.blockScale_le_blockScale_of_pos hdag.refBlock_posDef
    apply mul_le_mul_of_nonneg_left _ hCa.le
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    apply mul_le_mul_of_nonneg_left _ hγ.1
    apply max_le
    · exact sub_le_sub_right (by exact_mod_cast hJt) _
    · exact sub_nonneg.mpr (by exact_mod_cast hr.le)
  have hp := partition_comparison P q (1 : Mat d) hq isUnit_one
    (2 * Real.sqrt (‖m‖ * ‖m⁻¹‖)) (by positivity) hInv (t + ℓ) t 0 γ hγ.2
    (adaptedMean P q t) E hA hdag.refBlock_posDef Ca hCa.le hintW hint hcap hlow
  have hexp : -(((t + (ℓ : ℤ) : ℤ) : ℝ) - (t : ℝ)) = -(ℓ : ℝ) := by push_cast; ring
  simp only [hexp, adaptedCellTranslate, zero_add, Set.image_id'] at hp
  have hn := normalize_forward (by positivity : 0 ≤ Ca *
      ((6 * (d : ℝ) * (2 * Real.sqrt (‖m‖ * ‖m⁻¹‖)) * Real.sqrt d) / D) *
      (3 : ℝ) ^ (-(ℓ : ℝ))) hp
    (hnorm P E Ψ K S hstat hdag J hJ hsn m hm t hJt hwindow).2
  have heq : 1 + (Ca * ((6 * (d : ℝ) * (2 * Real.sqrt (‖m‖ * ‖m⁻¹‖)) * Real.sqrt d) / D) *
        (3 : ℝ) ^ (-(ℓ : ℝ))) * (Cb * aspectRatio E * Real.sqrt (‖m‖ * ‖m⁻¹‖)) =
      1 + C * aspectRatio E * (‖m‖ * ‖m⁻¹‖) * (3 : ℝ) ^ (-(ℓ : ℝ)) := by
    dsimp [C]
    calc
      _ = 1 + Ca * (12 * (d : ℝ) * Real.sqrt d / D) * Cb * aspectRatio E *
          (Real.sqrt (‖m‖ * ‖m⁻¹‖)) ^ 2 * (3 : ℝ) ^ (-(ℓ : ℝ)) := by ring
      _ = _ := by rw [Real.sq_sqrt (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  rw [heq] at hn
  exact hn

end Homogenization.HighContrast.Multiscale.Adapter
