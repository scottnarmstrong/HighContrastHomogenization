import HCPoly.Entry.Annealed.BridgeComparisons

/-!
Plan for E1, then E2 (HC).

1. Establish identity-grid and integer-translation support, and integrate the
  source bound for standard cells at arbitrary locations. The bounded-window
  multiplier is used after translating an aligned ancestor into its window.
2. Apply standard Whitney subadditivity to obtain an annealed source estimate
  for every rounded adapted cell, without inserting an eccentricity factor:
  the inverse norm of the rounded grid is at most two.
3. Tile a Euclidean cube by maximal adapted cells capped at t. The cap has
  expectation adaptedMean q t by integer stationarity. Lower rows use step 2,
  with a direct relative inverse-norm bound of order e (the general gridRatio
  API raises distortion to power 2d and would lose the required dependence).
  Sum the geometric deficit series, then apply reference normalization.
  Antitonicity does not bound smaller means by the cap mean; only the cap
  uses stationarity, and every smaller row uses the source estimate.
4. Only after E1 closes, exchange grids for E2, cap at t+ell, and normalize
  the source error at t. Constants are chosen before every law and metric.

Every lemma is compiled under the package lock with warnings as errors.
No result from ResponseInputs.Support or the response skeleton is consumed.
-/

open Homogenization.HighContrast (CoeffSpace HasIntegrableCoarseBlock adaptedCellCenter
  adaptedMean annealedBlock blockMatEntry_blockScale blockScale coarseBlock
  toFullBlockMat_eq_blockMatEntry)
open Homogenization.HighContrast (adaptedCell adaptedCellTranslate centeredCube standardCell
  standardCellCenter)
namespace Homogenization.HighContrast.Multiscale.Adapter

open MeasureTheory Geometry
open scoped Matrix.Norms.L2Operator

/-- The adapted cell of the identity grid at generation `j` is the centered cube of side
`3 ^ j`. -/
theorem identity_cell {d : ℕ} (j : ℤ) :
    adaptedCell (1 : Mat d) j = centeredCube d j := by
  have hid : matVecMul (1 : Mat d) = (fun v => v) :=
    funext fun v => by rw [matVecMul_eq_mulVec, Matrix.one_mulVec]
  simp [adaptedCell, hid]

/-- Any generation-`j` standard cell centered at `w` has a generation-`j` recentered copy,
centered at some `u`, that lies inside the generation-`J` centered cube for `j ≤ J`; the two
centers differ by an integer translation `v` at generation `J`. -/
theorem standard_recenter {d : ℕ} {j J : ℤ} (hj : j ≤ J) (w : Fin d → ℤ) :
    ∃ u v : Fin d → ℤ, standardCell d j u ⊆ centeredCube d J ∧
      standardCellCenter j w = standardCellCenter j u + standardCellCenter J v := by
  obtain ⟨v, hv⟩ := Source.exists_standardCell_ancestor hj w
  let n := (J - j).toNat
  have hn : j + (n : ℤ) = J := by
    dsimp [n]
    rw [Int.toNat_of_nonneg (by omega)]
    omega
  let u : Fin d → ℤ := fun i => w i - (3 : ℤ) ^ n * v i
  have hp : (3 : ℝ) ^ J = (3 : ℝ) ^ j * (3 : ℝ) ^ n := by
    rw [← hn, zpow_add₀ (by norm_num), zpow_natCast]
  have hc : standardCellCenter j w = standardCellCenter j u + standardCellCenter J v := by
    ext i
    simp only [standardCellCenter, u, Pi.add_apply, Int.cast_sub, Int.cast_mul,
      Int.cast_pow, Int.cast_ofNat, hp]
    ring
  refine ⟨u, v, ?_, hc⟩
  intro x hx
  have hxw : standardCellCenter J v + x ∈ standardCell d j w := by
    rw [mem_standardCell_iff] at hx ⊢
    intro i
    have hci := congrFun hc i
    simp only [standardCellCenter, Pi.add_apply] at hci ⊢
    constructor <;> nlinarith [(hx i).1, (hx i).2]
  have hparent := hv hxw
  rw [mem_standardCell_iff] at hparent
  rw [mem_centeredCube_iff]
  intro i
  have hi := hparent i
  simp only [standardCellCenter, Pi.add_apply] at hi
  constructor <;> nlinarith [hi.1, hi.2]

/-- The rounded-grid analogue of `standard_recenter`: a generation-`j` adapted cell indexed by
`w`, `j ≤ J`, has a recentered index `u` whose cell lies inside the generation-`J` adapted cell,
and the annealed block over the two cells agrees, since integer translation of an adapted cell
does not change its annealed block under a stationary law. -/
theorem rounded_recenter {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (hstat : IsStationaryLaw P)
    (J : ℕ) (hJ : 2 * d ≤ 3 ^ J) (m : Mat d) (hm : m.PosDef)
    (j : ℤ) (hj : j ≤ (J : ℤ)) (w : Fin d → ℤ) :
    ∃ u : Fin d → ℤ,
      adaptedCellAtCenter (explicitRoundedGrid J m) j u ⊆ adaptedCell (explicitRoundedGrid J m) J ∧
      annealedBlock P (adaptedCellAtCenter (explicitRoundedGrid J m) j w) =
        annealedBlock P (adaptedCellAtCenter (explicitRoundedGrid J m) j u) := by
  obtain ⟨u, v, hu, hc⟩ := standard_recenter hj w
  refine ⟨u, ?_, ?_⟩
  · rw [adaptedCellAtCenter_eq_affine_standardCell, adaptedCell]
    exact Set.image_mono hu
  · obtain ⟨z, hz⟩ := Annealed.adaptedCellCenter_eq_intTranslation J m le_rfl v
    have hcent : adaptedCellCenter (explicitRoundedGrid J m) j w =
        adaptedCellCenter (explicitRoundedGrid J m) j u + Homogenization.Source.AKL.intTranslation z := by
      simp only [adaptedCellCenter_eq_matVecMul_standardCellCenter] at hz ⊢
      rw [hc, matVecMul_eq_mulVec, Matrix.mulVec_add]
      exact congrArg (fun x => matVecMul (explicitRoundedGrid J m) (standardCellCenter j u) + x) hz
    change annealedBlock P (adaptedCellTranslate _ j _) = _
    rw [hcent]
    exact Source.annealedBlock_adapted_add_intTranslation P hstat
      (explicitRoundedGrid J m) (isUnit_roundedGrid hJ hm) j
      (adaptedCellCenter (explicitRoundedGrid J m) j u) z

/-- Averaging a pointwise Loewner bound `coarseBlock U a ≤ c * X a * E` (a.e. in `a`, `X`
integrable) gives the corresponding bound on the annealed block, scaled by the expectation of
`X`. -/
theorem annealed_scale_bound {d : ℕ} {P : Measure (CoeffSpace d)}
    {U : Set (Vec d)} {X : CoeffSpace d → ℝ} {E : BlockMat d} (c : ℝ)
    (hU : HasIntegrableCoarseBlock P U) (hX : Integrable X P)
    (hb : ∀ᵐ a ∂P, BlockMatLoewnerLE (coarseBlock U a) (blockScale (c * X a) E)) :
    BlockMatLoewnerLE (annealedBlock P U) (blockScale (c * ∫ a, X a ∂P) E) := by
  have hi (α β : BlockCoord d) : Integrable
      (fun a => blockMatEntry (blockScale (c * X a) E) α β) P := by
    simpa only [blockMatEntry_blockScale] using (hX.const_mul c).mul_const (blockMatEntry E α β)
  have h := Analysis.blockMatLoewnerLE_integral hU hi hb
  have he : ofFullBlockMat (Matrix.of fun α β =>
      ∫ a, blockMatEntry (blockScale (c * X a) E) α β ∂P) =
      blockScale (c * ∫ a, X a ∂P) E := by
    rw [← ofFullBlockMat_toFullBlockMat (blockScale (c * ∫ a, X a ∂P) E)]
    congr 1
    ext α β
    simp only [Matrix.of_apply, toFullBlockMat_eq_blockMatEntry,
      blockMatEntry_blockScale, integral_mul_const, integral_const_mul]
  rw [he] at h
  simpa only [Matrix.of_apply, Annealed.fullBlock_integral_coarseBlock,
    ofFullBlockMat_toFullBlockMat] using! h

/-- The source bound for aligned cells has no eccentricity cost: the local
Whitney proof only uses the inverse-norm bound two. Recenter fine cells at J,
and use stationarity and monotonicity for coarser cells. -/
theorem aligned_source_bound (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∃ Csrc C : ℝ, 0 < Csrc ∧ 0 < C ∧
      ∀ (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
        (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ),
        IsStationaryLaw P → CoarseEllipticityDagger P γ E Ψ K S →
        ∀ (J : ℕ), 2 * d ≤ 3 ^ J →
          ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (J : ℤ) →
          ∀ (m : Mat d), m.PosDef →
            adaptedCell (explicitRoundedGrid J m) J ⊆ centeredCube d (2 * (J : ℤ)) →
            ∀ (j : ℤ) (w : Fin d → ℤ),
              BlockMatLoewnerLE (annealedBlock P (adaptedCellAtCenter (explicitRoundedGrid J m) j w))
                (blockScale (C * (3 : ℝ) ^ (γ * max ((J : ℝ) - (j : ℝ)) 0)) E) := by
  let : NeZero d := ⟨by omega⟩
  obtain ⟨Csrc, C₀, hCsrc, _hC₀, hsource⟩ :=
    Source.source_multiplier_and_adapted_bound d hd γ hγ
  let D : ℝ := 12 * (d : ℝ) ^ ((3 : ℝ) / 2) / (1 - (3 : ℝ) ^ (-(1 - γ)))
  have hden : 0 < 1 - (3 : ℝ) ^ (-(1 - γ)) :=
    sub_pos.mpr (Annealed.bridge_fine_ratio_mem_Ico hγ.2).2
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨Csrc, 2 * D, hCsrc, by positivity, ?_⟩
  intro P hP E Ψ K S hstat hdag J hJ hsrc m hm hwindow
  obtain ⟨ell, X, _hell, _hX, hform, _hmin, hlp, _hi, _hmoment, hnorm, hpath⟩ :=
    hsource P E Ψ K S hstat hdag J hJ hsrc
  have hX0 (a) : 0 ≤ X a := by rw [hform]; positivity
  have hEX := Annealed.source_envelope_integral_le_two d hd γ hγ P X hX0 hlp hnorm
  have hQ : 1 ≤ ENNReal.ofReal (bigQ d γ : ℝ) := by
    apply ENNReal.one_le_ofReal.mpr
    exact_mod_cast (bigQ_two_le d hd γ hγ).trans' (by norm_num)
  have hlocal (j : ℤ) (y : Vec d)
      (hcell : adaptedCellTranslate (explicitRoundedGrid J m) j y ⊆ centeredCube d (2 * (J : ℤ))) :
      BlockMatLoewnerLE (annealedBlock P (adaptedCellTranslate (explicitRoundedGrid J m) j y))
        (blockScale (2 * D * (3 : ℝ) ^ (γ * max ((J : ℝ) - (j : ℝ)) 0)) E) := by
    have hint := Annealed.hasIntegrableCoarseBlock_adapted d hd P γ E Ψ K S hstat hdag
      J hJ m hm j y
    have hb : ∀ᵐ a ∂P, BlockMatLoewnerLE
        (coarseBlock (adaptedCellTranslate (explicitRoundedGrid J m) j y) a)
        (blockScale ((D * (3 : ℝ) ^ (γ * max ((J : ℝ) - (j : ℝ)) 0)) * X a) E) := by
      filter_upwards [hpath] with a ha
      simpa only [D, mul_assoc, mul_left_comm, mul_comm] using
        Source.adapted_bound_of_standard γ hγ E hdag.refBlock_posDef a J (X a) (hX0 a)
          ha.1 (inverseNormLE_roundedGrid hJ hm) j y hcell
    exact (annealed_scale_bound _ hint (hlp.integrable hQ) hb).trans
      (Source.blockScale_le_blockScale_of_pos hdag.refBlock_posDef (by
        nlinarith [mul_le_mul_of_nonneg_left hEX
          (show 0 ≤ D * (3 : ℝ) ^ (γ * max ((J : ℝ) - (j : ℝ)) 0) by positivity)]))
  intro j w
  by_cases hj : j ≤ (J : ℤ)
  · obtain ⟨u, hu, he⟩ := rounded_recenter P hstat J hJ m hm j hj w
    rw [he]
    exact hlocal j (adaptedCellCenter (explicitRoundedGrid J m) j u) (hu.trans hwindow)
  · have hJj : (J : ℤ) ≤ j := le_of_lt (lt_of_not_ge hj)
    rw [Annealed.annealedBlock_adaptedCellAtCenter P hstat J hJ m hm j hJj w]
    have hmono := Annealed.adaptedMean_antitone d hd P γ E Ψ K S hstat hdag
      J hJ m hm J j le_rfl hJj
    have hb := hlocal J 0 (by simpa [adaptedCellTranslate] using hwindow)
    have hJR : (J : ℝ) ≤ (j : ℝ) := by exact_mod_cast hJj
    simpa [adaptedCellTranslate, adaptedMean, max_eq_right (sub_nonpos.mpr hJR)] using
      hmono.trans (by
        simpa [adaptedCellTranslate, adaptedMean, HighContrast.adaptedCell,
          HighContrast.centeredCube] using hb)

end Homogenization.HighContrast.Multiscale.Adapter
