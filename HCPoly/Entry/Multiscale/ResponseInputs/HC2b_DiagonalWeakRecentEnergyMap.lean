import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakRecentLoewner

/-!
# The coarse energy map on the doubled response space

This module proves the coarse energy-map estimate on the doubled response space together with
the intermediate steps it rests on.  The estimate is reached by two chains: one
reaches it through `metricBlockNormSq_recent_difference_le` and
`metricBlockNormSq_average_le_adaptedCellAtCenter`, and the other through
`metricBlockNormSq_blockCellAverage_diagonalWeakState_le`, which also applies
`metricBlockNormSq_average_le_adaptedCellAtCenter`.

The chain is
`doubledResponseJ_zero_left` → `doubledResponseValue_le` /
`doubledResponseValue_zero_left_eq` → `energy_map_le` → `energy_map_metric_le`, and it is
proved here in full.

The reflection order sits above this root: it supplies the comparison hypothesis `hcmp` of
the metric estimate below, and the chain below does not depend on it.  Only the single identity
`Sharp.blockVecDot_blockMatVecMul_blockScale` is needed from that layer; the same identity
already appears in `ResponseTransferSkeleton.lean`, and `E-1` proves it again here so that this
module's import edge stays at `Loewner`.

The final metric estimate is stated for an arbitrary reference block `M : BlockMat d` rather
than the self-dual diagonal metric `blockDiag m m⁻¹`.  That matrix plays no role in the proof —
it occurs only as the left-hand side of the Loewner hypothesis and inside the conclusion's
quadratic form — so taking `M` arbitrary is free, is strictly more general, and commits the
estimate to no one metric encoding.  Later layers may supply whichever of `blockDiag m m⁻¹`,
`blockSqrt (respM0 F)` or `normalizedBlock · ·` they print.
-/

open Homogenization.HighContrast (blockScale)
namespace Homogenization.HighContrast.Multiscale

open Homogenization.Book.Ch02

noncomputable section

variable {d : ℕ}

/-! ## E-1 … E-2: flat helpers -/

/-- **E-1.**  Scalar dilation acts on the doubled quadratic form, the identity
`Sharp.blockVecDot_blockMatVecMul_blockScale`.  The same identity already appears in
`ResponseTransferSkeleton.lean`, but that module is not imported here, so it is proved again
rather than reached for. -/
private theorem r271_qform_blockScale (c : ℝ) (A : BlockMat d) (X : BlockVec d) :
    blockVecDot X (blockMatVecMul (blockScale c A) X) =
      c * blockVecDot X (blockMatVecMul A X) := by
  simp only [blockScale, blockMatVecMul, smul_matVecMul, ← smul_add, blockVecDot,
    vecDot_smul_right]
  ring

/-- **E-2.**  Pairing against the zero doubled vector, the identity `blockVecDot_zero_left`. -/
private theorem r271_blockVecDot_zero_left (X : BlockVec d) :
    blockVecDot (0 : BlockVec d) X = 0 := by
  show vecDot (0 : Vec d) X.1 + vecDot (0 : Vec d) X.2 = 0
  rw [vecDot_zero_left, vecDot_zero_left, add_zero]

/-! ## E-3 … E-6: averages of a doubled field against a fixed load -/

/-- **E-3.**  The normalized average of a scalar sum splits, given integrability: the identity
`average_add`. -/
theorem h6a_average_add {U : Domain d} {f g : Vec d → ℝ}
    (hf : MeasureTheory.IntegrableOn f (U : Set (Vec d)) MeasureTheory.volume)
    (hg : MeasureTheory.IntegrableOn g (U : Set (Vec d)) MeasureTheory.volume) :
    Book.Ch02.average U (fun x => f x + g x) =
      Book.Ch02.average U f + Book.Ch02.average U g := by
  unfold Book.Ch02.average
  rw [MeasureTheory.integral_add hf hg]
  ring

/-- **E-4.**  A component of a square-integrable vector field is integrable on a Chapter 2
domain: the identity `integrableOn_component`. -/
theorem h6a_integrableOn_component {U : Domain d} {F : Vec d → Vec d}
    (hF : MemVectorL2 (U : Set (Vec d)) F) (i : Fin d) :
    MeasureTheory.IntegrableOn (fun x => F x i) (U : Set (Vec d)) MeasureTheory.volume := by
  have hcomp : MeasureTheory.MemLp (fun x => F x i) 2
      (volumeMeasureOn (U : Set (Vec d))) := by
    have := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i).comp_memLp' hF
    simpa using! this
  exact hcomp.integrable (by norm_num)

/-- **E-5.**  The average commutes with pairing against a fixed vector: `(c·F)_U = c·(F)_U`,
the identity `average_vecDot_const`. -/
theorem h6a_average_vecDot_const {U : Domain d} (c : Vec d) {F : Vec d → Vec d}
    (hF : MemVectorL2 (U : Set (Vec d)) F) :
    Book.Ch02.average U (fun x => vecDot c (F x)) = vecDot c (Book.Ch02.averageVec U F) := by
  have hsum : ∫ x in (U : Set (Vec d)), (∑ i : Fin d, c i * F x i) ∂MeasureTheory.volume =
      ∑ i : Fin d, c i * ∫ x in (U : Set (Vec d)), F x i ∂MeasureTheory.volume := by
    rw [MeasureTheory.integral_finsetSum _
      (fun i _ => (h6a_integrableOn_component hF i).const_mul (c i))]
    exact Finset.sum_congr rfl fun i _ => MeasureTheory.integral_const_mul _ _
  show (MeasureTheory.volume (U : Set (Vec d))).toReal⁻¹ *
      ∫ x in (U : Set (Vec d)), (∑ i : Fin d, c i * F x i) ∂MeasureTheory.volume =
    ∑ i : Fin d, c i *
      ((MeasureTheory.volume (U : Set (Vec d))).toReal⁻¹ *
        ∫ x in (U : Set (Vec d)), F x i ∂MeasureTheory.volume)
  rw [hsum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **E-6.**  The average of a doubled field against a fixed load: `(Q·Y)_U = Q·(Y)_U`, the
step that turns the doubled response value into a function of the cell average `(Y)_U` alone,
the identity `average_blockVecDot_const`. -/
theorem h6a_average_blockVecDot_const {U : Domain d} (Q : BlockVec d) (Y : DoubledField d)
    (hp : MemVectorL2 (U : Set (Vec d)) Y.potential)
    (hf : MemVectorL2 (U : Set (Vec d)) Y.flux) :
    Book.Ch02.average U (fun x => blockVecDot Q (Y.eval x)) =
      blockVecDot Q
        ((Book.Ch02.averageVec U Y.potential,
          Book.Ch02.averageVec U Y.flux) : BlockVec d) := by
  have hint1 : MeasureTheory.IntegrableOn (fun x => vecDot Q.1 (Y.potential x))
      (U : Set (Vec d)) MeasureTheory.volume := by
    refine MeasureTheory.integrable_finsetSum _ fun i _ => ?_
    exact (h6a_integrableOn_component hp i).const_mul (Q.1 i)
  have hint2 : MeasureTheory.IntegrableOn (fun x => vecDot Q.2 (Y.flux x))
      (U : Set (Vec d)) MeasureTheory.volume := by
    refine MeasureTheory.integrable_finsetSum _ fun i _ => ?_
    exact (h6a_integrableOn_component hf i).const_mul (Q.2 i)
  show Book.Ch02.average U (fun x => vecDot Q.1 (Y.potential x) + vecDot Q.2 (Y.flux x)) =
    vecDot Q.1 (Book.Ch02.averageVec U Y.potential) + vecDot Q.2 (Book.Ch02.averageVec U Y.flux)
  rw [h6a_average_add hint1 hint2, h6a_average_vecDot_const Q.1 hp,
    h6a_average_vecDot_const Q.2 hf]

/-! ## E-7 … E-8: the doubled response at zero primal load -/

/-- **E-7.**  The doubled variational formula at zero first load
([Armstrong–Kuusi, (2.17)], [Armstrong–Kuusi, (2.20)]):
`𝐉(V,0,Q;a) = ½ Q · 𝐀_*^{-1}(V) Q`,
the identity `doubledResponseJ_zero_left`. -/
theorem h6a_doubledResponseJ_zero_left {U : Domain d} (a : CoeffOn U) (Q : BlockVec d) :
    Book.Ch02.doubledResponseJ U a 0 Q =
      (1 / 2 : ℝ) *
        blockVecDot Q
          (blockMatVecMul (Book.Ch02.coarseStarredBlockMatrixInv U a) Q) := by
  have h := (Book.Ch02.blockCoarseMatrixTheory U a).doubled_response_splitting 0 Q
  rw [h, r271_blockVecDot_zero_left, r271_blockVecDot_zero_left]
  ring

/-- **E-8.**  Every element of the response space is dominated by the doubled formula: for
`Y ∈ 𝒮(V;a)`, the value `⨍_V(-½ Y·𝐀Y + Q·Y)` is at most `½ Q · 𝐀_*^{-1}(V) Q`.  The maximizer
supplied by `DoubledResponseTheory` makes the supremum a greatest element, so no boundedness
argument is needed. -/
theorem h6a_doubledResponseValue_le {U : Domain d} (a : CoeffOn U) (Q : BlockVec d)
    {Y : DoubledField d} (hY : Book.Ch02.IsDoubledResponseField U a Y) :
    Book.Ch02.doubledResponseValue U a 0 Q Y ≤
      (1 / 2 : ℝ) *
        blockVecDot Q
          (blockMatVecMul (Book.Ch02.coarseStarredBlockMatrixInv U a) Q) := by
  obtain ⟨X, hX⟩ := (Book.Ch02.doubledResponseTheory U a).maximizer_exists 0 Q
  have hgreat : IsGreatest (Book.Ch02.doubledResponseValueSet U a 0 Q)
      (Book.Ch02.doubledResponseValue U a 0 Q X) := by
    refine ⟨⟨X, hX.1, rfl⟩, ?_⟩
    rintro y ⟨Z, hZ, rfl⟩
    exact hX.2 Z hZ
  have hJ : Book.Ch02.doubledResponseJ U a 0 Q =
      Book.Ch02.doubledResponseValue U a 0 Q X := hgreat.csSup_eq
  rw [← h6a_doubledResponseJ_zero_left, hJ]
  exact hX.2 Y hY

/-- **E-9.**  The doubled response value at zero first load, expanded: the value of a response
field `Y` is `Q·(Y)_V - ½ ⨍_V Y·𝐀Y`, the form in which the supremum over `Q` is taken in the
energy bound for the dual block. -/
theorem h6a_doubledResponseValue_zero_left_eq {U : Domain d} {lam Lam : ℝ} (a : CoeffOn U)
    (hEll : IsEllipticFieldOn lam Lam (U : Set (Vec d)) a.toCoeffField)
    (Q : BlockVec d) {Y : DoubledField d}
    (hY : Book.Ch02.IsDoubledResponseField U a Y) :
    Book.Ch02.doubledResponseValue U a 0 Q Y =
      blockVecDot Q
          ((Book.Ch02.averageVec U Y.potential,
            Book.Ch02.averageVec U Y.flux) : BlockVec d) -
        (1 / 2 : ℝ) *
          Book.Ch02.average U (fun x =>
            blockVecDot (Y.eval x)
              (blockMatVecMul (Book.Ch02.blockMatrixField a x) (Y.eval x))) := by
  have hp : MemVectorL2 (U : Set (Vec d)) Y.potential := hY.1.1.1
  have hf : MemVectorL2 (U : Set (Vec d)) Y.flux := hY.1.2.1
  have hblock : MemBlockL2 (U : Set (Vec d))
      (({ potential := Y.potential, flux := Y.flux } : BlockState d)).eval :=
    memBlockL2_blockField hp hf
  have hE : MeasureTheory.IntegrableOn (fun x =>
      -Book.Ch02.blockEnergyDensityAt a (Y.eval x) x)
      (U : Set (Vec d)) MeasureTheory.volume :=
    (blockEnergyDensity_integrableOn_of_memBlockL2_of_isEllipticFieldOn hblock hEll).neg
  have hQ : MeasureTheory.IntegrableOn (fun x => blockVecDot Q (Y.eval x))
      (U : Set (Vec d)) MeasureTheory.volume := by
    refine MeasureTheory.Integrable.add ?_ ?_
    · exact MeasureTheory.integrable_finsetSum _ fun i _ =>
        (h6a_integrableOn_component hp i).const_mul (Q.1 i)
    · exact MeasureTheory.integrable_finsetSum _ fun i _ =>
        (h6a_integrableOn_component hf i).const_mul (Q.2 i)
  have hval : Book.Ch02.doubledResponseValue U a 0 Q Y =
      Book.Ch02.average U (fun x =>
        -Book.Ch02.blockEnergyDensityAt a (Y.eval x) x + blockVecDot Q (Y.eval x)) := by
    unfold Book.Ch02.doubledResponseValue Book.Ch02.doubledResponseIntegrand
    congr 1
    funext x
    rw [r271_blockVecDot_zero_left, sub_zero]
  have hhalf : Book.Ch02.average U
      (fun x => -Book.Ch02.blockEnergyDensityAt a (Y.eval x) x) =
      -((1 / 2 : ℝ) *
        Book.Ch02.average U (fun x =>
          blockVecDot (Y.eval x)
            (blockMatVecMul (Book.Ch02.blockMatrixField a x) (Y.eval x)))) := by
    unfold Book.Ch02.average Book.Ch02.blockEnergyDensityAt
    rw [MeasureTheory.integral_neg, MeasureTheory.integral_const_mul]
    ring
  rw [hval, h6a_average_add hE hQ, hhalf, h6a_average_blockVecDot_const Q Y hp hf]
  ring

/-! ## E-10 … E-11: the energy map -/

/-- **E-10.**  The coarse energy-map estimate, the energy bound for the dual block: for every
field `Y` in the doubled response space `𝒮(V;a)` with cell average `y = (Y)_V`,
`½ y·𝐀_*(V) y ≤ ½ ⨍_V Y·𝐀Y`.  The supremum over `Q` is realized at `Q = 𝐀_*(V) y`. -/
theorem h6a_energy_map_le {U : Domain d} {lam Lam : ℝ} (a : CoeffOn U)
    (hEll : IsEllipticFieldOn lam Lam (U : Set (Vec d)) a.toCoeffField)
    {Y : DoubledField d} (hY : Book.Ch02.IsDoubledResponseField U a Y) :
    (1 / 2 : ℝ) *
        blockVecDot
          ((Book.Ch02.averageVec U Y.potential,
            Book.Ch02.averageVec U Y.flux) : BlockVec d)
          (blockMatVecMul (Book.Ch02.coarseStarredBlockMatrix U a)
            ((Book.Ch02.averageVec U Y.potential,
              Book.Ch02.averageVec U Y.flux) : BlockVec d)) ≤
      (1 / 2 : ℝ) *
        Book.Ch02.average U (fun x =>
          blockVecDot (Y.eval x)
            (blockMatVecMul (Book.Ch02.blockMatrixField a x) (Y.eval x))) := by
  set y : BlockVec d :=
    (Book.Ch02.averageVec U Y.potential, Book.Ch02.averageVec U Y.flux) with hy
  set E : ℝ := Book.Ch02.average U (fun x =>
    blockVecDot (Y.eval x)
      (blockMatVecMul (Book.Ch02.blockMatrixField a x) (Y.eval x))) with hE
  set Q : BlockVec d :=
    blockMatVecMul (Book.Ch02.coarseStarredBlockMatrix U a) y with hQ
  have hinv : blockMatVecMul (Book.Ch02.coarseStarredBlockMatrixInv U a) Q = y := by
    rw [hQ, ← blockMatVecMul_blockMatMul,
      (Book.Ch02.blockCoarseMatrixTheory U a).starred_right_inverse,
      blockMatVecMul_blockIdentity]
  have hle := h6a_doubledResponseValue_le a Q hY
  rw [h6a_doubledResponseValue_zero_left_eq a hEll Q hY, hinv] at hle
  have hcomm : blockVecDot Q y =
      blockVecDot y (blockMatVecMul (Book.Ch02.coarseStarredBlockMatrix U a) y) :=
    blockVecDot_comm _ _
  rw [hcomm] at hle
  linarith only [hle]

/-- **E-11.**  The metric form of the energy map: once a reference block `M` is dominated by the
starred coarse block, `M ≤ c 𝐀_*(V)` in the Loewner order, the `M`-size of the cell average is
controlled by the cell energy, `y·M y ≤ c ⨍_V Y·𝐀Y`.

The estimate is stated for an arbitrary `M : BlockMat d`, in place of the self-dual diagonal
metric `blockDiag m m⁻¹`; the generalisation is free because that matrix is never unfolded in
the proof, and it keeps the result uncommitted to any one metric encoding.

This is the declaration both chains described in the header bottom out in. -/
theorem h6a_energy_map_metric_le {U : Domain d} {lam Lam : ℝ} (a : CoeffOn U)
    (hEll : IsEllipticFieldOn lam Lam (U : Set (Vec d)) a.toCoeffField)
    {Y : DoubledField d} (hY : Book.Ch02.IsDoubledResponseField U a Y)
    (M : BlockMat d) {c : ℝ} (hc : 0 ≤ c)
    (hcmp : BlockMatLoewnerLE M
      (blockScale c (Book.Ch02.coarseStarredBlockMatrix U a))) :
    (1 / 2 : ℝ) *
        blockVecDot
          ((Book.Ch02.averageVec U Y.potential,
            Book.Ch02.averageVec U Y.flux) : BlockVec d)
          (blockMatVecMul M
            ((Book.Ch02.averageVec U Y.potential,
              Book.Ch02.averageVec U Y.flux) : BlockVec d)) ≤
      c *
        ((1 / 2 : ℝ) *
          Book.Ch02.average U (fun x =>
            blockVecDot (Y.eval x)
              (blockMatVecMul (Book.Ch02.blockMatrixField a x) (Y.eval x)))) := by
  set y : BlockVec d :=
    (Book.Ch02.averageVec U Y.potential, Book.Ch02.averageVec U Y.flux) with hy
  have h1 := hcmp y
  rw [r271_qform_blockScale] at h1
  have h2 := h6a_energy_map_le a hEll hY
  have hprod := mul_le_mul_of_nonneg_left h2 hc
  linarith only [h1, hprod]


/-- **E-12 — the estimate in the form applied downstream.**  `E-11` with the reference block
taken to be a congruence `R^T I R`: a squared metric size `|R (Y)_V|²` of the cell average,
with no factor `½` on either side.

This is the form the upper layers should use.  It carries no symmetry hypothesis on `R`:
`blockVecDot_blockCongr` already produces the congruence on the nose.  The same shape is
reached elsewhere by unfolding `metricBlockNormSq` at the end of
`metricBlockNormSq_average_le_adaptedCellAtCenter`. -/
theorem h6a_energy_map_congr_le {U : Domain d} {lam Lam : ℝ} (a : CoeffOn U)
    (hEll : IsEllipticFieldOn lam Lam (U : Set (Vec d)) a.toCoeffField)
    {Y : DoubledField d} (hY : Book.Ch02.IsDoubledResponseField U a Y)
    (R : BlockMat d) {c : ℝ} (hc : 0 ≤ c)
    (hcmp : BlockMatLoewnerLE (blockCongr R (Book.Ch02.blockIdentity d))
      (blockScale c (Book.Ch02.coarseStarredBlockMatrix U a))) :
    blockVecDot
        (blockMatVecMul R
          ((Book.Ch02.averageVec U Y.potential,
            Book.Ch02.averageVec U Y.flux) : BlockVec d))
        (blockMatVecMul R
          ((Book.Ch02.averageVec U Y.potential,
            Book.Ch02.averageVec U Y.flux) : BlockVec d)) ≤
      c *
        Book.Ch02.average U (fun x =>
          blockVecDot (Y.eval x)
            (blockMatVecMul (Book.Ch02.blockMatrixField a x) (Y.eval x))) := by
  have h := h6a_energy_map_metric_le a hEll hY
    (blockCongr R (Book.Ch02.blockIdentity d)) hc hcmp
  rw [blockVecDot_blockCongr, blockMatVecMul_blockIdentity] at h
  linarith only [h]

end

end Homogenization.HighContrast.Multiscale
