import HCPoly.Entry.Multiscale.ResponseInputs.HC1_DomainBridgeAnnealedBlock
import Homogenization.Deterministic.WeakNormInterfaces.Definitions

/-!
# HC bridge II: the scale-average seminorm (AK.HC (2.130))

The carrier is `besovSeminorm t avg` (`AdaptedDefs.lean`, real `tsum`); the
`ℝ≥0∞`-valued `adaptedWeakSeminorm q t s F` is the alternative.  The real carrier needs the
summability supplied below.  Paper `p.response.transfer`.

The pullback to the reference cube is in `HC2a_ReferenceCubePullback.lean`; the diagonal
weak-norm primal bound is in `HC2b_DiagonalWeakRecentSupport.lean` /
`HC2b_DiagonalWeakRecent.lean`.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]

/-- The cell-average family of a doubled field on the selected grid: depth `n`, label `w`
(old `blockCellAverage ∘ adaptedCellAtCenter`, `WeakNorm.lean`). -/
def cellAverageFamily (q : Mat d) (t : ℤ) (X : Vec d → BlockVec d) :
    ℕ → (Fin d → ℤ) → BlockVec d :=
  fun n w => cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) X

/-- The squared `L²(U_t)` mean of a doubled field. -/
def cellMeanSq (V : Set (Vec d)) (X : Vec d → BlockVec d) : ℝ :=
  volumeAverage V fun x => blockVecDot (X x) (X x)

/-! ## Summability and the Jensen/partition bound
(`p.response.transfer`: a constant `c` has `3^{-t/2}[c] = |c|/(1-3^{-1/2})`; the general
field is bounded the same way through Jensen on each cell and exact partition averaging,
`p.response.transfer`).  Old counterpart: the `ℝ≥0∞` sum needed no summability
(`WeakNorm.lean`); the real carrier does. -/

/-! ## HELPERS -/

omit [NeZero d] in
/-- Scalar Jensen for `volumeAverage`. -/
theorem volumeAverage_mul_self_le {V : Set (Vec d)} (hV : MeasurableSet V)
    (hfin : volume V ≠ ⊤) (hvol : (volume V).toReal ≠ 0) {g : Vec d → ℝ}
    (hg : IntegrableOn g V) (hg2 : IntegrableOn (fun x => g x * g x) V) :
    volumeAverage V g * volumeAverage V g ≤ volumeAverage V (fun x => g x * g x) := by
  have : IsFiniteMeasure (volume.restrict V) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_of_le_of_ne le_top hfin⟩
  set c := volumeAverage V g with hc
  have hconst : IntegrableOn (fun _ : Vec d => c * c) V := integrable_const _
  have hlin : IntegrableOn (fun x => (2 * c) * g x) V := hg.const_mul _
  have hd : IntegrableOn (fun x => g x * g x - (2 * c) * g x) V := hg2.sub hlin
  have hnn : 0 ≤ volumeAverage V (fun x => (g x - c) * (g x - c)) := by
    refine volumeAverage_nonneg_of_nonneg_on hV ?_
    intro x _
    exact mul_self_nonneg _
  have h2 : volumeAverage V (fun x => g x * g x - (2 * c) * g x)
      = volumeAverage V (fun x => g x * g x) - (2 * c) * c := by
    have hrw : (fun x => g x * g x - (2 * c) * g x)
        = (fun x => g x * g x) - ((2 * c) • g) := by
      funext x; simp [smul_eq_mul]
    rw [hrw, volumeAverage_sub hg2 (by simpa [smul_eq_mul] using! hlin), volumeAverage_smul]
  have heq : volumeAverage V (fun x => (g x - c) * (g x - c))
      = volumeAverage V (fun x => g x * g x) - c * c := by
    have h1 : (fun x => (g x - c) * (g x - c))
        = (fun x => g x * g x - (2 * c) * g x) + (fun _ => c * c) := by
      funext x; simp only [Pi.add_apply]; ring
    rw [h1, volumeAverage_add hd hconst, volumeAverage_const hvol, h2]
    ring
  linarith [heq ▸ hnn]

omit [NeZero d] in
/-- Finite-family Jensen, junk-safe: non-integrable components contribute `0` on the left. -/
theorem sum_volumeAverage_mul_self_le {ι : Type*} [Fintype ι] {V : Set (Vec d)}
    (hV : MeasurableSet V) (hfin : volume V ≠ ⊤) (hvol : (volume V).toReal ≠ 0)
    (g : ι → Vec d → ℝ)
    (hG : IntegrableOn (fun x => ∑ k, g k x * g k x) V) :
    ∑ k, volumeAverage V (g k) * volumeAverage V (g k)
      ≤ volumeAverage V (fun x => ∑ k, g k x * g k x) := by
  classical
  have : IsFiniteMeasure (volume.restrict V) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_of_le_of_ne le_top hfin⟩
  set s : Finset ι := Finset.univ.filter (fun k => IntegrableOn (g k) V) with hs
  have hmem : ∀ k ∈ s, IntegrableOn (g k) V := by
    intro k hk
    exact (Finset.mem_filter.mp hk).2
  have hzero : ∀ k, k ∉ s → volumeAverage V (g k) = 0 := by
    intro k hk
    have hni : ¬ IntegrableOn (g k) V := by
      intro h; exact hk (Finset.mem_filter.mpr ⟨Finset.mem_univ k, h⟩)
    unfold volumeAverage
    rw [integral_undef hni, mul_zero]
  have hL : ∑ k, volumeAverage V (g k) * volumeAverage V (g k)
      = ∑ k ∈ s, volumeAverage V (g k) * volumeAverage V (g k) := by
    refine (Finset.sum_subset (Finset.subset_univ s) ?_).symm
    intro k _ hk
    rw [hzero k hk, mul_zero]
  have hptnn : ∀ (x : Vec d) (k : ι), g k x * g k x ≤ ∑ j, g j x * g j x := by
    intro x k
    exact Finset.single_le_sum (f := fun j => g j x * g j x)
      (fun j _ => mul_self_nonneg _) (Finset.mem_univ k)
  have hsq : ∀ k ∈ s, IntegrableOn (fun x => g k x * g k x) V := by
    intro k hk
    have hgk := hmem k hk
    refine hG.mono' (hgk.aestronglyMeasurable.mul hgk.aestronglyMeasurable) ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_self_nonneg _)]
    exact hptnn x k
  have hsInt : IntegrableOn (fun x => ∑ k ∈ s, g k x * g k x) V := by
    simpa [IntegrableOn] using
      (integrable_finsetSum (μ := volume.restrict V) s
        (fun k hk => (hsq k hk).integrable))
  calc ∑ k, volumeAverage V (g k) * volumeAverage V (g k)
      = ∑ k ∈ s, volumeAverage V (g k) * volumeAverage V (g k) := hL
    _ ≤ ∑ k ∈ s, volumeAverage V (fun x => g k x * g k x) :=
        Finset.sum_le_sum (fun k hk =>
          volumeAverage_mul_self_le hV hfin hvol (hmem k hk) (hsq k hk))
    _ = volumeAverage V (fun x => ∑ k ∈ s, g k x * g k x) :=
        (volumeAverage_sum s (fun k x => g k x * g k x) hsq).symm
    _ ≤ volumeAverage V (fun x => ∑ k, g k x * g k x) := by
        refine volumeAverage_le_volumeAverage_of_le_on hV hsInt hG ?_
        intro x _
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
          (fun j _ _ => mul_self_nonneg _)

omit [NeZero d] in
/-- Jensen for the doubled cell average: `|(X)_V|² ≤ (|X|²)_V`. -/
theorem blockVecDot_cellAverage_self_le_cellMeanSq {V : Set (Vec d)} (hV : MeasurableSet V)
    (hfin : volume V ≠ ⊤) (hvol : (volume V).toReal ≠ 0) (X : Vec d → BlockVec d)
    (hX : IntegrableOn (fun x => blockVecDot (X x) (X x)) V) :
    blockVecDot (cellAverage V X) (cellAverage V X) ≤ cellMeanSq V X := by
  classical
  set g : (Fin d ⊕ Fin d) → Vec d → ℝ :=
    fun k x => Sum.elim (fun i => (X x).1 i) (fun i => (X x).2 i) k with hgdef
  have hsum : ∀ x : Vec d, ∑ k, g k x * g k x = blockVecDot (X x) (X x) := by
    intro x
    rw [Fintype.sum_sum_type]
    simp [hgdef, blockVecDot, vecDot]
  have hG : IntegrableOn (fun x => ∑ k, g k x * g k x) V := by
    simpa only [hsum] using hX
  have hmain := sum_volumeAverage_mul_self_le hV hfin hvol g hG
  have hR : volumeAverage V (fun x => ∑ k, g k x * g k x) = cellMeanSq V X := by
    unfold cellMeanSq
    exact congrArg (volumeAverage V) (funext hsum)
  have hLhs : ∑ k, volumeAverage V (g k) * volumeAverage V (g k)
      = blockVecDot (cellAverage V X) (cellAverage V X) := by
    rw [Fintype.sum_sum_type]
    simp [hgdef, blockVecDot, vecDot, cellAverage]
  rw [hLhs, hR] at hmain
  exact hmain

/-! ## GEOMETRY.  `standardCell_subset_centeredCube_of_mem_triadicIndexBox` and
`adaptedCellAtCenter_subset_adaptedCell` are imported from `HC1_DomainBridge.lean`. -/

omit [NeZero d] in
theorem card_triadicIndexBox (n : ℕ) : ((triadicIndexBox d n).card : ℝ) = ((3 : ℝ) ^ n) ^ d := by
  classical
  have hone : 1 ≤ (3 : ℕ) ^ n := Nat.one_le_pow _ _ (by norm_num)
  have hdvd : 2 ∣ (3 : ℕ) ^ n - 1 := by
    have hodd : Odd ((3 : ℕ) ^ n) := Odd.pow (by decide)
    exact (Nat.Odd.sub_odd hodd odd_one).two_dvd
  have hIcc : (Finset.Icc (-(((3 ^ n - 1) / 2 : ℕ) : ℤ)) (((3 ^ n - 1) / 2 : ℕ) : ℤ)).card
      = (3 : ℕ) ^ n := by
    rw [Int.card_Icc]
    have h2 : 2 * ((3 ^ n - 1) / 2 : ℕ) = (3 : ℕ) ^ n - 1 := Nat.mul_div_cancel' hdvd
    omega
  have hc : (triadicIndexBox d n).card = ((3 : ℕ) ^ n) ^ d := by
    unfold triadicIndexBox
    rw [Fintype.card_piFinset, Finset.prod_congr rfl (fun i _ => hIcc)]
    simp
  rw [hc]
  push_cast
  ring

omit [NeZero d] in
theorem isOpen_adaptedCell_of_isUnit {q : Mat d} (hq : IsUnit q) (j : ℤ) :
    IsOpen (HighContrast.adaptedCell q j) := by
  have h0 : HighContrast.adaptedCellTranslate q j 0 = HighContrast.adaptedCell q j := by
    ext x; simp [HighContrast.adaptedCellTranslate]
  rw [← h0]
  exact Geometry.isOpen_adaptedCellTranslate hq j 0

omit [NeZero d] in
theorem isOpen_adaptedCellAtCenter_of_isUnit {q : Mat d} (hq : IsUnit q) (j : ℤ) (w : Fin d → ℤ) :
    IsOpen (adaptedCellAtCenter q j w) :=
  Geometry.isOpen_adaptedCellTranslate hq j _

/-! ## The scale-term average bound -/

omit [NeZero d] in
/-- Each scale term is bounded by the `L²(U_t)` mean: Jensen on cells + exact partition
of `U_t` by the `3^{nd}` depth-`n` cells. -/
theorem avsum_cellAverageFamily_sq_le (q : Mat d) (hq : IsUnit q) (t : ℤ)
    (X : Vec d → BlockVec d) (hX : MemLp (fun x => blockVecDot (X x) (X x)) 1
      (volume.restrict (HighContrast.adaptedCell q t))) (n : ℕ) :
    (((triadicIndexBox d n).card : ℝ))⁻¹ *
        ∑ w ∈ triadicIndexBox d n,
          blockVecDot (cellAverageFamily q t X n w) (cellAverageFamily q t X n w) ≤
      cellMeanSq (HighContrast.adaptedCell q t) X := by
  classical
  set U : Set (Vec d) := HighContrast.adaptedCell q t with hU
  set f : Vec d → ℝ := fun x => blockVecDot (X x) (X x) with hf
  have hfnn : ∀ x, 0 ≤ f x := by
    intro x
    have : f x = (∑ i, (X x).1 i * (X x).1 i) + ∑ i, (X x).2 i * (X x).2 i := by
      simp [hf, blockVecDot, vecDot]
    rw [this]
    exact add_nonneg (Finset.sum_nonneg fun i _ => mul_self_nonneg _)
      (Finset.sum_nonneg fun i _ => mul_self_nonneg _)
  have hdet : |q.det| ≠ 0 := by
    have := (Matrix.isUnit_iff_isUnit_det q).mp hq
    exact abs_ne_zero.mpr (IsUnit.ne_zero this)
  have hUmeas : MeasurableSet U := (isOpen_adaptedCell_of_isUnit hq t).measurableSet
  have hUreal : (volume U).toReal = |q.det| * ((3 : ℝ) ^ t) ^ d :=
    Geometry.volume_adaptedCell_toReal q t
  have hUfin : volume U ≠ ⊤ := by
    rw [hU, Geometry.volume_adaptedCell]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  have hUpos : 0 < (volume U).toReal := by
    rw [hUreal]
    have h1 : 0 < |q.det| := abs_pos.mpr (by
      have := (Matrix.isUnit_iff_isUnit_det q).mp hq
      exact IsUnit.ne_zero this)
    positivity
  have hXint : IntegrableOn f U := (memLp_one_iff_integrable.mp hX)
  -- per-cell data
  set V : (Fin d → ℤ) → Set (Vec d) := fun w => adaptedCellAtCenter q (t - (n : ℤ)) w with hV
  have hVmeas : ∀ w, MeasurableSet (V w) := fun w => (isOpen_adaptedCellAtCenter_of_isUnit hq _ w).measurableSet
  have hVreal : ∀ w, (volume (V w)).toReal = |q.det| * ((3 : ℝ) ^ (t - (n : ℤ))) ^ d := by
    intro w
    rw [hV, Geometry.volume_adaptedCellAtCenter]
    rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal (abs_nonneg _),
      ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ (3 : ℝ) ^ (t - (n : ℤ)))]
  have hVfin : ∀ w, volume (V w) ≠ ⊤ := fun w => Geometry.volume_adaptedCellAtCenter_ne_top q _ w
  have hVpos : ∀ w, 0 < (volume (V w)).toReal := by
    intro w
    rw [hVreal w]
    have h1 : 0 < |q.det| := abs_pos.mpr (by
      have := (Matrix.isUnit_iff_isUnit_det q).mp hq
      exact IsUnit.ne_zero this)
    positivity
  have hsub : ∀ w ∈ triadicIndexBox d n, V w ⊆ U := by
    intro w hw
    exact adaptedCellAtCenter_subset_adaptedCell q t n hw
  have hVint : ∀ w ∈ triadicIndexBox d n, IntegrableOn f (V w) :=
    fun w hw => hXint.mono_set (hsub w hw)
  -- Step 1: Jensen on each cell
  have hJ : ∀ w ∈ triadicIndexBox d n,
      blockVecDot (cellAverageFamily q t X n w) (cellAverageFamily q t X n w)
        ≤ (volume (V w)).toReal⁻¹ * ∫ x in V w, f x := by
    intro w hw
    have := blockVecDot_cellAverage_self_le_cellMeanSq (V := V w) (hVmeas w) (hVfin w)
      (ne_of_gt (hVpos w)) X (hVint w hw)
    simpa [cellAverageFamily, cellMeanSq, volumeAverage, hV, hf] using this
  -- Step 2: sum of the integrals
  have hdisj : Set.Pairwise (↑(triadicIndexBox d n) : Set (Fin d → ℤ))
      (Function.onFun Disjoint V) := by
    intro a _ b _ hab
    exact Geometry.adaptedCellAtCenter_disjoint_of_ne hq _ hab
  have hunion : ∫ x in (⋃ w ∈ triadicIndexBox d n, V w), f x
      = ∑ w ∈ triadicIndexBox d n, ∫ x in V w, f x :=
    integral_biUnion_finset _ (fun w _ => hVmeas w) hdisj hVint
  have hUsub : (⋃ w ∈ triadicIndexBox d n, V w) ⊆ U := by
    refine Set.iUnion₂_subset ?_
    intro w hw
    exact hsub w hw
  have hmono : ∫ x in (⋃ w ∈ triadicIndexBox d n, V w), f x ≤ ∫ x in U, f x := by
    refine setIntegral_mono_set hXint ?_ (LE.le.eventuallyLE hUsub)
    filter_upwards with x using hfnn x
  have hsumle : ∑ w ∈ triadicIndexBox d n, ∫ x in V w, f x ≤ ∫ x in U, f x := by
    rw [← hunion]; exact hmono
  -- Step 3: arithmetic
  have hNcard : ((triadicIndexBox d n).card : ℝ) = ((3 : ℝ) ^ n) ^ d := card_triadicIndexBox n
  have hNpos : (0 : ℝ) < ((triadicIndexBox d n).card : ℝ) := by
    rw [hNcard]; positivity
  have hprod : ((triadicIndexBox d n).card : ℝ) * (volume (V 0)).toReal = (volume U).toReal := by
    rw [hNcard, hVreal 0, hUreal]
    have h3 : (3 : ℝ) ^ n * (3 : ℝ) ^ (t - (n : ℤ)) = (3 : ℝ) ^ t := by
      rw [show ((3 : ℝ) ^ n) = (3 : ℝ) ^ ((n : ℤ)) from (zpow_natCast (3 : ℝ) n).symm,
        ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
      ring_nf
    calc ((3 : ℝ) ^ n) ^ d * (|q.det| * ((3 : ℝ) ^ (t - (n : ℤ))) ^ d)
        = |q.det| * ((3 : ℝ) ^ n * (3 : ℝ) ^ (t - (n : ℤ))) ^ d := by rw [mul_pow]; ring
      _ = |q.det| * ((3 : ℝ) ^ t) ^ d := by rw [h3]
  have hVconst : ∀ w, (volume (V w)).toReal = (volume (V 0)).toReal := by
    intro w; rw [hVreal w, hVreal 0]
  calc (((triadicIndexBox d n).card : ℝ))⁻¹ *
        ∑ w ∈ triadicIndexBox d n,
          blockVecDot (cellAverageFamily q t X n w) (cellAverageFamily q t X n w)
      ≤ (((triadicIndexBox d n).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d n, ((volume (V 0)).toReal⁻¹ * ∫ x in V w, f x) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum ?_) (le_of_lt (inv_pos.mpr hNpos))
        intro w hw
        have := hJ w hw
        rwa [hVconst w] at this
    _ = ((((triadicIndexBox d n).card : ℝ)) * (volume (V 0)).toReal)⁻¹ *
          ∑ w ∈ triadicIndexBox d n, ∫ x in V w, f x := by
        rw [← Finset.mul_sum, mul_inv]
        ring
    _ ≤ ((((triadicIndexBox d n).card : ℝ)) * (volume (V 0)).toReal)⁻¹ * ∫ x in U, f x := by
        refine mul_le_mul_of_nonneg_left hsumle ?_
        rw [hprod]
        exact le_of_lt (inv_pos.mpr hUpos)
    _ = cellMeanSq U X := by
        rw [hprod]
        rfl

/-! ## The geometric majorant -/

omit [NeZero d] in
theorem three_rpow_scale_split (t : ℤ) (n : ℕ) :
    (3 : ℝ) ^ (((t : ℝ) - (n : ℝ)) / 2)
      = (3 : ℝ) ^ ((t : ℝ) / 2) * ((3 : ℝ) ^ (-(1 / 2 : ℝ))) ^ n := by
  rw [← Real.rpow_natCast ((3 : ℝ) ^ (-(1 / 2 : ℝ))) n,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  congr 1
  ring

omit [NeZero d] in
theorem besovRatio_lt_one : (3 : ℝ) ^ (-(1 / 2 : ℝ)) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)

omit [NeZero d] in
theorem besovRatio_nonneg : (0 : ℝ) ≤ (3 : ℝ) ^ (-(1 / 2 : ℝ)) :=
  Real.rpow_nonneg (by norm_num) _

omit [NeZero d] in
/-- The geometric majorant of the scale terms (`avsum_cellAverageFamily_sq_le` +
monotonicity of `sqrt`). -/
theorem besov_term_le (q : Mat d) (hq : IsUnit q) (t : ℤ)
    (X : Vec d → BlockVec d) (hX : MemLp (fun x => blockVecDot (X x) (X x)) 1
      (volume.restrict (HighContrast.adaptedCell q t))) (n : ℕ) :
    (3 : ℝ) ^ (((t : ℝ) - (n : ℝ)) / 2) *
        Real.sqrt ((((triadicIndexBox d n).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d n,
            blockVecDot (cellAverageFamily q t X n w) (cellAverageFamily q t X n w))
      ≤ (3 : ℝ) ^ ((t : ℝ) / 2) * Real.sqrt (cellMeanSq (HighContrast.adaptedCell q t) X) *
          ((3 : ℝ) ^ (-(1 / 2 : ℝ))) ^ n := by
  have hA : Real.sqrt ((((triadicIndexBox d n).card : ℝ))⁻¹ *
      ∑ w ∈ triadicIndexBox d n,
        blockVecDot (cellAverageFamily q t X n w) (cellAverageFamily q t X n w))
      ≤ Real.sqrt (cellMeanSq (HighContrast.adaptedCell q t) X) :=
    Real.sqrt_le_sqrt (avsum_cellAverageFamily_sq_le q hq t X hX n)
  have h1 : (0 : ℝ) ≤ (3 : ℝ) ^ ((t : ℝ) / 2) * ((3 : ℝ) ^ (-(1 / 2 : ℝ))) ^ n := by
    have := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) ((t : ℝ) / 2)
    have h2 : (0 : ℝ) ≤ ((3 : ℝ) ^ (-(1 / 2 : ℝ))) ^ n := pow_nonneg besovRatio_nonneg n
    exact mul_nonneg this h2
  rw [three_rpow_scale_split t n]
  calc (3 : ℝ) ^ ((t : ℝ) / 2) * ((3 : ℝ) ^ (-(1 / 2 : ℝ))) ^ n *
        Real.sqrt ((((triadicIndexBox d n).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d n,
            blockVecDot (cellAverageFamily q t X n w) (cellAverageFamily q t X n w))
      ≤ (3 : ℝ) ^ ((t : ℝ) / 2) * ((3 : ℝ) ^ (-(1 / 2 : ℝ))) ^ n *
          Real.sqrt (cellMeanSq (HighContrast.adaptedCell q t) X) :=
        mul_le_mul_of_nonneg_left hA h1
    _ = (3 : ℝ) ^ ((t : ℝ) / 2) * Real.sqrt (cellMeanSq (HighContrast.adaptedCell q t) X) *
          ((3 : ℝ) ^ (-(1 / 2 : ℝ))) ^ n := by ring

/-! ## Summability of the scale-term series -/

omit [NeZero d] in
/-- The series defining `besovSeminorm` is summable for an `L²(U_t)` field. -/
theorem summable_besov_cellAverageFamily (q : Mat d) (hq : IsUnit q) (t : ℤ)
    (X : Vec d → BlockVec d) (hX : MemLp (fun x => blockVecDot (X x) (X x)) 1
      (volume.restrict (HighContrast.adaptedCell q t))) :
    Summable fun n : ℕ => (3 : ℝ) ^ (((t : ℝ) - (n : ℝ)) / 2) *
      Real.sqrt ((((triadicIndexBox d n).card : ℝ))⁻¹ *
        ∑ w ∈ triadicIndexBox d n,
          blockVecDot (cellAverageFamily q t X n w) (cellAverageFamily q t X n w)) := by
  refine Summable.of_nonneg_of_le (fun n => ?_)
    (fun n => besov_term_le q hq t X hX n)
    ((summable_geometric_of_lt_one besovRatio_nonneg besovRatio_lt_one).mul_left
      ((3 : ℝ) ^ ((t : ℝ) / 2) * Real.sqrt (cellMeanSq (HighContrast.adaptedCell q t) X)))
  exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.sqrt_nonneg _)



end

end Homogenization.HighContrast.Multiscale
