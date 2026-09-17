import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakRecentDecomp

/-!
# The centred scale term is dominated by the uncentred one

At each depth the flat average over the depth-`n` subcells of the recentred transported cell
averages is compared with the same average of the uncentred ones.  Since the flat average of the
subcell averages is the parent average (an equal-volume partition), this is the elementary
identity "the mean square distance from the mean is the second moment minus the square of the
mean".  This file proves the purely algebraic inequality over an arbitrary finite index set, and
then its instance at the estimate's carriers, where the metric transport `R` is applied first.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]

/-! ## Bilinearity helpers -/

omit [NeZero d] in
/-- The doubled pairing against the zero vector vanishes. -/
private theorem h6av_blockVecDot_zero_left (m : BlockVec d) :
    blockVecDot (0 : BlockVec d) m = 0 := by
  change blockVecDot ((0 : Vec d), (0 : Vec d)) m = 0
  simp [blockVecDot, vecDot]

omit [NeZero d] in
/-- The doubled pairing is additive in its first argument, hence linear over a finite sum. -/
private theorem h6av_blockVecDot_finset_sum_left {ι : Type*} (Z : Finset ι)
    (y : ι → BlockVec d) (m : BlockVec d) :
    blockVecDot (∑ w ∈ Z, y w) m = ∑ w ∈ Z, blockVecDot (y w) m := by
  classical
  induction Z using Finset.induction_on with
  | empty => simp [h6av_blockVecDot_zero_left]
  | insert a S ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, blockVecDot_add_left, ih]

omit [NeZero d] in
/-- The doubled pairing is additive in its first argument, including subtraction. -/
private theorem h6av_blockVecDot_sub_left (X Y Z : BlockVec d) :
    blockVecDot (X - Y) Z = blockVecDot X Z - blockVecDot Y Z := by
  rw [sub_eq_add_neg, blockVecDot_add_left]
  have hneg : blockVecDot (-Y) Z = -blockVecDot Y Z := by
    simpa using blockVecDot_smul_left (-1 : ℝ) Y Z
  rw [hneg]
  ring

omit [NeZero d] in
/-- Expanding the squared distance from the mean. -/
private theorem h6av_blockVecDot_sub_self_expand (X m : BlockVec d) :
    blockVecDot (X - m) (X - m)
      = blockVecDot X X - 2 * blockVecDot X m + blockVecDot m m := by
  rw [blockVecDot_sub_right, h6av_blockVecDot_sub_left, h6av_blockVecDot_sub_left,
    blockVecDot_comm m X]
  ring

omit [NeZero d] in
/-- The first component of a finite sum of doubled vectors is the sum of the first components. -/
private theorem h6av_fst_finset_sum {ι : Type*} (Z : Finset ι) (y : ι → BlockVec d) :
    (∑ w ∈ Z, y w).1 = ∑ w ∈ Z, (y w).1 := by
  classical
  induction Z using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      simp [ih]

omit [NeZero d] in
/-- The second component of a finite sum of doubled vectors is the sum of the second
components. -/
private theorem h6av_snd_finset_sum {ι : Type*} (Z : Finset ι) (y : ι → BlockVec d) :
    (∑ w ∈ Z, y w).2 = ∑ w ∈ Z, (y w).2 := by
  classical
  induction Z using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      simp [ih]

omit [NeZero d] in
/-- The zero doubled vector is annihilated by a block matrix. -/
private theorem h6av_blockMatVecMul_zero (A : BlockMat d) :
    blockMatVecMul A (0 : BlockVec d) = 0 := by
  change blockMatVecMul A ((0 : Vec d), (0 : Vec d)) = ((0 : Vec d), (0 : Vec d))
  simp [blockMatVecMul, matVecMul_zero]

omit [NeZero d] in
/-- A block matrix is additive, hence linear over a finite sum of doubled vectors. -/
private theorem h6av_blockMatVecMul_finset_sum {ι : Type*} (A : BlockMat d)
    (Z : Finset ι) (y : ι → BlockVec d) :
    (∑ w ∈ Z, blockMatVecMul A (y w)) = blockMatVecMul A (∑ w ∈ Z, y w) := by
  classical
  induction Z using Finset.induction_on with
  | empty => simp [h6av_blockMatVecMul_zero]
  | insert a S ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, blockMatVecMul_add, ih]

/-! ## The algebraic inequality -/

omit [NeZero d] in
/-- **Variance is at most the second moment.**  For a finite nonempty index set `Z`, a family of
doubled vectors `y` and a doubled vector `m` whose two components are the corresponding flat
averages of the family, the flat average of the squared distance from `m` is at most the flat
average of the squared norm.  This is
`E‖y - m‖² = E‖y‖² - ‖m‖² ≤ E‖y‖²`. -/
theorem h6a_avsum_blockVecDot_sub_mean_le {iota : Type*} (Z : Finset iota) (hZ : Z.Nonempty)
    (y : iota → BlockVec d) (m : BlockVec d)
    (hmean1 : ∀ i : Fin d, (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, (y w).1 i = m.1 i)
    (hmean2 : ∀ i : Fin d, (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, (y w).2 i = m.2 i) :
    (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, blockVecDot (y w - m) (y w - m)
      ≤ (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, blockVecDot (y w) (y w) := by
  classical
  have hcard : (Z.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr hZ)
  have havg : ∑ w ∈ Z, y w = (Z.card : ℝ) • m := by
    refine Prod.ext ?_ ?_
    · funext i
      have hS : (∑ w ∈ Z, y w).1 i = (Z.card : ℝ) * m.1 i := by
        have hfst : (∑ w ∈ Z, y w).1 i = ∑ w ∈ Z, (y w).1 i := by
          rw [congrFun (h6av_fst_finset_sum Z y) i, Finset.sum_apply]
        rw [hfst]
        have hc : (Z.card : ℝ) * ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, (y w).1 i)
            = ∑ w ∈ Z, (y w).1 i := by
          rw [← mul_assoc, mul_inv_cancel₀ hcard, one_mul]
        rw [← hc, hmean1 i]
      have hrhs : ((Z.card : ℝ) • m).1 i = (Z.card : ℝ) * m.1 i := by
        rw [Prod.smul_fst, Pi.smul_apply, smul_eq_mul]
      rw [hrhs]
      exact hS
    · funext i
      have hS : (∑ w ∈ Z, y w).2 i = (Z.card : ℝ) * m.2 i := by
        have hsnd : (∑ w ∈ Z, y w).2 i = ∑ w ∈ Z, (y w).2 i := by
          rw [congrFun (h6av_snd_finset_sum Z y) i, Finset.sum_apply]
        rw [hsnd]
        have hc : (Z.card : ℝ) * ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, (y w).2 i)
            = ∑ w ∈ Z, (y w).2 i := by
          rw [← mul_assoc, mul_inv_cancel₀ hcard, one_mul]
        rw [← hc, hmean2 i]
      have hrhs : ((Z.card : ℝ) • m).2 i = (Z.card : ℝ) * m.2 i := by
        rw [Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
      rw [hrhs]
      exact hS
  have hdot : ∑ w ∈ Z, blockVecDot (y w) m = (Z.card : ℝ) * blockVecDot m m := by
    rw [← h6av_blockVecDot_finset_sum_left Z y m, havg, blockVecDot_smul_left]
  have hsum_expand :
      ∑ w ∈ Z, blockVecDot (y w - m) (y w - m)
        = (∑ w ∈ Z, blockVecDot (y w) (y w)) - (Z.card : ℝ) * blockVecDot m m := by
    calc ∑ w ∈ Z, blockVecDot (y w - m) (y w - m)
        = ∑ w ∈ Z, (blockVecDot (y w) (y w) - 2 * blockVecDot (y w) m
            + blockVecDot m m) :=
          Finset.sum_congr rfl fun w _ => h6av_blockVecDot_sub_self_expand (y w) m
      _ = (∑ w ∈ Z, blockVecDot (y w) (y w)) - 2 * (∑ w ∈ Z, blockVecDot (y w) m)
            + (Z.card : ℝ) * blockVecDot m m := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
            Finset.sum_const, nsmul_eq_mul]
      _ = (∑ w ∈ Z, blockVecDot (y w) (y w)) - (Z.card : ℝ) * blockVecDot m m := by
          rw [hdot]
          ring
  rw [hsum_expand]
  have hP : (0 : ℝ) ≤ blockVecDot m m := blockVecDot_nonneg m
  have hmul : (Z.card : ℝ)⁻¹ * ((Z.card : ℝ) * blockVecDot m m) = blockVecDot m m := by
    rw [← mul_assoc, inv_mul_cancel₀ hcard, one_mul]
  have hrew : (Z.card : ℝ)⁻¹ * ((∑ w ∈ Z, blockVecDot (y w) (y w))
        - (Z.card : ℝ) * blockVecDot m m)
      = (Z.card : ℝ)⁻¹ * (∑ w ∈ Z, blockVecDot (y w) (y w)) - blockVecDot m m := by
    rw [mul_sub, hmul]
  rw [hrew]
  linarith

/-! ## The instance at the estimate's carriers -/

omit [NeZero d] in
/-- **The centred transported scale term is dominated by the uncentred one.**  Applying the
algebraic inequality to `y w = blockMatVecMul R ((X)_{V_w})` and
`m = blockMatVecMul R ((X)_U)`, with the parent-mean identity supplied as a hypothesis and the
metric transport `R` distributed over the difference by linearity. -/
theorem h6a_scaleTerm_centred_le (q : Mat d) (t : ℤ) (n : ℕ) (R : BlockMat d)
    (X : Vec d → BlockVec d)
    (hmean1 : ∀ i : Fin d, ((triadicIndexBox d n).card : ℝ)⁻¹ *
        ∑ w ∈ triadicIndexBox d n,
          (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) X).1 i
      = (cellAverage (HighContrast.adaptedCell q t) X).1 i)
    (hmean2 : ∀ i : Fin d, ((triadicIndexBox d n).card : ℝ)⁻¹ *
        ∑ w ∈ triadicIndexBox d n,
          (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) X).2 i
      = (cellAverage (HighContrast.adaptedCell q t) X).2 i) :
    ((triadicIndexBox d n).card : ℝ)⁻¹ *
        ∑ w ∈ triadicIndexBox d n,
          blockVecDot
            (blockMatVecMul R (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) X -
              cellAverage (HighContrast.adaptedCell q t) X))
            (blockMatVecMul R (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) X -
              cellAverage (HighContrast.adaptedCell q t) X))
      ≤ ((triadicIndexBox d n).card : ℝ)⁻¹ *
        ∑ w ∈ triadicIndexBox d n,
          blockVecDot
            (blockMatVecMul R (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) X))
            (blockMatVecMul R (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) X)) := by
  classical
  let Z : Finset (Fin d → ℤ) := triadicIndexBox d n
  let v : (Fin d → ℤ) → BlockVec d := fun w => cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) X
  let V : BlockVec d := cellAverage (HighContrast.adaptedCell q t) X
  have hZne : Z.Nonempty := by
    change (triadicIndexBox d n).Nonempty
    refine ⟨0, ?_⟩
    rw [triadicIndexBox, Fintype.mem_piFinset]
    intro i
    exact Finset.mem_Icc.mpr
      ⟨neg_nonpos.mpr (Int.natCast_nonneg _), Int.natCast_nonneg _⟩
  have havg : (Z.card : ℝ)⁻¹ • (∑ w ∈ Z, v w) = V := by
    refine Prod.ext ?_ ?_
    · funext i
      rw [Prod.smul_fst, Pi.smul_apply, smul_eq_mul]
      have hfst : (∑ w ∈ Z, v w).1 i = ∑ w ∈ Z, (v w).1 i := by
        rw [congrFun (h6av_fst_finset_sum Z v) i, Finset.sum_apply]
      rw [hfst]
      exact hmean1 i
    · funext i
      rw [Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
      have hsnd : (∑ w ∈ Z, v w).2 i = ∑ w ∈ Z, (v w).2 i := by
        rw [congrFun (h6av_snd_finset_sum Z v) i, Finset.sum_apply]
      rw [hsnd]
      exact hmean2 i
  let y : (Fin d → ℤ) → BlockVec d := fun w => blockMatVecMul R (v w)
  let m : BlockVec d := blockMatVecMul R V
  have hsumy : ∑ w ∈ Z, y w = blockMatVecMul R (∑ w ∈ Z, v w) :=
    h6av_blockMatVecMul_finset_sum R Z v
  have hm : (Z.card : ℝ)⁻¹ • (∑ w ∈ Z, y w) = m := by
    calc (Z.card : ℝ)⁻¹ • (∑ w ∈ Z, y w)
        = (Z.card : ℝ)⁻¹ • blockMatVecMul R (∑ w ∈ Z, v w) := by rw [hsumy]
      _ = blockMatVecMul R ((Z.card : ℝ)⁻¹ • (∑ w ∈ Z, v w)) :=
            (blockMatVecMul_smul R (Z.card : ℝ)⁻¹ (∑ w ∈ Z, v w)).symm
      _ = blockMatVecMul R V := by rw [havg]
      _ = m := rfl
  have hy1 : ∀ i : Fin d, (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, (y w).1 i = m.1 i := by
    intro i
    have hcomp : ((Z.card : ℝ)⁻¹ • (∑ w ∈ Z, y w)).1 i = m.1 i :=
      congrArg (fun z : BlockVec d => z.1 i) hm
    have h2 : ((Z.card : ℝ)⁻¹ • (∑ w ∈ Z, y w)).1 i
        = (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, (y w).1 i := by
      rw [Prod.smul_fst, Pi.smul_apply, smul_eq_mul,
        congrFun (h6av_fst_finset_sum Z y) i, Finset.sum_apply]
    rw [h2] at hcomp
    exact hcomp
  have hy2 : ∀ i : Fin d, (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, (y w).2 i = m.2 i := by
    intro i
    have hcomp : ((Z.card : ℝ)⁻¹ • (∑ w ∈ Z, y w)).2 i = m.2 i :=
      congrArg (fun z : BlockVec d => z.2 i) hm
    have h2 : ((Z.card : ℝ)⁻¹ • (∑ w ∈ Z, y w)).2 i
        = (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, (y w).2 i := by
      rw [Prod.smul_snd, Pi.smul_apply, smul_eq_mul,
        congrFun (h6av_snd_finset_sum Z y) i, Finset.sum_apply]
    rw [h2] at hcomp
    exact hcomp
  have hbase : (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, blockVecDot (y w - m) (y w - m)
      ≤ (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, blockVecDot (y w) (y w) :=
    h6a_avsum_blockVecDot_sub_mean_le Z hZne y m hy1 hy2
  have hsum_eq : (∑ w ∈ Z, blockVecDot (blockMatVecMul R (v w - V))
        (blockMatVecMul R (v w - V)))
      = ∑ w ∈ Z, blockVecDot (y w - m) (y w - m) := by
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [blockMatVecMul_sub_vec]
  calc (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, blockVecDot (blockMatVecMul R (v w - V))
          (blockMatVecMul R (v w - V))
      = (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, blockVecDot (y w - m) (y w - m) := by rw [hsum_eq]
    _ ≤ (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, blockVecDot (y w) (y w) := hbase
    _ = (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, blockVecDot (blockMatVecMul R (v w))
          (blockMatVecMul R (v w)) := rfl

end

end Homogenization.HighContrast.Multiscale
