import HCPoly.Entry.Multiscale.ResponseInputs.AdapterBasic

open Homogenization.HighContrast (blockScale blockVecDot_blockMatVecMul_eq_sum)
namespace Homogenization.HighContrast.Multiscale.Adapter

open MeasureTheory

/-- If each fine row's weight below a cap is bounded by a geometrically decaying multiple `D *
3 ^ (t - n)` of a base scale, the row-weighted geometric sum over all indices below the cap is
summable and bounded by the total mass `D` times the geometric series constant, evaluated at the
cap. -/
theorem fine_weight_bound {ι : Type*} [Countable ι]
    (w : ι → ℝ) (r : ι → ℤ) (hw0 : ∀ i, 0 ≤ w i) (hw : Summable w)
    (cap n : ℤ) (D : ℝ) (hD : 0 ≤ D)
    (hrow : ∀ t < cap, (∑' i : {i // r i = t}, w i) ≤ D * (3 : ℝ) ^ ((t : ℝ) - n))
    (γ : ℝ) (hγ : γ < 1) :
    Summable (fun i : {i // r i < cap} => w i * (3 : ℝ) ^ (γ * ((cap : ℝ) - r i))) ∧
      (∑' i : {i // r i < cap}, w i * (3 : ℝ) ^ (γ * ((cap : ℝ) - r i))) ≤
        D / (1 - (3 : ℝ) ^ (-(1 - γ))) * (3 : ℝ) ^ (-((n : ℝ) - cap)) := by
  let L := {i // r i < cap}
  have hwL : Summable (fun i : L => w i) := hw.subtype _
  apply Annealed.bridge_fine_weighted_sum (fun i : L => w i) (fun i => r i)
    (fun i => hw0 i) hwL cap n (fun i => i.2) D hD _ γ hγ
  intro t
  by_cases ht : t < cap
  · let e : {i : L // r i = t} → {i // r i = t} := fun i => ⟨i.1.1, i.2⟩
    have he : Function.Injective e := by
      intro i k h
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun x : {i // r i = t} => x.1) h
    exact (Summable.tsum_le_tsum_of_inj e he (fun i _ => hw0 i)
      (fun _ => le_rfl) (hwL.subtype _) (hw.subtype _)).trans (hrow t ht)
  · have : IsEmpty {i : L // r i = t} := ⟨fun i => ht (i.2 ▸ i.1.2)⟩
    simp only [tsum_empty]
    positivity

/-- A weighted finite sum `∑ w i * f i` splits by whether the row index reaches the cap: the
at-cap terms are bounded using the total mass `≤ 1` and the cap bound `a`, and the below-cap
terms are bounded using the geometric weighted-sum bound `T` from `fine_weight_bound`, together
giving `a + c * T * b`. -/
theorem finite_cap_sum {ι : Type*}
    (w : ι → ℝ) (r : ι → ℤ) (f : ι → ℝ)
    (hw0 : ∀ i, 0 ≤ w i) (hw : Summable w) (hmass : (∑' i, w i) ≤ 1)
    (cap : ℤ) (hr : ∀ i, r i ≤ cap) (γ a b c T : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hcap : ∀ i, r i = cap → f i ≤ a)
    (hlow : ∀ i, r i < cap → f i ≤ c * (3 : ℝ) ^ (γ * ((cap : ℝ) - r i)) * b)
    (hs : Summable (fun i : {i // r i < cap} => w i * (3 : ℝ) ^ (γ * ((cap : ℝ) - r i))))
    (ht : (∑' i : {i // r i < cap}, w i * (3 : ℝ) ^ (γ * ((cap : ℝ) - r i))) ≤ T)
    (F : Finset ι) :
    (∑ i ∈ F, w i * f i) ≤ a + c * T * b := by
  classical
  have htop : (∑ i ∈ F with ¬ r i < cap, w i * f i) ≤ a := by
    calc
      _ ≤ ∑ i ∈ F with ¬ r i < cap, w i * a := Finset.sum_le_sum (fun i hi =>
        mul_le_mul_of_nonneg_left (hcap i (by have := (Finset.mem_filter.mp hi).2; have := hr i; omega)) (hw0 i))
      _ = (∑ i ∈ F with ¬ r i < cap, w i) * a := (Finset.sum_mul ..).symm
      _ ≤ 1 * a := mul_le_mul_of_nonneg_right
        ((hw.sum_le_tsum _ (fun i _ => hw0 i)).trans hmass) ha
      _ = a := one_mul a
  have htail : (∑ i ∈ F with r i < cap, w i * f i) ≤ c * T * b := by
    have hsum := hs.sum_le_tsum (F.subtype (fun i => r i < cap)) (fun i _ =>
      mul_nonneg (hw0 i) (Real.rpow_nonneg (by norm_num) _))
    rw [Finset.sum_subtype_eq_sum_filter
      (f := fun i => w i * (3 : ℝ) ^ (γ * ((cap : ℝ) - r i)))] at hsum
    calc
      _ ≤ ∑ i ∈ F with r i < cap, w i *
          (c * (3 : ℝ) ^ (γ * ((cap : ℝ) - r i)) * b) :=
        Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left
          (hlow i (Finset.mem_filter.mp hi).2) (hw0 i))
      _ = c * (∑ i ∈ F with r i < cap, w i * (3 : ℝ) ^ (γ * ((cap : ℝ) - r i))) * b := by
        rw [Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ ≤ c * T * b := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hsum.trans ht) hc) hb
  calc
    _ = (∑ i ∈ F with r i < cap, w i * f i) +
        (∑ i ∈ F with ¬ r i < cap, w i * f i) :=
      (Finset.sum_filter_add_sum_filter_not F (fun i => r i < cap) _).symm
    _ ≤ c * T * b + a := add_le_add htail htop
    _ = a + c * T * b := add_comm _ _

/-- The doubled quadratic form `v. (1/2) A v` is additive in the block matrix `A`. -/
theorem quadratic_add {d : ℕ} (M N : FullBlockMat d) (v : BlockVec d) :
    (1 / 2 : ℝ) * blockVecDot v (blockMatVecMul (ofFullBlockMat (M + N)) v) =
      (1 / 2 : ℝ) * blockVecDot v (blockMatVecMul (ofFullBlockMat M) v) +
      (1 / 2 : ℝ) * blockVecDot v (blockMatVecMul (ofFullBlockMat N) v) := by
  simp only [blockVecDot_blockMatVecMul_eq_sum, blockMatEntry_ofFullBlockMat,
    Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

/-- The doubled quadratic form `v. (1/2) A v` is nonnegative when `A` is positive definite. -/
theorem quadratic_nonneg {d : ℕ} {A : BlockMat d}
    (hA : Book.Ch02.BlockPosDef A) (v : BlockVec d) :
    0 ≤ (1 / 2 : ℝ) * blockVecDot v (blockMatVecMul A v) := by
  by_cases hv : v = 0
  · simp [hv, blockVecDot, vecDot]
  · exact mul_nonneg (by norm_num) (hA v hv).le

/-- The doubled quadratic form `v. (1/2) A v` scales linearly under scalar multiplication of
`A`. -/
theorem quadratic_smul {d : ℕ} (c : ℝ) (M : FullBlockMat d) (v : BlockVec d) :
    (1 / 2 : ℝ) * blockVecDot v (blockMatVecMul (ofFullBlockMat (c • M)) v) =
      c * ((1 / 2 : ℝ) * blockVecDot v (blockMatVecMul (ofFullBlockMat M) v)) :=
  Source.quadratic_blockScale c (ofFullBlockMat M) v

/-- The block-matrix specialization of `finite_cap_sum`, via the quadratic form: a weighted sum
of blocks `B i`, each Loewner-bounded by `A` at the cap and by a geometrically decaying multiple
of `E` below the cap, is itself Loewner-bounded by `A + (c * T) • E`. -/
theorem finite_block_cap {d : ℕ} {ι : Type*}
    (w : ι → ℝ) (r : ι → ℤ) (B : ι → BlockMat d) (A E : BlockMat d)
    (hw0 : ∀ i, 0 ≤ w i) (hw : Summable w) (hmass : (∑' i, w i) ≤ 1)
    (cap : ℤ) (hr : ∀ i, r i ≤ cap) (γ c T : ℝ)
    (hA : Book.Ch02.BlockPosDef A) (hE : Book.Ch02.BlockPosDef E) (hc : 0 ≤ c)
    (hcap : ∀ i, r i = cap → BlockMatLoewnerLE (B i) A)
    (hlow : ∀ i, r i < cap →
      BlockMatLoewnerLE (B i) (blockScale (c * (3 : ℝ) ^ (γ * ((cap : ℝ) - r i))) E))
    (hs : Summable (fun i : {i // r i < cap} => w i * (3 : ℝ) ^ (γ * ((cap : ℝ) - r i))))
    (ht : (∑' i : {i // r i < cap}, w i * (3 : ℝ) ^ (γ * ((cap : ℝ) - r i))) ≤ T)
    (F : Finset ι) :
    BlockMatLoewnerLE (ofFullBlockMat (∑ i ∈ F, w i • toFullBlockMat (B i)))
      (ofFullBlockMat (toFullBlockMat A + (c * T) • toFullBlockMat E)) := by
  intro v
  rw [Annealed.bridge_quadratic_sum, quadratic_add, quadratic_smul]
  simp only [quadratic_smul, ofFullBlockMat_toFullBlockMat]
  exact finite_cap_sum w r
    (fun i => (1 / 2 : ℝ) * blockVecDot v (blockMatVecMul (B i) v))
    hw0 hw hmass cap hr γ _ _ c T (quadratic_nonneg hA v) (quadratic_nonneg hE v) hc
    (fun i hi => hcap i hi v)
    (fun i hi => by simpa only [Source.quadratic_blockScale] using hlow i hi v) hs ht F

end Homogenization.HighContrast.Multiscale.Adapter
