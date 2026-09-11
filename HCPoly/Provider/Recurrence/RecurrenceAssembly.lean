/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Recurrence.FiniteRangeAveraging
import HCPoly.Provider.Recurrence.PositiveGapClosure

/-!
# `p.fixed.geometry.parent.child.recurrence`

The fixed-grid recurrence is assembled here from the estimates of the section.
On one deterministic rounded adapted grid `q` of alignment `ℓ`, at a child scale
`j ≥ ℓ` and a parent scale `p = j + h` above it, the parent cell is partitioned
by `3^{dh}` aligned children; write `Ĝ` for the average of the responses over
those children, `E_j` and `E_p` for the two adapted means and
`Δ = Δ_{j,p}^q` for the determinant increment.

Four displays are composed.

*The averaging step.*  The centred average `Ĝ - E_j`, normalized by the child
mean, has mixed norm at most `C(d,Q) 3^{-hd/2}` times the child moment `v_j^q`;
this is `l.fixed.geometry.matrix.averaging` read at the aligned subdivision,
whose cardinality `3^{dh}` supplies the printed gain.

*The transport of the normalization.*  The mean order `E_p ≤ E_j` and the ideal
property of the Schatten norm carry that estimate from the child normalization
to the parent one, at the cost of `(2d)^{1/Q}e^{Δ}`.

*The positive gap.*  Pathwise `0 ≤ 𝐀_p ≤ Ĝ`, so the normalized excess
`D = (Ĝ - 𝐀_p)^~` is positive with mean `B = P_{j,p}^q - I`; the determinant
transport bounds the spectral size of `P_{j,p}^q` by `e^{Δ}` and its trace gap by
`e^{Δ} - 1`.  The positive-gap estimate then bounds the parent moment by
`C(y + Φ_Q(Δ))`, where `y` is the transported mixed norm of the centred average.

*The gain.*  Substituting the transported bound for `y` produces the printed
contraction: a geometric factor `3^{-hd/2}e^{Δ}` on the child moment plus the
increment's own gain `Φ_Q(Δ)`, both carrying one constant `C_rec(d, Q)`.

The mixed norms are `ℝ≥0∞`-valued, and the passage to the real inequalities the
positive-gap estimate is stated in is made on the finiteness hypotheses the
proposition carries.  The exponent `Q` is an even integer, which is what makes
the Schatten size a continuous function of the entries: the inner power `Q/2` of
`|H|_{S_Q} = (tr((H²)^{Q/2}))^{1/Q}` is then an integer, the functional calculus
collapses to a matrix power and the trace is a polynomial.  That is the content
of the opening section.
-/

namespace Homogenization
namespace HighContrast
namespace Recurrence

open MeasureTheory

open scoped ENNReal MatrixOrder Matrix.Norms.L2Operator Matrix

noncomputable section

variable {d : ℕ}

/-! ## Measurability of the Schatten size at an even exponent -/

section Entries

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The entries of a matrix power are polynomials in the entries. -/
theorem aestronglyMeasurable_entry_pow {F : Ω → Matrix n n ℝ}
    (h : ∀ i j, AEStronglyMeasurable (fun a => F a i j) μ) :
    ∀ (k : ℕ) (i j : n), AEStronglyMeasurable (fun a => (F a ^ k) i j) μ := by
  intro k
  induction k with
  | zero =>
      intro i j
      simp only [pow_zero]
      exact aestronglyMeasurable_const
  | succ k ih =>
      intro i j
      simp only [pow_succ]
      exact aestronglyMeasurable_entry_mul ih h i j

omit [DecidableEq n] in
/-- The entries of a two-sided constant congruence are linear in the entries. -/
theorem aestronglyMeasurable_entry_conj (S : Matrix n n ℝ) {F : Ω → Matrix n n ℝ}
    (h : ∀ i j, AEStronglyMeasurable (fun a => F a i j) μ) (i j : n) :
    AEStronglyMeasurable (fun a => (S * F a * S) i j) μ := by
  have hS : ∀ i j : n, AEStronglyMeasurable (fun _ : Ω => S i j) μ :=
    fun _ _ => aestronglyMeasurable_const
  have hSF : ∀ i j : n, AEStronglyMeasurable (fun a => (S * F a) i j) μ :=
    aestronglyMeasurable_entry_mul (F := fun _ => S) (G := F) hS h
  exact aestronglyMeasurable_entry_mul (F := fun a => S * F a) (G := fun _ => S) hSF hS i j

end Entries

/-- The entries of a normalized difference of two random doubled blocks are
measurable as soon as the entries of the two blocks are: normalization and
subtraction are a fixed real-linear map of the entries. -/
theorem aestronglyMeasurable_entry_normalizedBlock_blockSub {P : Measure (CoeffSpace d)}
    {X Y : CoeffSpace d → BlockMat d} (F : BlockMat d)
    (hX : ∀ α β : BlockCoord d, AEStronglyMeasurable (fun a => toFullBlockMat (X a) α β) P)
    (hY : ∀ α β : BlockCoord d, AEStronglyMeasurable (fun a => toFullBlockMat (Y a) α β) P)
    (α β : BlockCoord d) :
    AEStronglyMeasurable
      (fun a => toFullBlockMat (normalizedBlock (blockSub (X a) (Y a)) F) α β) P := by
  have hsub : ∀ γ δ : BlockCoord d, AEStronglyMeasurable
      (fun a => (toFullBlockMat (X a) - toFullBlockMat (Y a)) γ δ) P := by
    intro γ δ
    simpa only [Matrix.sub_apply] using (hX γ δ).sub (hY γ δ)
  have hfun : (fun a : CoeffSpace d =>
        toFullBlockMat (normalizedBlock (blockSub (X a) (Y a)) F) α β)
      = fun a : CoeffSpace d => (matSqrt (toFullBlockMat F)⁻¹ *
          (toFullBlockMat (X a) - toFullBlockMat (Y a)) *
          matSqrt (toFullBlockMat F)⁻¹) α β := by
    funext a
    rw [toFullBlockMat_normalizedBlock, toFullBlockMat_blockSub]
  rw [hfun]
  exact aestronglyMeasurable_entry_conj _ hsub α β

/-- The trace of a random doubled block is measurable as soon as its entries
are. -/
theorem aestronglyMeasurable_blockTrace {P : Measure (CoeffSpace d)}
    {W : CoeffSpace d → BlockMat d}
    (hW : ∀ α β : BlockCoord d, AEStronglyMeasurable (fun a => toFullBlockMat (W a) α β) P) :
    AEStronglyMeasurable (fun a => blockTrace (W a)) P := by
  simp only [blockTrace, Matrix.trace, Matrix.diag]
  exact Finset.aestronglyMeasurable_fun_sum _ fun i _ => hW i i

/-- At an even natural exponent the Schatten trace of a self-adjoint matrix is
the trace of a matrix power: the spectral power `x ↦ x^{Q/2}` is then a natural
power, and the functional calculus of a natural power is that power. -/
theorem trace_cfc_rpow_eq_trace_pow {A : FullBlockMat d} (hA : IsSelfAdjoint A) {Q : ℕ}
    (hQ : Even Q) :
    Matrix.trace (cfc (fun x : ℝ => x ^ ((Q : ℝ) / 2)) A) = Matrix.trace (A ^ (Q / 2)) := by
  obtain ⟨m, hm⟩ := hQ
  have hmnat : Q / 2 = m := by omega
  have hmR : (Q : ℝ) / 2 = (m : ℝ) := by
    have hcast : (Q : ℝ) = (m : ℝ) + (m : ℝ) := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) hm
    rw [hcast]
    ring
  have hfun : (fun x : ℝ => x ^ ((Q : ℝ) / 2)) = fun x : ℝ => x ^ (m : ℕ) := by
    funext x
    rw [hmR, Real.rpow_natCast]
  have hpow := cfc_pow (R := ℝ) (fun x : ℝ => x) m A
  rw [cfc_id' ℝ A hA] at hpow
  rw [hfun, hpow, hmnat]

/-- **The Schatten size at an even exponent is an algebraic function of the
entries**: `|H|_{S_Q} = (tr((H²)^{Q/2}))^{1/Q}` with `Q/2` an integer power. -/
theorem schattenNorm_natCast_eq {H : BlockMat d} (hH : IsSymmetricBlockMat H) {Q : ℕ}
    (hQ : Even Q) :
    schattenNorm (Q : ℝ) H =
      Matrix.trace ((toFullBlockMat H * toFullBlockMat H) ^ (Q / 2)) ^ ((Q : ℝ))⁻¹ := by
  rw [schattenNorm,
    trace_cfc_rpow_eq_trace_pow (isSelfAdjoint_mul_self (isSelfAdjoint_toFullBlockMat hH)) hQ]

/-- **The Schatten size of a random symmetric doubled block is measurable** at an
even exponent, with no hypothesis beyond measurability of the entries: the
Schatten trace is then a polynomial in them and the `Q`-th root is continuous. -/
theorem aestronglyMeasurable_schattenNorm {P : Measure (CoeffSpace d)}
    {H : CoeffSpace d → BlockMat d} (hH : ∀ a, IsSymmetricBlockMat (H a)) {Q : ℕ}
    (hQeven : Even Q)
    (hmeas : ∀ α β : BlockCoord d,
      AEStronglyMeasurable (fun a => toFullBlockMat (H a) α β) P) :
    AEStronglyMeasurable (fun a => schattenNorm (Q : ℝ) (H a)) P := by
  have hsq : ∀ α β : BlockCoord d, AEStronglyMeasurable
      (fun a => (toFullBlockMat (H a) * toFullBlockMat (H a)) α β) P :=
    aestronglyMeasurable_entry_mul hmeas hmeas
  have hpow := aestronglyMeasurable_entry_pow hsq (Q / 2)
  have htr : AEStronglyMeasurable
      (fun a => Matrix.trace ((toFullBlockMat (H a) * toFullBlockMat (H a)) ^ (Q / 2))) P := by
    simp only [Matrix.trace, Matrix.diag]
    exact Finset.aestronglyMeasurable_fun_sum _ fun i _ => hpow i i
  have hcont : Continuous fun t : ℝ => t ^ ((Q : ℝ))⁻¹ :=
    continuous_iff_continuousAt.mpr fun t =>
      Real.continuousAt_rpow_const t _ (Or.inr (by positivity))
  exact (hcont.comp_aestronglyMeasurable htr).congr
    (Filter.Eventually.of_forall fun a => (schattenNorm_natCast_eq (hH a) hQeven).symm)

/-! ## The recurrence -/

/-- **`p.fixed.geometry.parent.child.recurrence`.**  On one rounded adapted grid, at scales at
or above its alignment, the centred normalized moment at the parent scale is
controlled by a geometric contraction of the moment at the child scale,
transported by the determinant increment, plus the increment's own gain. -/
theorem fixed_grid_recurrence_assembly
    (d : ℕ) (hd : 2 ≤ d) (Q : ℕ) (hQ : 2 ≤ Q) (hQeven : Even Q) :
    ∃ Crec : ℝ, 0 < Crec ∧
      ∀ (P : MeasureTheory.Measure (Homogenization.HighContrast.CoeffSpace d)),
        MeasureTheory.IsProbabilityMeasure P →
        HCPoly.Frozen.IsStationaryLaw P →
        HCPoly.Frozen.IsUnitRangeLaw P →
        ∀ (l : ℤ) (q : Homogenization.Mat d),
          Homogenization.HighContrast.IsRoundedGrid l q →
          ∀ j h : ℤ, l ≤ j → 1 ≤ h →
            Homogenization.Book.Ch02.BlockPosDef
              (Homogenization.HighContrast.adaptedMean P q j) →
            Homogenization.Book.Ch02.BlockPosDef
              (Homogenization.HighContrast.adaptedMean P q (j + h)) →
            Homogenization.HighContrast.HasFiniteAdaptedMean P q j →
            Homogenization.HighContrast.HasFiniteAdaptedMean P q (j + h) →
            Homogenization.HighContrast.centeredMoment P (Q : ℝ) q j ≠ ⊤ →
            Homogenization.HighContrast.centeredMoment P (Q : ℝ) q (j + h) ≠ ⊤ →
            0 ≤ Homogenization.HighContrast.detIncrement P q j (j + h) ∧
              Homogenization.HighContrast.centeredMoment P (Q : ℝ) q (j + h) ≤
                ENNReal.ofReal
                    (Crec * (3 : ℝ) ^ (-(h : ℝ) * (d : ℝ) / 2) *
                      Real.exp
                        (Homogenization.HighContrast.detIncrement P q j (j + h))) *
                  Homogenization.HighContrast.centeredMoment P (Q : ℝ) q j +
                ENNReal.ofReal
                  (Crec *
                    Homogenization.HighContrast.gainPhi (Q : ℝ)
                      (Homogenization.HighContrast.detIncrement P q j (j + h)))
    := by
  have hd0 : 0 < d := by omega
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
  have h2d : (0 : ℝ) < (2 * d : ℝ) := by linarith only [hdR]
  have hQR : (2 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
  have hQ1 : (1 : ℝ) ≤ (Q : ℝ) := by linarith only [hQR]
  have hQ0 : (0 : ℝ) < (Q : ℝ) := by linarith only [hQR]
  have hKK : (0 : ℝ) < (2 * d : ℝ) ^ ((Q : ℝ))⁻¹ := Real.rpow_pos_of_pos h2d _
  have hCC : (0 : ℝ) <
      (2 : ℝ) ^ ((Q : ℝ) - 2) * (2 * d : ℝ) ^ (1 - ((Q : ℝ))⁻¹) :=
    mul_pos (Real.rpow_pos_of_pos (by norm_num) _) (Real.rpow_pos_of_pos h2d _)
  have hCgap : (0 : ℝ) < (2 * d : ℝ) ^ ((Q : ℝ))⁻¹ *
      (1 + (2 * ((2 : ℝ) ^ ((Q : ℝ) - 2) * (2 * d : ℝ) ^ (1 - ((Q : ℝ))⁻¹))) ^ ((Q : ℝ))⁻¹ +
        (2 * ((2 : ℝ) ^ ((Q : ℝ) - 2) *
          (2 * d : ℝ) ^ (1 - ((Q : ℝ))⁻¹))) ^ ((Q : ℝ) - 1)⁻¹) := by
    refine mul_pos hKK ?_
    have h1 : (0 : ℝ) ≤
        (2 * ((2 : ℝ) ^ ((Q : ℝ) - 2) * (2 * d : ℝ) ^ (1 - ((Q : ℝ))⁻¹))) ^ ((Q : ℝ))⁻¹ :=
      Real.rpow_nonneg (by linarith only [hCC]) _
    have h2 : (0 : ℝ) ≤
        (2 * ((2 : ℝ) ^ ((Q : ℝ) - 2) *
          (2 * d : ℝ) ^ (1 - ((Q : ℝ))⁻¹))) ^ ((Q : ℝ) - 1)⁻¹ :=
      Real.rpow_nonneg (by linarith only [hCC]) _
    linarith only [h1, h2]
  have hCAA : (0 : ℝ) ≤ 2 * (d : ℝ) *
      ((2 * (Q : ℝ) + 4 * IndependentSums.rosenthalBennettIntegralConst *
        Real.sqrt (Q : ℝ)) * Real.sqrt ((3 : ℝ) ^ d)) := by
    have hconst : (0 : ℝ) ≤ IndependentSums.rosenthalBennettIntegralConst := by
      simp only [IndependentSums.rosenthalBennettIntegralConst]
      positivity
    have hterm : (0 : ℝ) ≤ 4 * IndependentSums.rosenthalBennettIntegralConst *
        Real.sqrt (Q : ℝ) :=
      mul_nonneg (by linarith only [hconst]) (Real.sqrt_nonneg _)
    exact mul_nonneg (by linarith only [hdR])
      (mul_nonneg (by linarith only [hQ0, hterm]) (Real.sqrt_nonneg _))
  refine ⟨(2 * d : ℝ) ^ ((Q : ℝ))⁻¹ *
      (1 + (2 * ((2 : ℝ) ^ ((Q : ℝ) - 2) * (2 * d : ℝ) ^ (1 - ((Q : ℝ))⁻¹))) ^ ((Q : ℝ))⁻¹ +
        (2 * ((2 : ℝ) ^ ((Q : ℝ) - 2) *
          (2 * d : ℝ) ^ (1 - ((Q : ℝ))⁻¹))) ^ ((Q : ℝ) - 1)⁻¹) *
      (1 + (2 * d : ℝ) ^ ((Q : ℝ))⁻¹ *
        (2 * (d : ℝ) * ((2 * (Q : ℝ) + 4 * IndependentSums.rosenthalBennettIntegralConst *
          Real.sqrt (Q : ℝ)) * Real.sqrt ((3 : ℝ) ^ d)))), ?_, ?_⟩
  · refine mul_pos hCgap ?_
    have hprod : (0 : ℝ) ≤ (2 * d : ℝ) ^ ((Q : ℝ))⁻¹ *
        (2 * (d : ℝ) * ((2 * (Q : ℝ) + 4 * IndependentSums.rosenthalBennettIntegralConst *
          Real.sqrt (Q : ℝ)) * Real.sqrt ((3 : ℝ) ^ d))) := mul_nonneg hKK.le hCAA
    linarith only [hprod]
  intro P hPprob hPstat hPunit l q hq j h hlj hh _hposj _hposp hfinj hfinp hmomj hmomp
  haveI := hPprob
  haveI : NeZero d := ⟨by omega⟩
  have hjp : j ≤ j + h := by omega
  have hqPD : q.PosDef := posDef_of_isRoundedGrid hq
  obtain ⟨-, hDelta, -, hrelnorm, hrelgap⟩ :=
    determinant_transport_adaptedMean hPstat hq hlj hjp hfinj hfinp
  refine ⟨hDelta, ?_⟩
  -- the two adapted means
  have hEj : (toFullBlockMat (adaptedMean P q j)).PosDef :=
    posDef_toFullBlockMat_adaptedMean hq j hfinj
  have hEp : (toFullBlockMat (adaptedMean P q (j + h))).PosDef :=
    posDef_toFullBlockMat_adaptedMean hq (j + h) hfinp
  -- the aligned subdivision and the average of the children's responses
  obtain ⟨Z, hZset, hZcard, -, -, -, -⟩ := aligned_subdivision hq hlj hjp
  have hZne : Z.Nonempty := by
    rw [← Finset.card_pos, hZcard]
    positivity
  set G : CoeffSpace d → BlockMat d := fun a => ofFullBlockMat ((Z.card : ℝ)⁻¹ •
    ∑ w ∈ Z, toFullBlockMat (coarseBlock (adaptedCellAt q j w) a))
  have hGsym : ∀ a, IsSymmetricBlockMat (G a) := fun a =>
    isSymmetricBlockMat_alignedAverage Z a
  have hGfull : ∀ a, toFullBlockMat (G a) =
      (Z.card : ℝ)⁻¹ • ∑ w ∈ Z, toFullBlockMat (coarseBlock (adaptedCellAt q j w) a) :=
    fun a => toFullBlockMat_ofFullBlockMat _
  have hGle : ∀ a, toFullBlockMat (coarseBlock (adaptedCell q (j + h)) a) ≤
      toFullBlockMat (G a) := by
    intro a
    rw [hGfull a]
    exact toFullBlockMat_coarseBlock_adaptedCell_le_average hqPD hjp hZset a
  have hGint : Integrable (fun a => toFullBlockMat (G a)) P := by
    have hsum : Integrable
        (fun a => ∑ w ∈ Z, toFullBlockMat (coarseBlock (adaptedCellAt q j w) a)) P :=
      integrable_finset_sum Z fun w _ =>
        integrable_toFullBlockMat_coarseBlock_adaptedCellAt hPstat hq hlj hfinj w
    simp only [hGfull]
    exact (hsum.smul ((Z.card : ℝ)⁻¹)).congr (Filter.Eventually.of_forall fun _ => rfl)
  have hGmean : ∫ a, toFullBlockMat (G a) ∂P = toFullBlockMat (adaptedMean P q j) := by
    simp only [hGfull]
    exact integral_alignedAverage_eq_adaptedMean hPstat hq hlj hfinj hZne
  have hGmeas : ∀ α β : BlockCoord d,
      AEStronglyMeasurable (fun a => toFullBlockMat (G a) α β) P := by
    intro α β
    have hfun : (fun a : CoeffSpace d => toFullBlockMat (G a) α β)
        = fun a : CoeffSpace d => (Z.card : ℝ)⁻¹ *
            ∑ w ∈ Z, toFullBlockMat (coarseBlock (adaptedCellAt q j w) a) α β := by
      funext a
      rw [hGfull a]
      simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
    rw [hfun]
    exact (Finset.aestronglyMeasurable_fun_sum _ fun w _ =>
      hasMeasurableCoarseBlock_adaptedCellAt P hqPD j w α β).const_mul _
  have hAmeas : ∀ α β : BlockCoord d, AEStronglyMeasurable
      (fun a => toFullBlockMat (coarseBlock (adaptedCell q (j + h)) a) α β) P :=
    fun α β => hasMeasurableCoarseBlock_adaptedCell P hqPD (j + h) α β
  -- the mean of the normalized excess
  have hBfull : toFullBlockMat
        (ofFullBlockMat (toFullBlockMat (relMean P q j (j + h)) - 1))
      = toFullBlockMat (relMean P q j (j + h)) - 1 := toFullBlockMat_ofFullBlockMat _
  have hBsym : IsSymmetricBlockMat
      (ofFullBlockMat (toFullBlockMat (relMean P q j (j + h)) - 1)) :=
    isSymmetricBlockMat_of_isSymm
      ((isSymm_toFullBlockMat (isSymmetricBlockMat_relMean P q j (j + h))).sub
        Matrix.isSymm_one)
  have hBpos : (toFullBlockMat
      (ofFullBlockMat (toFullBlockMat (relMean P q j (j + h)) - 1))).PosSemidef := by
    rw [hBfull]
    refine Matrix.le_iff.mp ?_
    rw [toFullBlockMat_relMean]
    exact one_le_normalize hEp (toFullBlockMat_adaptedMean_le hPstat hq hlj hjp hfinj hfinp)
  have hb0 : (0 : ℝ) ≤
      blockTrace (ofFullBlockMat (toFullBlockMat (relMean P q j (j + h)) - 1)) :=
    hBpos.trace_nonneg
  have hBtrace : blockTrace (ofFullBlockMat (toFullBlockMat (relMean P q j (j + h)) - 1))
      = blockTrace (relMean P q j (j + h)) - 2 * (d : ℝ) := by
    have hcard : (Fintype.card (BlockCoord d) : ℝ) = 2 * (d : ℝ) := by
      simp [Fintype.card_sum, two_mul]
    rw [blockTrace, hBfull, Matrix.trace_sub, Matrix.trace_one, hcard]
    rfl
  -- symmetry of the three normalized families
  have hDsym : ∀ a, IsSymmetricBlockMat (normalizedBlock
      (blockSub (G a) (coarseBlock (adaptedCell q (j + h)) a))
      (adaptedMean P q (j + h))) := fun a =>
    isSymmetricBlockMat_normalizedBlock
      (isSymmetricBlockMat_blockSub (hGsym a)
        (isSymmetricBlockMat_coarseBlock (adaptedCell q (j + h)) a))
  have hYsym : ∀ a, IsSymmetricBlockMat (normalizedBlock
      (blockSub (G a) (adaptedMean P q j)) (adaptedMean P q (j + h))) := fun a =>
    isSymmetricBlockMat_normalizedBlock
      (isSymmetricBlockMat_blockSub (hGsym a) (isSymmetricBlockMat_adaptedMean P q j))
  have hHsym : ∀ a, IsSymmetricBlockMat (normalizedBlock
      (blockSub (coarseBlock (adaptedCell q (j + h)) a) (adaptedMean P q (j + h)))
      (adaptedMean P q (j + h))) := fun a =>
    isSymmetricBlockMat_normalizedBlock
      (isSymmetricBlockMat_blockSub
        (isSymmetricBlockMat_coarseBlock (adaptedCell q (j + h)) a)
        (isSymmetricBlockMat_adaptedMean P q (j + h)))
  -- measurability of the three normalized families
  have hDmeas : ∀ α β : BlockCoord d, AEStronglyMeasurable
      (fun a => toFullBlockMat (normalizedBlock
        (blockSub (G a) (coarseBlock (adaptedCell q (j + h)) a))
        (adaptedMean P q (j + h))) α β) P :=
    aestronglyMeasurable_entry_normalizedBlock_blockSub _ hGmeas hAmeas
  have hYmeas : ∀ α β : BlockCoord d, AEStronglyMeasurable
      (fun a => toFullBlockMat (normalizedBlock
        (blockSub (G a) (adaptedMean P q j)) (adaptedMean P q (j + h))) α β) P :=
    aestronglyMeasurable_entry_normalizedBlock_blockSub _ hGmeas
      (fun _ _ => aestronglyMeasurable_const)
  have hHmeas : ∀ α β : BlockCoord d, AEStronglyMeasurable
      (fun a => toFullBlockMat (normalizedBlock
        (blockSub (coarseBlock (adaptedCell q (j + h)) a) (adaptedMean P q (j + h)))
        (adaptedMean P q (j + h))) α β) P :=
    aestronglyMeasurable_entry_normalizedBlock_blockSub _ hAmeas
      (fun _ _ => aestronglyMeasurable_const)
  have hmD := aestronglyMeasurable_schattenNorm hDsym hQeven hDmeas
  have hmY := aestronglyMeasurable_schattenNorm hYsym hQeven hYmeas
  have hmH := aestronglyMeasurable_schattenNorm hHsym hQeven hHmeas
  have hmT := aestronglyMeasurable_blockTrace hDmeas
  -- the algebraic identities of the positive-gap estimate
  have hsplit : ∀ a, toFullBlockMat (normalizedBlock (G a) (adaptedMean P q (j + h)))
      = toFullBlockMat (relMean P q j (j + h)) +
        toFullBlockMat (normalizedBlock (blockSub (G a) (adaptedMean P q j))
          (adaptedMean P q (j + h))) := by
    intro a
    rw [toFullBlockMat_normalizedBlock, toFullBlockMat_normalizedBlock_blockSub,
      toFullBlockMat_relMean]
    abel
  have heqH : ∀ a, toFullBlockMat (normalizedBlock
      (blockSub (coarseBlock (adaptedCell q (j + h)) a) (adaptedMean P q (j + h)))
      (adaptedMean P q (j + h)))
      = toFullBlockMat (normalizedBlock (blockSub (G a) (adaptedMean P q j))
            (adaptedMean P q (j + h))) -
          (toFullBlockMat (normalizedBlock
              (blockSub (G a) (coarseBlock (adaptedCell q (j + h)) a))
              (adaptedMean P q (j + h))) -
            toFullBlockMat
              (ofFullBlockMat (toFullBlockMat (relMean P q j (j + h)) - 1))) := by
    intro a
    rw [toFullBlockMat_normalizedBlock_blockSub, toFullBlockMat_normalizedBlock_blockSub,
      toFullBlockMat_normalizedBlock_blockSub, hBfull, toFullBlockMat_relMean,
      matSqrt_inv_conj hEp]
    abel
  have heqD : ∀ a, toFullBlockMat (normalizedBlock
      (blockSub (G a) (coarseBlock (adaptedCell q (j + h)) a)) (adaptedMean P q (j + h)))
      = toFullBlockMat (normalizedBlock (blockSub (G a) (adaptedMean P q j))
            (adaptedMean P q (j + h))) -
          (toFullBlockMat (normalizedBlock
              (blockSub (coarseBlock (adaptedCell q (j + h)) a) (adaptedMean P q (j + h)))
              (adaptedMean P q (j + h))) -
            toFullBlockMat
              (ofFullBlockMat (toFullBlockMat (relMean P q j (j + h)) - 1))) := by
    intro a
    rw [toFullBlockMat_normalizedBlock_blockSub, toFullBlockMat_normalizedBlock_blockSub,
      toFullBlockMat_normalizedBlock_blockSub, hBfull, toFullBlockMat_relMean,
      matSqrt_inv_conj hEp]
    abel
  have hDpos : ∀ a, (toFullBlockMat (normalizedBlock
      (blockSub (G a) (coarseBlock (adaptedCell q (j + h)) a))
      (adaptedMean P q (j + h)))).PosSemidef := fun a =>
    posSemidef_toFullBlockMat_normalizedBlock_blockSub hEp hGle a
  have hDG : ∀ a, toFullBlockMat (normalizedBlock
        (blockSub (G a) (coarseBlock (adaptedCell q (j + h)) a)) (adaptedMean P q (j + h)))
      ≤ toFullBlockMat (normalizedBlock (G a) (adaptedMean P q (j + h))) := by
    intro a
    rw [toFullBlockMat_normalizedBlock_blockSub, toFullBlockMat_normalizedBlock]
    refine sub_le_self _ (Matrix.nonneg_iff_posSemidef.mpr (posSemidef_normalize ?_ hEp))
    exact (posDef_toFullBlockMat
      (isSymmetricBlockMat_coarseBlock (adaptedCell q (j + h)) a)
      (blockPosDef_coarseBlock_adaptedCell hqPD (j + h) a)).posSemidef
  have hPmle : ∀ _a : CoeffSpace d, toFullBlockMat (relMean P q j (j + h)) ≤
      Real.exp (detIncrement P q j (j + h)) • (1 : FullBlockMat d) := fun _ =>
    le_smul_one_of_norm_le (by
      rw [toFullBlockMat_relMean]
      exact posSemidef_normalize hEj.posSemidef hEp) hrelnorm
  have hgapmean : eLpNorm (fun a => blockTrace (normalizedBlock
        (blockSub (G a) (coarseBlock (adaptedCell q (j + h)) a))
        (adaptedMean P q (j + h)))) 1 P
      ≤ ENNReal.ofReal
        (blockTrace (ofFullBlockMat (toFullBlockMat (relMean P q j (j + h)) - 1))) :=
    eLpNorm_blockTrace_normalizedBlock_blockSub_le hfinp hEp hGint hGmean hGle
      (le_of_eq hBtrace.symm)
  -- the averaging step, at the cardinality of the aligned subdivision
  have hgain : ((Z.card : ℝ)) ^ (-(2 : ℝ)⁻¹) = (3 : ℝ) ^ (-(h : ℝ) * (d : ℝ) / 2) := by
    have hexp : (j + h - j).toNat = h.toNat := by
      congr 1
      omega
    have hcard : Z.card = 3 ^ (d * h.toNat) := by rw [hZcard, hexp]
    have h3 : (0 : ℝ) ≤ 3 := by norm_num
    have htoNat : ((h.toNat : ℕ) : ℝ) = (h : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ h)
    have hbase : ((Z.card : ℕ) : ℝ) = (3 : ℝ) ^ ((d * h.toNat : ℕ) : ℝ) := by
      rw [hcard, Real.rpow_natCast]
      push_cast
      ring
    rw [hbase, ← Real.rpow_mul h3]
    congr 1
    push_cast [htoNat]
    ring
  have haverage : lqSchattenSize P (Q : ℝ)
        (fun a => blockSub (G a) (adaptedMean P q j)) (adaptedMean P q j)
      ≤ ENNReal.ofReal (2 * (d : ℝ) *
          ((2 * (Q : ℝ) + 4 * IndependentSums.rosenthalBennettIntegralConst *
            Real.sqrt (Q : ℝ)) * Real.sqrt ((3 : ℝ) ^ d)) *
          (3 : ℝ) ^ (-(h : ℝ) * (d : ℝ) / 2)) * centeredMoment P (Q : ℝ) q j := by
    have hbd := lqSchattenSize_alignedAverage_le_centeredMoment hPstat hPunit hQR hq hlj
      hfinj hmomj hZne
    rwa [hgain] at hbd
  have htrans : lqSchattenSize P (Q : ℝ)
        (fun a => blockSub (G a) (adaptedMean P q j)) (adaptedMean P q (j + h))
      ≤ ENNReal.ofReal ((2 * d : ℝ) ^ ((Q : ℝ))⁻¹ *
          Real.exp (detIncrement P q j (j + h)) *
          (2 * (d : ℝ) * ((2 * (Q : ℝ) + 4 * IndependentSums.rosenthalBennettIntegralConst *
            Real.sqrt (Q : ℝ)) * Real.sqrt ((3 : ℝ) ^ d)) *
            (3 : ℝ) ^ (-(h : ℝ) * (d : ℝ) / 2))) * centeredMoment P (Q : ℝ) q j :=
    transported_average_le (isSymmetricBlockMat_adaptedMean P q j)
      (isSymmetricBlockMat_adaptedMean P q (j + h))
      (blockPosDef_adaptedMean_of_isRoundedGrid hq j hfinj)
      (blockPosDef_adaptedMean_of_isRoundedGrid hq (j + h) hfinp)
      (adaptedMean_le hPstat hq hlj hjp hfinj hfinp)
      (fun a => isSymmetricBlockMat_blockSub (hGsym a) (isSymmetricBlockMat_adaptedMean P q j))
      hQ0 haverage
  -- the three mixed norms as real numbers
  have hyne : lqSchattenSize P (Q : ℝ)
      (fun a => blockSub (G a) (adaptedMean P q j)) (adaptedMean P q (j + h)) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hmomj) htrans
  set y : ℝ := (lqSchattenSize P (Q : ℝ)
    (fun a => blockSub (G a) (adaptedMean P q j)) (adaptedMean P q (j + h))).toReal
  set f : ℝ := (centeredMoment P (Q : ℝ) q (j + h)).toReal
  have hy0 : (0 : ℝ) ≤ y := ENNReal.toReal_nonneg
  have hyval : eLpNorm (fun a => schattenNorm (Q : ℝ) (normalizedBlock
        (blockSub (G a) (adaptedMean P q j)) (adaptedMean P q (j + h))))
        (ENNReal.ofReal (Q : ℝ)) P = ENNReal.ofReal y :=
    (ENNReal.ofReal_toReal hyne).symm
  have hfval : eLpNorm (fun a => schattenNorm (Q : ℝ) (normalizedBlock
        (blockSub (coarseBlock (adaptedCell q (j + h)) a) (adaptedMean P q (j + h)))
        (adaptedMean P q (j + h)))) (ENNReal.ofReal (Q : ℝ)) P = ENNReal.ofReal f :=
    (ENNReal.ofReal_toReal hmomp).symm
  have hxne : eLpNorm (fun a => schattenNorm (Q : ℝ) (normalizedBlock
      (blockSub (G a) (coarseBlock (adaptedCell q (j + h)) a))
      (adaptedMean P q (j + h)))) (ENNReal.ofReal (Q : ℝ)) P ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_
      (eLpNorm_schattenNorm_le_mul_add P hQ1 hDsym hYsym hHsym hBsym hBpos heqD hmY hmH)
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨hyne, hmomp⟩, ENNReal.ofReal_ne_top⟩)
  set x : ℝ := (eLpNorm (fun a => schattenNorm (Q : ℝ) (normalizedBlock
    (blockSub (G a) (coarseBlock (adaptedCell q (j + h)) a))
    (adaptedMean P q (j + h)))) (ENNReal.ofReal (Q : ℝ)) P).toReal
  have hx0 : (0 : ℝ) ≤ x := ENNReal.toReal_nonneg
  have hxval : eLpNorm (fun a => schattenNorm (Q : ℝ) (normalizedBlock
        (blockSub (G a) (coarseBlock (adaptedCell q (j + h)) a))
        (adaptedMean P q (j + h)))) (ENNReal.ofReal (Q : ℝ)) P = ENNReal.ofReal x :=
    (ENNReal.ofReal_toReal hxne).symm
  -- the positive-gap estimate
  have habsorb := rpow_le_mul_add_mul_of_eLpNorm_eq P hd0 hQR
    (D := fun a => normalizedBlock
      (blockSub (G a) (coarseBlock (adaptedCell q (j + h)) a)) (adaptedMean P q (j + h)))
    (Gh := fun a => normalizedBlock (G a) (adaptedMean P q (j + h)))
    (Pm := fun _ => relMean P q j (j + h))
    (Y := fun a => normalizedBlock (blockSub (G a) (adaptedMean P q j))
      (adaptedMean P q (j + h)))
    (Real.exp_pos _).le hb0 hx0 hy0 hDsym hDpos hYsym hsplit hPmle hDG hmD hmY hmT
    hgapmean hxval hyval
  have htri := le_mul_add_of_eLpNorm_eq P hQ1 hx0 hy0 hHsym hYsym hDsym hBsym hBpos heqH
    hmY hmD hfval hxval hyval
  have hgapbound := le_gap_bound_gainPhi hQR hCC hKK.le hx0 hy0 (Real.exp_pos _).le hb0
    hDelta le_rfl (by rw [hBtrace]; exact hrelgap) habsorb htri
  -- the transported bound on the centred average
  have hyle : y ≤ (2 * d : ℝ) ^ ((Q : ℝ))⁻¹ * Real.exp (detIncrement P q j (j + h)) *
      (2 * (d : ℝ) * ((2 * (Q : ℝ) + 4 * IndependentSums.rosenthalBennettIntegralConst *
        Real.sqrt (Q : ℝ)) * Real.sqrt ((3 : ℝ) ^ d)) *
        (3 : ℝ) ^ (-(h : ℝ) * (d : ℝ) / 2)) * (centeredMoment P (Q : ℝ) q j).toReal := by
    have hcoef : (0 : ℝ) ≤ (2 * d : ℝ) ^ ((Q : ℝ))⁻¹ *
        Real.exp (detIncrement P q j (j + h)) *
        (2 * (d : ℝ) * ((2 * (Q : ℝ) + 4 * IndependentSums.rosenthalBennettIntegralConst *
          Real.sqrt (Q : ℝ)) * Real.sqrt ((3 : ℝ) ^ d)) *
          (3 : ℝ) ^ (-(h : ℝ) * (d : ℝ) / 2)) :=
      mul_nonneg (mul_nonneg hKK.le (Real.exp_pos _).le)
        (mul_nonneg hCAA (Real.rpow_nonneg (by norm_num) _))
    have hmono := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hmomj) htrans
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hcoef] at hmono
  -- the printed contraction, first between real numbers
  have hgainpos : (0 : ℝ) ≤ gainPhi (Q : ℝ) (detIncrement P q j (j + h)) :=
    gainPhi_nonneg hDelta
  have hvj0 : (0 : ℝ) ≤ (centeredMoment P (Q : ℝ) q j).toReal := ENNReal.toReal_nonneg
  have hg0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(h : ℝ) * (d : ℝ) / 2) :=
    Real.rpow_nonneg (by norm_num) _
  have hreal : f ≤ (2 * d : ℝ) ^ ((Q : ℝ))⁻¹ *
        (1 + (2 * ((2 : ℝ) ^ ((Q : ℝ) - 2) * (2 * d : ℝ) ^ (1 - ((Q : ℝ))⁻¹))) ^ ((Q : ℝ))⁻¹ +
          (2 * ((2 : ℝ) ^ ((Q : ℝ) - 2) *
            (2 * d : ℝ) ^ (1 - ((Q : ℝ))⁻¹))) ^ ((Q : ℝ) - 1)⁻¹) *
        (1 + (2 * d : ℝ) ^ ((Q : ℝ))⁻¹ *
          (2 * (d : ℝ) * ((2 * (Q : ℝ) + 4 * IndependentSums.rosenthalBennettIntegralConst *
            Real.sqrt (Q : ℝ)) * Real.sqrt ((3 : ℝ) ^ d)))) *
        (3 : ℝ) ^ (-(h : ℝ) * (d : ℝ) / 2) *
        Real.exp (detIncrement P q j (j + h)) * (centeredMoment P (Q : ℝ) q j).toReal +
      (2 * d : ℝ) ^ ((Q : ℝ))⁻¹ *
        (1 + (2 * ((2 : ℝ) ^ ((Q : ℝ) - 2) * (2 * d : ℝ) ^ (1 - ((Q : ℝ))⁻¹))) ^ ((Q : ℝ))⁻¹ +
          (2 * ((2 : ℝ) ^ ((Q : ℝ) - 2) *
            (2 * d : ℝ) ^ (1 - ((Q : ℝ))⁻¹))) ^ ((Q : ℝ) - 1)⁻¹) *
        (1 + (2 * d : ℝ) ^ ((Q : ℝ))⁻¹ *
          (2 * (d : ℝ) * ((2 * (Q : ℝ) + 4 * IndependentSums.rosenthalBennettIntegralConst *
            Real.sqrt (Q : ℝ)) * Real.sqrt ((3 : ℝ) ^ d)))) *
        gainPhi (Q : ℝ) (detIncrement P q j (j + h)) := by
    have hstep : f ≤ (2 * d : ℝ) ^ ((Q : ℝ))⁻¹ *
        (1 + (2 * ((2 : ℝ) ^ ((Q : ℝ) - 2) * (2 * d : ℝ) ^ (1 - ((Q : ℝ))⁻¹))) ^ ((Q : ℝ))⁻¹ +
          (2 * ((2 : ℝ) ^ ((Q : ℝ) - 2) *
            (2 * d : ℝ) ^ (1 - ((Q : ℝ))⁻¹))) ^ ((Q : ℝ) - 1)⁻¹) *
        ((2 * d : ℝ) ^ ((Q : ℝ))⁻¹ * Real.exp (detIncrement P q j (j + h)) *
          (2 * (d : ℝ) * ((2 * (Q : ℝ) + 4 * IndependentSums.rosenthalBennettIntegralConst *
            Real.sqrt (Q : ℝ)) * Real.sqrt ((3 : ℝ) ^ d)) *
            (3 : ℝ) ^ (-(h : ℝ) * (d : ℝ) / 2)) * (centeredMoment P (Q : ℝ) q j).toReal +
          gainPhi (Q : ℝ) (detIncrement P q j (j + h))) := by
      refine le_trans hgapbound (mul_le_mul_of_nonneg_left ?_ hCgap.le)
      linarith only [hyle]
    have hslack : (0 : ℝ) ≤ (2 * d : ℝ) ^ ((Q : ℝ))⁻¹ *
        (1 + (2 * ((2 : ℝ) ^ ((Q : ℝ) - 2) * (2 * d : ℝ) ^ (1 - ((Q : ℝ))⁻¹))) ^ ((Q : ℝ))⁻¹ +
          (2 * ((2 : ℝ) ^ ((Q : ℝ) - 2) *
            (2 * d : ℝ) ^ (1 - ((Q : ℝ))⁻¹))) ^ ((Q : ℝ) - 1)⁻¹) *
        ((3 : ℝ) ^ (-(h : ℝ) * (d : ℝ) / 2) * Real.exp (detIncrement P q j (j + h)) *
          (centeredMoment P (Q : ℝ) q j).toReal) :=
      mul_nonneg hCgap.le
        (mul_nonneg (mul_nonneg hg0 (Real.exp_pos _).le) hvj0)
    have hslack' : (0 : ℝ) ≤ (2 * d : ℝ) ^ ((Q : ℝ))⁻¹ *
        (1 + (2 * ((2 : ℝ) ^ ((Q : ℝ) - 2) * (2 * d : ℝ) ^ (1 - ((Q : ℝ))⁻¹))) ^ ((Q : ℝ))⁻¹ +
          (2 * ((2 : ℝ) ^ ((Q : ℝ) - 2) *
            (2 * d : ℝ) ^ (1 - ((Q : ℝ))⁻¹))) ^ ((Q : ℝ) - 1)⁻¹) *
        ((2 * d : ℝ) ^ ((Q : ℝ))⁻¹ *
          (2 * (d : ℝ) * ((2 * (Q : ℝ) + 4 * IndependentSums.rosenthalBennettIntegralConst *
            Real.sqrt (Q : ℝ)) * Real.sqrt ((3 : ℝ) ^ d))) *
          gainPhi (Q : ℝ) (detIncrement P q j (j + h))) :=
      mul_nonneg hCgap.le (mul_nonneg (mul_nonneg hKK.le hCAA) hgainpos)
    linarith only [hstep, hslack, hslack']
  -- the printed contraction, back in the extended reals
  have hcoef1 : (0 : ℝ) ≤ (2 * d : ℝ) ^ ((Q : ℝ))⁻¹ *
      (1 + (2 * ((2 : ℝ) ^ ((Q : ℝ) - 2) * (2 * d : ℝ) ^ (1 - ((Q : ℝ))⁻¹))) ^ ((Q : ℝ))⁻¹ +
        (2 * ((2 : ℝ) ^ ((Q : ℝ) - 2) *
          (2 * d : ℝ) ^ (1 - ((Q : ℝ))⁻¹))) ^ ((Q : ℝ) - 1)⁻¹) *
      (1 + (2 * d : ℝ) ^ ((Q : ℝ))⁻¹ *
        (2 * (d : ℝ) * ((2 * (Q : ℝ) + 4 * IndependentSums.rosenthalBennettIntegralConst *
          Real.sqrt (Q : ℝ)) * Real.sqrt ((3 : ℝ) ^ d)))) *
      (3 : ℝ) ^ (-(h : ℝ) * (d : ℝ) / 2) * Real.exp (detIncrement P q j (j + h)) := by
    have hCrec : (0 : ℝ) ≤ (2 * d : ℝ) ^ ((Q : ℝ))⁻¹ *
        (1 + (2 * ((2 : ℝ) ^ ((Q : ℝ) - 2) * (2 * d : ℝ) ^ (1 - ((Q : ℝ))⁻¹))) ^ ((Q : ℝ))⁻¹ +
          (2 * ((2 : ℝ) ^ ((Q : ℝ) - 2) *
            (2 * d : ℝ) ^ (1 - ((Q : ℝ))⁻¹))) ^ ((Q : ℝ) - 1)⁻¹) *
        (1 + (2 * d : ℝ) ^ ((Q : ℝ))⁻¹ *
          (2 * (d : ℝ) * ((2 * (Q : ℝ) + 4 * IndependentSums.rosenthalBennettIntegralConst *
            Real.sqrt (Q : ℝ)) * Real.sqrt ((3 : ℝ) ^ d)))) := by
      have hprod := mul_nonneg hKK.le hCAA
      exact mul_nonneg hCgap.le (by linarith only [hprod])
    exact mul_nonneg (mul_nonneg hCrec hg0) (Real.exp_pos _).le
  have hcoef2 : (0 : ℝ) ≤ (2 * d : ℝ) ^ ((Q : ℝ))⁻¹ *
      (1 + (2 * ((2 : ℝ) ^ ((Q : ℝ) - 2) * (2 * d : ℝ) ^ (1 - ((Q : ℝ))⁻¹))) ^ ((Q : ℝ))⁻¹ +
        (2 * ((2 : ℝ) ^ ((Q : ℝ) - 2) *
          (2 * d : ℝ) ^ (1 - ((Q : ℝ))⁻¹))) ^ ((Q : ℝ) - 1)⁻¹) *
      (1 + (2 * d : ℝ) ^ ((Q : ℝ))⁻¹ *
        (2 * (d : ℝ) * ((2 * (Q : ℝ) + 4 * IndependentSums.rosenthalBennettIntegralConst *
          Real.sqrt (Q : ℝ)) * Real.sqrt ((3 : ℝ) ^ d)))) *
      gainPhi (Q : ℝ) (detIncrement P q j (j + h)) := by
    have hprod := mul_nonneg hKK.le hCAA
    exact mul_nonneg (mul_nonneg hCgap.le (by linarith only [hprod])) hgainpos
  have hconv : ∀ A B : ℝ, 0 ≤ A → 0 ≤ B →
      f ≤ A * (centeredMoment P (Q : ℝ) q j).toReal + B →
      centeredMoment P (Q : ℝ) q (j + h) ≤
        ENNReal.ofReal A * centeredMoment P (Q : ℝ) q j + ENNReal.ofReal B := by
    intro A B hA hB hle
    calc centeredMoment P (Q : ℝ) q (j + h) = ENNReal.ofReal f :=
          (ENNReal.ofReal_toReal hmomp).symm
      _ ≤ ENNReal.ofReal (A * (centeredMoment P (Q : ℝ) q j).toReal + B) :=
          ENNReal.ofReal_le_ofReal hle
      _ = ENNReal.ofReal (A * (centeredMoment P (Q : ℝ) q j).toReal) + ENNReal.ofReal B :=
          ENNReal.ofReal_add (mul_nonneg hA hvj0) hB
      _ = ENNReal.ofReal A * ENNReal.ofReal (centeredMoment P (Q : ℝ) q j).toReal +
            ENNReal.ofReal B := by rw [ENNReal.ofReal_mul hA]
      _ = ENNReal.ofReal A * centeredMoment P (Q : ℝ) q j + ENNReal.ofReal B := by
          rw [ENNReal.ofReal_toReal hmomj]
  exact hconv _ _ hcoef1 hcoef2 hreal

end

end Recurrence
end HighContrast
end Homogenization
