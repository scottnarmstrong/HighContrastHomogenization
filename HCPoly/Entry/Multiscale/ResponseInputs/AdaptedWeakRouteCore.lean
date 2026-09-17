import HCPoly.Entry.Multiscale.ResponseInputs.AdaptedEnergy
import HCPoly.Entry.Multiscale.ResponseInputs.HC1_DomainBridgeAnnealedBlock
import HCPoly.Entry.Multiscale.ResponseInputs.HC2_WeakSeminorm
import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakRecentSupport
import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakRecent
import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakPrimalRoutePlus
import HCPoly.Entry.Multiscale.ResponseInputs.RecentreCore

/-!
# The route to `response_weak_estimate` (`p.response.transfer`)

Every statement here except `response_weak_estimate_of_route` is an intermediate that may be
restated; the final theorem has the same statement as `AdaptedWeak.lean` and is proved from
the intermediate lemmas.

Notation: `K_0^2 = respK0Sq±`, `(L^±)^2 = respLsq±`, `M = respAllScaleMax`, `Q = bigQ`,
`α = respAlpha`, `ρ = respRho`, `S_cell = weakCellSum`, `S_av = weakAverageSum`,
`ℰ = weakOptimizerEnergy`, `c_a = respRecentre±` (the recentring vector of `p.response.transfer`).

Chain for one maximizer family `u` (minus sign; plus is the twin):
`3^{-t/2}·[M_0^{1/2}(⟨X_a⟩_{k,z} - Y)] ≤ 3^{-t/2}·[M_0^{1/2}(⟨X_a⟩_{k,z} - ⟨X_a⟩_{U_t})] + |c_a|/(1-3^{-1/2})`
by the triangle inequality, the summability of the centred family and the pathwise bound
≤ `16 K_0 L (S_cell + S_av) + (16/(1-ρ)) K_0 T(a) ℰ(a) + |c_a|/(1-3^{-1/2})`
(`diagonalWeakNorm_primal_le`); square, `(x+y+z)^2 ≤ 3(x^2+y^2+z^2)`, integrate:
`∫(S_cell+S_av)^2 ≤ D_H η^{1/Q}`, `T(a)^2 ℰ(a)^2 ≤ 2 L^2 (M^Q + 3^{-2αH})` a.e.
integrated with `∫ M^Q ≤ C_m η` and `Integrable M^Q`,
`∫|c_a|^2 ≤ C K_0^2 L^2 η^{2/Q}`; finally `K_0^2 L^2 ≤ C κ_s` and the `rpow`
algebra give the integrated estimate, and `Real.sSup_le` gives the final estimate.
-/

open Homogenization.HighContrast (CoeffSpace HasIntegrableCoarseBlock blockSub coarseBlock
  normalizedBlock)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ}

/-! ## Carriers -/

/-- The `n`-th term of `besovSeminorm t avg` (`AdaptedDefs.lean`). -/
def besovTerm (t : ℤ) (avg : ℕ → (Fin d → ℤ) → BlockVec d) (n : ℕ) : ℝ :=
  (3 : ℝ) ^ (((t : ℝ) - (n : ℝ)) / 2) *
    Real.sqrt ((((triadicIndexBox d n).card : ℝ))⁻¹ *
      ∑ w ∈ triadicIndexBox d n, blockVecDot (avg n w) (avg n w))

theorem besovSeminorm_eq_tsum_besovTerm (t : ℤ) (avg : ℕ → (Fin d → ℤ) → BlockVec d) :
    besovSeminorm t avg = ∑' n : ℕ, besovTerm t avg n := rfl

/-- The per-family weak energy `3^{-t} ∫ [Besov]^2 dP` of one maximizer family `u`: the generic
element of the `sSup` set defining `respWeakEnergy` (`AdaptedDefs.lean`). -/
def respWeakEnergyOf (P : Measure (CoeffSpace d)) (qq : Mat d) (t : ℤ) (M0 : BlockMat d)
    (b : CoeffSpace d → CoeffField d) (Y : BlockVec d)
    (u : (a : CoeffSpace d) → AHarmonicFunction (b a) (HighContrast.adaptedCell qq t)) : ℝ :=
  (3 : ℝ) ^ (-(t : ℝ)) *
    ∫ a, besovSeminorm t (fun n z =>
        blockMatVecMul (blockSqrt M0)
          (cellAverage (adaptedCellAtCenter qq (t - (n : ℤ)) z) (optimizerField (b a) (u a)) - Y)) ^ 2 ∂P

/-- `K_0^2 = |M_0^{-1/2} Ehat_t^- M_0^{-1/2}|` (paper `p.response.transfer`), minus sign; the literal
factor of `diagonalWeakNorm_primal_le`. -/
def respK0SqMinus (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d) (t : ℤ) : ℝ :=
  blockSpecBound (normalizedBlock (respEhatMinus P jStar F t) (respM0 F))

/-- `K_0^2` for the plus sign. -/
def respK0SqPlus (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d) (t : ℤ) : ℝ :=
  blockSpecBound (normalizedBlock (respEhatPlus P jStar F t) (respM0 F))

/-- The recentring vector `c_a = M_0^{1/2}(⟨X_a⟩_{U_t} - Y^-)` (paper `p.response.transfer`), minus sign. -/
def respRecentreMinus (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d) (t : ℤ)
    (e : Vec d) (a : CoeffSpace d)
    (u : AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t)) : BlockVec d :=
  blockMatVecMul (blockSqrt (respM0 F))
    (cellAverage (respCell jStar F t) (optimizerField (respCoeffMinus F a) u) -
      respYMinus P jStar F t e)

/-- The recentring vector, plus sign. -/
def respRecentrePlus (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d) (t : ℤ)
    (e : Vec d) (a : CoeffSpace d)
    (u : AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t)) : BlockVec d :=
  blockMatVecMul (blockSqrt (respM0 F))
    (cellAverage (respCell jStar F t) (optimizerField (respCoeffPlus F a) u) -
      respYPlus P jStar F t e)

/-- The recent-cell normalized defect block at depth `n`, index `w`: the summand of
`weakCellDefect` before the norm. -/
def recentDefectBlock (q : Mat d) (t : ℤ) (n : ℕ) (w : Fin d → ℤ) (E : BlockMat d)
    (b : CoeffField d) :=
  toFullBlockMat
    (normalizedBlock
      (blockSub (coarseBlockMatrix (adaptedCellAtCenter q (t - (n : ℤ)) w) b)
        (coarseBlockMatrix (HighContrast.adaptedCell q t) b)) E)

/-- Its norm, the summand of `weakCellDefect`. -/
def recentDefect (q : Mat d) (t : ℤ) (n : ℕ) (w : Fin d → ℤ) (E : BlockMat d)
    (b : CoeffField d) : ℝ :=
  ‖recentDefectBlock q t n w E b‖

/-! ## The `sSup` reduction (`p.response.transfer`) -/

/-- `0 ≤ W^±` unconditionally (`Real.sSup_nonneg`: every member is
`3^{-t} ∫ (…)^2 ≥ 0`; the empty/unbounded junk value is `0`). -/
theorem respWeakEnergy_nonneg (P : Measure (CoeffSpace d)) (qq : Mat d) (t : ℤ)
    (M0 : BlockMat d) (p q' : Vec d) (b : CoeffSpace d → CoeffField d) (Y : BlockVec d) :
    0 ≤ respWeakEnergy P qq t M0 p q' b Y := by
  refine Real.sSup_nonneg ?_
  rintro c ⟨u, -, rfl⟩
  exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
    (integral_nonneg fun a => sq_nonneg _)

/-- `(W^±)^{1/2} ≤ B` once every admissible family has energy `≤ B^2`
(`Real.sSup_le` needs no boundedness in `ℝ`; then `Real.sqrt_le_sqrt`, `Real.sqrt_sq hB`). -/
theorem sqrt_respWeakEnergy_le (P : Measure (CoeffSpace d)) (qq : Mat d) (t : ℤ)
    (M0 : BlockMat d) (p q' : Vec d) (b : CoeffSpace d → CoeffField d) (Y : BlockVec d)
    (B : ℝ) (hB : 0 ≤ B)
    (h : ∀ u : (a : CoeffSpace d) → AHarmonicFunction (b a) (HighContrast.adaptedCell qq t),
      (∀ a, IsResponseMaximizer (HighContrast.adaptedCell qq t) p q' (b a) (u a)) →
        respWeakEnergyOf P qq t M0 b Y u ≤ B ^ 2) :
    Real.sqrt (respWeakEnergy P qq t M0 p q' b Y) ≤ B := by
  have hW : respWeakEnergy P qq t M0 p q' b Y ≤ B ^ 2 := by
    refine Real.sSup_le ?_ (sq_nonneg B)
    rintro c ⟨u, hu, rfl⟩
    exact h u hu
  calc Real.sqrt (respWeakEnergy P qq t M0 p q' b Y)
      ≤ Real.sqrt (B ^ 2) := Real.sqrt_le_sqrt hW
    _ = B := Real.sqrt_sq hB

/-! ## Local helper: Minkowski for the normalized finite-cell `L²` length.

The corresponding declarations in `HC2_WeakSeminorm.lean` are `private` and so cannot be
imported across files; these local copies are needed for the triangle inequality of the Besov
seminorm against a constant family. -/

private theorem w2_sum_blockVecDot_eq_sum_prod {iota : Type*}
    (Z : Finset iota) (u v : iota → BlockVec d) :
    ∑ z ∈ Z, blockVecDot (u z) (v z) =
      ∑ p ∈ Z ×ˢ (Finset.univ : Finset (Fin d ⊕ Fin d)),
        Sum.elim (fun i => (u p.1).1 i) (fun i => (u p.1).2 i) p.2 *
          Sum.elim (fun i => (v p.1).1 i) (fun i => (v p.1).2 i) p.2 := by
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Fintype.sum_sum_type]
  rfl

private theorem w2_sq_sum_blockVecDot_le {iota : Type*}
    (Z : Finset iota) (u v : iota → BlockVec d) :
    (∑ z ∈ Z, blockVecDot (u z) (v z)) ^ 2 ≤
      (∑ z ∈ Z, blockVecDot (u z) (u z)) *
        ∑ z ∈ Z, blockVecDot (v z) (v z) := by
  classical
  set S : Finset (iota × (Fin d ⊕ Fin d)) :=
    Z ×ˢ (Finset.univ : Finset (Fin d ⊕ Fin d)) with hS
  set U : iota × (Fin d ⊕ Fin d) → ℝ :=
    fun p => Sum.elim (fun i => (u p.1).1 i) (fun i => (u p.1).2 i) p.2 with hU
  set V : iota × (Fin d ⊕ Fin d) → ℝ :=
    fun p => Sum.elim (fun i => (v p.1).1 i) (fun i => (v p.1).2 i) p.2 with hV
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (s := S) (f := U) (g := V)
  have hUU : ∑ p ∈ S, U p ^ 2 = ∑ z ∈ Z, blockVecDot (u z) (u z) := by
    rw [w2_sum_blockVecDot_eq_sum_prod Z u u]
    exact Finset.sum_congr rfl fun p _ => pow_two (U p)
  have hVV : ∑ p ∈ S, V p ^ 2 = ∑ z ∈ Z, blockVecDot (v z) (v z) := by
    rw [w2_sum_blockVecDot_eq_sum_prod Z v v]
    exact Finset.sum_congr rfl fun p _ => pow_two (V p)
  rw [w2_sum_blockVecDot_eq_sum_prod Z u v, ← hUU, ← hVV]
  exact hcs

private theorem w2_sq_normalized_sum_blockVecDot_le {iota : Type*}
    (Z : Finset iota) (u v : iota → BlockVec d) :
    (((Z.card : ℝ)⁻¹ * ∑ z ∈ Z, blockVecDot (u z) (v z))) ^ 2 ≤
      (((Z.card : ℝ)⁻¹ * ∑ z ∈ Z, blockVecDot (u z) (u z)) *
        ((Z.card : ℝ)⁻¹ * ∑ z ∈ Z, blockVecDot (v z) (v z))) := by
  have hkey := w2_sq_sum_blockVecDot_le Z u v
  have hc : 0 ≤ (((Z.card : ℝ)⁻¹) ^ 2) := sq_nonneg _
  calc
    (((Z.card : ℝ)⁻¹ * ∑ z ∈ Z, blockVecDot (u z) (v z)) ^ 2) =
        (Z.card : ℝ)⁻¹ ^ 2 * (∑ z ∈ Z, blockVecDot (u z) (v z)) ^ 2 := by
      ring
    _ ≤ (Z.card : ℝ)⁻¹ ^ 2 *
          ((∑ z ∈ Z, blockVecDot (u z) (u z)) *
            ∑ z ∈ Z, blockVecDot (v z) (v z)) :=
      mul_le_mul_of_nonneg_left hkey hc
    _ = ((Z.card : ℝ)⁻¹ * ∑ z ∈ Z, blockVecDot (u z) (u z)) *
        ((Z.card : ℝ)⁻¹ * ∑ z ∈ Z, blockVecDot (v z) (v z)) := by ring

private theorem w2_blockVecDot_add_self (u v : BlockVec d) :
    blockVecDot (u + v) (u + v) =
      blockVecDot u u + 2 * blockVecDot u v + blockVecDot v v := by
  have hd : ∀ a b : Vec d,
      vecDot (a + b) (a + b) = vecDot a a + 2 * vecDot a b + vecDot b b := by
    intro a b
    rw [vecDot_add_left, vecDot_add_right, vecDot_add_right, vecDot_comm b a]
    ring
  change vecDot (u.1 + v.1) (u.1 + v.1) + vecDot (u.2 + v.2) (u.2 + v.2) = _
  rw [hd u.1 v.1, hd u.2 v.2]
  simp only [blockVecDot]
  ring

private theorem w2_normalized_blockL2_add_le {iota : Type*}
    (Z : Finset iota) (u v : iota → BlockVec d) :
    Real.sqrt ((Z.card : ℝ)⁻¹ *
        ∑ z ∈ Z, blockVecDot (u z + v z) (u z + v z)) ≤
      Real.sqrt ((Z.card : ℝ)⁻¹ *
          ∑ z ∈ Z, blockVecDot (u z) (u z)) +
        Real.sqrt ((Z.card : ℝ)⁻¹ *
          ∑ z ∈ Z, blockVecDot (v z) (v z)) := by
  let A : ℝ := (Z.card : ℝ)⁻¹ * ∑ z ∈ Z, blockVecDot (u z) (u z)
  let B : ℝ := (Z.card : ℝ)⁻¹ * ∑ z ∈ Z, blockVecDot (v z) (v z)
  let C : ℝ := (Z.card : ℝ)⁻¹ * ∑ z ∈ Z, blockVecDot (u z) (v z)
  have hself : ∀ x : BlockVec d, 0 ≤ blockVecDot x x := by
    intro x
    exact add_nonneg (vecNormSq_nonneg x.1) (vecNormSq_nonneg x.2)
  have hA0 : 0 ≤ A := mul_nonneg (by positivity) (Finset.sum_nonneg fun z _ => hself (u z))
  have hB0 : 0 ≤ B := mul_nonneg (by positivity) (Finset.sum_nonneg fun z _ => hself (v z))
  have hexp :
      (Z.card : ℝ)⁻¹ * ∑ z ∈ Z, blockVecDot (u z + v z) (u z + v z) =
        A + 2 * C + B := by
    simp_rw [w2_blockVecDot_add_self]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    dsimp only [A, B, C]
    ring
  have hCS : C ≤ Real.sqrt A * Real.sqrt B := by
    have hsq : C ^ 2 ≤ A * B := w2_sq_normalized_sum_blockVecDot_le Z u v
    calc
      C ≤ |C| := le_abs_self C
      _ = Real.sqrt (C ^ 2) := (Real.sqrt_sq_eq_abs C).symm
      _ ≤ Real.sqrt (A * B) := Real.sqrt_le_sqrt hsq
      _ = Real.sqrt A * Real.sqrt B := Real.sqrt_mul hA0 B
  have hexpand :
      (Real.sqrt A + Real.sqrt B) ^ 2 =
        A + 2 * (Real.sqrt A * Real.sqrt B) + B := by
    rw [add_sq, Real.sq_sqrt hA0, Real.sq_sqrt hB0]
    ring
  rw [hexp]
  calc
    Real.sqrt (A + 2 * C + B) ≤
        Real.sqrt ((Real.sqrt A + Real.sqrt B) ^ 2) := by
      refine Real.sqrt_le_sqrt ?_
      rw [hexpand]
      linarith only [hCS]
    _ = Real.sqrt A + Real.sqrt B := Real.sqrt_sq (by positivity)

/-! ## Recentring the Besov seminorm (`p.response.transfer`) -/

/-- Triangle inequality of the Besov seminorm against a constant family: a constant
`c` has `[c] = 3^{t/2}|c|/(1-3^{-1/2})`.  Per scale, Minkowski on the flat average
(`card_triadicIndexBox` for `card > 0`), then `tsum_le_tsum`/`tsum_add` with `hA` and the
geometric summability of the constant term. -/
theorem besovSeminorm_add_const_le (t : ℤ) (A : ℕ → (Fin d → ℤ) → BlockVec d) (c : BlockVec d)
    (hA : Summable (besovTerm t A)) :
    besovSeminorm t (fun n w => A n w + c) ≤
      besovSeminorm t A +
        (3 : ℝ) ^ ((t : ℝ) / 2) / (1 - (3 : ℝ) ^ (-(1 / 2 : ℝ))) * Real.sqrt (blockVecDot c c) := by
  have hterm_le : ∀ n : ℕ,
      besovTerm t (fun n w => A n w + c) n ≤
        besovTerm t A n +
          (3 : ℝ) ^ (((t : ℝ) - (n : ℝ)) / 2) * Real.sqrt (blockVecDot c c) := by
    intro n
    have hcard_pos : (0 : ℝ) < ((triadicIndexBox d n).card : ℝ) := by
      rw [card_triadicIndexBox]; positivity
    have hmink := w2_normalized_blockL2_add_le (triadicIndexBox d n) (A n)
      (fun _ : (Fin d → ℤ) => c)
    have hcavg : ((triadicIndexBox d n).card : ℝ)⁻¹ *
        ∑ _w ∈ triadicIndexBox d n, blockVecDot c c = blockVecDot c c := by
      rw [Finset.sum_const, nsmul_eq_mul, inv_mul_cancel_left₀ (ne_of_gt hcard_pos)]
    rw [hcavg] at hmink
    have hrpow_nn : (0 : ℝ) ≤ (3 : ℝ) ^ (((t : ℝ) - (n : ℝ)) / 2) :=
      Real.rpow_nonneg (by norm_num) _
    have hstep : besovTerm t (fun n w => A n w + c) n ≤
        (3 : ℝ) ^ (((t : ℝ) - (n : ℝ)) / 2) *
          (Real.sqrt (((triadicIndexBox d n).card : ℝ)⁻¹ *
              ∑ w ∈ triadicIndexBox d n, blockVecDot (A n w) (A n w)) +
            Real.sqrt (blockVecDot c c)) :=
      mul_le_mul_of_nonneg_left hmink hrpow_nn
    calc besovTerm t (fun n w => A n w + c) n
        ≤ (3 : ℝ) ^ (((t : ℝ) - (n : ℝ)) / 2) *
            (Real.sqrt (((triadicIndexBox d n).card : ℝ)⁻¹ *
                ∑ w ∈ triadicIndexBox d n, blockVecDot (A n w) (A n w)) +
              Real.sqrt (blockVecDot c c)) := hstep
      _ = besovTerm t A n +
            (3 : ℝ) ^ (((t : ℝ) - (n : ℝ)) / 2) * Real.sqrt (blockVecDot c c) := by
          unfold besovTerm; ring
  have hgeom' : Summable (fun n : ℕ =>
      (3 : ℝ) ^ (((t : ℝ) - (n : ℝ)) / 2) * Real.sqrt (blockVecDot c c)) := by
    have hgeom : Summable (fun n : ℕ => ((3 : ℝ) ^ (-(1 / 2 : ℝ))) ^ n) :=
      summable_geometric_of_lt_one besovRatio_nonneg besovRatio_lt_one
    have hmul := hgeom.mul_left ((3 : ℝ) ^ ((t : ℝ) / 2) * Real.sqrt (blockVecDot c c))
    convert hmul using 1 <;> try rfl
    funext n
    rw [three_rpow_scale_split t n]; ring
  have hmaj : Summable (fun n : ℕ => besovTerm t A n +
      (3 : ℝ) ^ (((t : ℝ) - (n : ℝ)) / 2) * Real.sqrt (blockVecDot c c)) := hA.add hgeom'
  have hnn : ∀ n, 0 ≤ besovTerm t (fun n w => A n w + c) n := by
    intro n; unfold besovTerm; positivity
  have hsum : Summable (besovTerm t (fun n w => A n w + c)) :=
    Summable.of_nonneg_of_le hnn hterm_le hmaj
  have hb : besovSeminorm t (fun n w => A n w + c) ≤
      ∑' n : ℕ, (besovTerm t A n +
        (3 : ℝ) ^ (((t : ℝ) - (n : ℝ)) / 2) * Real.sqrt (blockVecDot c c)) := by
    rw [besovSeminorm_eq_tsum_besovTerm]
    exact Summable.tsum_le_tsum hterm_le hsum hmaj
  rw [hA.tsum_add hgeom', ← besovSeminorm_eq_tsum_besovTerm] at hb
  have htsumgeom : (∑' n : ℕ,
      (3 : ℝ) ^ (((t : ℝ) - (n : ℝ)) / 2) * Real.sqrt (blockVecDot c c)) =
      (3 : ℝ) ^ ((t : ℝ) / 2) / (1 - (3 : ℝ) ^ (-(1 / 2 : ℝ))) * Real.sqrt (blockVecDot c c) := by
    have heq : (∑' n : ℕ,
        (3 : ℝ) ^ (((t : ℝ) - (n : ℝ)) / 2) * Real.sqrt (blockVecDot c c)) =
        ∑' n : ℕ, (3 : ℝ) ^ ((t : ℝ) / 2) * Real.sqrt (blockVecDot c c) *
          ((3 : ℝ) ^ (-(1 / 2 : ℝ))) ^ n := by
      refine tsum_congr fun n => ?_
      rw [three_rpow_scale_split t n]; ring
    rw [heq, tsum_mul_left, tsum_geometric_of_lt_one besovRatio_nonneg besovRatio_lt_one,
      div_eq_mul_inv]
    ring
  rw [htsumgeom] at hb
  exact hb

/-! ### Local helpers for the summability of the centred family.

The weak seminorm `adaptedWeakSeminorm` is an `ℝ≥0∞`-valued `tsum`, which converges
unconditionally, so summability is automatic there and no separate `summable_*` lemma is needed.
The route below therefore uses `summable_besov_cellAverageFamily` (`HC2_WeakSeminorm.lean`)
applied to the transported, recentred field `x ↦ M_0^{1/2}(X x - ⟨X⟩_{U_t})`.

The five algebraic helpers mirror the helpers of
`HC2b_DiagonalWeakRecent.lean`, which are `private` there and so cannot be
imported, with one deliberate difference: `w3_cellAverage_blockMatVecMul_sub_const` is stated
PER CELL, not as the `funext` family identity, because the family identity needs integrability of
`X` on `adaptedCellAtCenter q (t-n) w` for EVERY `w`, whereas the optimizer field is only `L²` on
`U_t` and so only controls the `w` in `triadicIndexBox d n` -- which is all `besovTerm` sums over.

`w3_memVectorL2_matVecMul` corresponds to `AdaptedSwarm.lean`
(`h7_memVectorL2_const_matVecMul`, `private` there); `w3_elliptic_respCoeffMinus/Plus` from
`H8bEllipticInput.lean` (public, but that file is not in this file's import closure), whose
own source is `Annealed.exists_elliptic_representative_adapted`
(`HCPoly/Entry/Annealed/AdaptedDomainRecovery.lean`).  Together they supply exactly the `L²` datum that
`HC3_CutoffKernel.lean` records as missing for the flux slot. -/

private theorem w3_integrableOn_matVecMul_apply {V : Set (Vec d)} (M : Mat d) (Y : Vec d → Vec d)
    (hY : ∀ j, IntegrableOn (fun x => Y x j) V) (i : Fin d) :
    IntegrableOn (fun x => matVecMul M (Y x) i) V := by
  have h : (fun x => matVecMul M (Y x) i) = fun x => ∑ j, M i j * Y x j := rfl
  rw [h]
  exact integrable_finsetSum _ (fun j _ => (hY j).const_mul (M i j))

private theorem w3_volumeAverage_sub_const {V : Set (Vec d)} (hVfin : volume V ≠ ⊤)
    (hvol : (volume V).toReal ≠ 0) {f : Vec d → ℝ} (hf : IntegrableOn f V) (k : ℝ) :
    volumeAverage V (fun x => f x - k) = volumeAverage V f - k := by
  have : IsFiniteMeasure (volume.restrict V) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_of_le_of_ne le_top hVfin⟩
  have hc : IntegrableOn (fun _ : Vec d => k) V := integrable_const k
  have h : (fun x => f x - k) = f - (fun _ => k) := rfl
  rw [h, volumeAverage_sub hf hc, volumeAverage_const hvol]

private theorem w3_cellAverage_sub_const {V : Set (Vec d)} (hVfin : volume V ≠ ⊤)
    (hvol : (volume V).toReal ≠ 0) (X : Vec d → BlockVec d) (c : BlockVec d)
    (h1 : ∀ j, IntegrableOn (fun x => (X x).1 j) V)
    (h2 : ∀ j, IntegrableOn (fun x => (X x).2 j) V) :
    cellAverage V (fun x => X x - c) = cellAverage V X - c := by
  have hfst : (cellAverage V fun x => X x - c).1 = (cellAverage V X - c).1 := by
    funext i
    exact w3_volumeAverage_sub_const hVfin hvol (h1 i) (c.1 i)
  have hsnd : (cellAverage V fun x => X x - c).2 = (cellAverage V X - c).2 := by
    funext i
    exact w3_volumeAverage_sub_const hVfin hvol (h2 i) (c.2 i)
  exact Prod.ext hfst hsnd

private theorem w3_cellAverage_blockMatVecMul {V : Set (Vec d)} (A : BlockMat d)
    (X : Vec d → BlockVec d)
    (h1 : ∀ j, IntegrableOn (fun x => (X x).1 j) V)
    (h2 : ∀ j, IntegrableOn (fun x => (X x).2 j) V) :
    cellAverage V (fun x => blockMatVecMul A (X x)) = blockMatVecMul A (cellAverage V X) := by
  have key : ∀ (M N : Mat d) (i : Fin d),
      volumeAverage V (fun x => matVecMul M (X x).1 i + matVecMul N (X x).2 i)
        = matVecMul M (fun j => volumeAverage V (fun x => (X x).1 j)) i
          + matVecMul N (fun j => volumeAverage V (fun x => (X x).2 j)) i := by
    intro M N i
    have hM : IntegrableOn (fun x => matVecMul M (X x).1 i) V :=
      w3_integrableOn_matVecMul_apply M (fun x => (X x).1) h1 i
    have hN : IntegrableOn (fun x => matVecMul N (X x).2 i) V :=
      w3_integrableOn_matVecMul_apply N (fun x => (X x).2) h2 i
    have hsplit : (fun x => matVecMul M (X x).1 i + matVecMul N (X x).2 i)
        = (fun x => matVecMul M (X x).1 i) + (fun x => matVecMul N (X x).2 i) := rfl
    rw [hsplit, volumeAverage_add hM hN]
    congr 1
    · exact volumeAverage_vecDot_left (M i) (fun x => (X x).1) h1
    · exact volumeAverage_vecDot_left (N i) (fun x => (X x).2) h2
  have hfst : (cellAverage V fun x => blockMatVecMul A (X x)).1
      = (blockMatVecMul A (cellAverage V X)).1 := by
    funext i
    exact key A.upperLeft A.upperRight i
  have hsnd : (cellAverage V fun x => blockMatVecMul A (X x)).2
      = (blockMatVecMul A (cellAverage V X)).2 := by
    funext i
    exact key A.lowerLeft A.lowerRight i
  exact Prod.ext hfst hsnd

private theorem w3_cellAverage_blockMatVecMul_sub_const {V : Set (Vec d)} (hVfin : volume V ≠ ⊤)
    (hvol : (volume V).toReal ≠ 0) (A : BlockMat d) (X : Vec d → BlockVec d) (c : BlockVec d)
    (h1 : ∀ j, IntegrableOn (fun x => (X x).1 j) V)
    (h2 : ∀ j, IntegrableOn (fun x => (X x).2 j) V) :
    cellAverage V (fun x => blockMatVecMul A (X x - c))
      = blockMatVecMul A (cellAverage V X - c) := by
  have : IsFiniteMeasure (volume.restrict V) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_of_le_of_ne le_top hVfin⟩
  have hs1 : ∀ j, IntegrableOn (fun x => (X x - c).1 j) V := fun j =>
    (h1 j).sub (integrable_const (c.1 j))
  have hs2 : ∀ j, IntegrableOn (fun x => (X x - c).2 j) V := fun j =>
    (h2 j).sub (integrable_const (c.2 j))
  rw [w3_cellAverage_blockMatVecMul A (fun x => X x - c) hs1 hs2,
    w3_cellAverage_sub_const hVfin hvol X c h1 h2]

/-! ### L² input -/

private theorem w3_memVectorL2_matVecMul {U : Set (Vec d)} (g : Mat d) {f : Vec d → Vec d}
    (hf : MemVectorL2 U f) : MemVectorL2 U (fun x => matVecMul g (f x)) := by
  rw [MemVectorL2, MeasureTheory.memLp_pi_iff] at hf ⊢
  intro i
  simpa [matVecMul] using MeasureTheory.memLp_finsetSum Finset.univ
    (fun j _ => (hf j).const_mul (g i j))

private theorem w3_memLp_one_blockVecDot {U : Set (Vec d)} {X : Vec d → BlockVec d}
    (h1 : MemVectorL2 U (fun x => (X x).1)) (h2 : MemVectorL2 U (fun x => (X x).2)) :
    MemLp (fun x => blockVecDot (X x) (X x)) 1 (volume.restrict U) := by
  have e1 := MeasureTheory.memLp_pi_iff.mp h1
  have e2 := MeasureTheory.memLp_pi_iff.mp h2
  rw [memLp_one_iff_integrable]
  have hA : Integrable (fun x => ∑ i, (X x).1 i * (X x).1 i) (volume.restrict U) :=
    integrable_finsetSum _ fun i _ => by
      simpa [Pi.mul_apply] using! (e1 i).integrable_mul (e1 i)
  have hB : Integrable (fun x => ∑ i, (X x).2 i * (X x).2 i) (volume.restrict U) :=
    integrable_finsetSum _ fun i _ => by
      simpa [Pi.mul_apply] using! (e2 i).integrable_mul (e2 i)
  simpa [blockVecDot, vecDot] using! hA.add hB

private theorem w3_integrableOn_slot {U V : Set (Vec d)} (hVU : V ⊆ U) (hVfin : volume V ≠ ⊤)
    {g : Vec d → Vec d} (hg : MemVectorL2 U g) (j : Fin d) :
    IntegrableOn (fun x => g x j) V := by
  have : IsFiniteMeasure (volume.restrict V) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_of_le_of_ne le_top hVfin⟩
  have h2 : MemLp (fun x => g x j) 2 (volume.restrict U) := (MeasureTheory.memLp_pi_iff.mp hg) j
  have h2' : MemLp (fun x => g x j) 2 (volume.restrict V) :=
    h2.mono_measure (Measure.restrict_mono hVU le_rfl)
  exact MemLp.integrable (by norm_num) h2'

private theorem w3_memVectorL2_optimizer_slots {U : Set (Vec d)} {b : CoeffField d}
    (u : AHarmonicFunction b U)
    (hb : ∃ (lam Lam : ℝ) (f : CoeffField d), 0 < lam ∧ lam ≤ Lam ∧
      IsEllipticFieldOn lam Lam U f ∧ b =ᵐ[volumeMeasureOn U] f) :
    MemVectorL2 U (fun x => (optimizerField b u x).1) ∧
      MemVectorL2 U (fun x => (optimizerField b u x).2) := by
  obtain ⟨lam, Lam, f, hlam, hle, hEll, hae⟩ := hb
  have hg : MemVectorL2 U u.toH1.grad := u.toH1.grad_memVectorL2
  refine ⟨hg, ?_⟩
  have h0 : MemVectorL2 U (fun x => matVecMul (f x) (u.toH1.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll hg
  have hcongr : (fun x => matVecMul (f x) (u.toH1.grad x))
      =ᵐ[volumeMeasureOn U] fun x => matVecMul (b x) (u.toH1.grad x) := by
    filter_upwards [hae] with x hx; rw [hx]
  exact (MeasureTheory.memLp_congr_ae hcongr).mp h0

private theorem w3_elliptic_respCoeffMinus [NeZero d] (q : Mat d) (hq : IsUnit q) (t : ℤ)
    (F : BlockMat d) (a : CoeffSpace d) :
    ∃ (lam Lam : ℝ) (f : CoeffField d), 0 < lam ∧ lam ≤ Lam ∧
      IsEllipticFieldOn lam Lam (HighContrast.adaptedCell q t) f ∧
        respCoeffMinus F a =ᵐ[volumeMeasureOn (HighContrast.adaptedCell q t)] f := by
  obtain ⟨lam, Lam, f, hlam, hle, hEll, hae⟩ :=
    Annealed.exists_elliptic_representative_adapted q hq t 0 a
  rw [adaptedCellTranslate_zero] at hEll
  refine ⟨lam, 2 * Lam + 2 * ‖respg F‖ ^ 2 / lam, fun x => f x - respg F, hlam, ?_,
    isEllipticFieldOn_sub_skew hEll _ (respg_isSkew F), ?_⟩
  · have hn : (0:ℝ) ≤ 2 * ‖respg F‖ ^ 2 / lam := by positivity
    linarith
  · refine MeasureTheory.ae_restrict_of_ae ?_
    filter_upwards [hae] with x hx
    simp [respCoeffMinus, hx]

private theorem w3_elliptic_respCoeffPlus [NeZero d] (q : Mat d) (hq : IsUnit q) (t : ℤ)
    (F : BlockMat d) (a : CoeffSpace d) :
    ∃ (lam Lam : ℝ) (f : CoeffField d), 0 < lam ∧ lam ≤ Lam ∧
      IsEllipticFieldOn lam Lam (HighContrast.adaptedCell q t) f ∧
        respCoeffPlus F a =ᵐ[volumeMeasureOn (HighContrast.adaptedCell q t)] f := by
  obtain ⟨lam, Lam, f, hlam, hle, hEll, hae⟩ :=
    Annealed.exists_elliptic_representative_adapted q hq t 0 a
  rw [adaptedCellTranslate_zero] at hEll
  refine ⟨lam, 2 * Lam + 2 * ‖respg F‖ ^ 2 / lam, fun x => matTranspose (f x) + respg F, hlam, ?_,
    isEllipticFieldOn_transpose_add_skew hEll _ (respg_isSkew F), ?_⟩
  · have hn : (0:ℝ) ≤ 2 * ‖respg F‖ ^ 2 / lam := by positivity
    linarith
  · refine MeasureTheory.ae_restrict_of_ae ?_
    filter_upwards [hae] with x hx
    simp [respCoeffPlus, hx]

private theorem w3_volume_adaptedCellAtCenter_toReal_ne_zero {q : Mat d} (hq : IsUnit q) (k : ℤ)
    (w : Fin d → ℤ) : (volume (adaptedCellAtCenter q k w)).toReal ≠ 0 := by
  have hdet : (0:ℝ) < |q.det| :=
    abs_pos.mpr (IsUnit.ne_zero ((Matrix.isUnit_iff_isUnit_det q).mp hq))
  have : (volume (adaptedCellAtCenter q k w)).toReal = |q.det| * ((3 : ℝ) ^ k) ^ d := by
    rw [Geometry.volume_adaptedCellAtCenter, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (abs_nonneg _),
      ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ (3 : ℝ) ^ k)]
  rw [this]
  positivity

/-- The core summability statement. -/
private theorem w3_summable_centred_core [NeZero d] {q : Mat d} (hq : IsUnit q) (t : ℤ)
    {b : CoeffField d} (u : AHarmonicFunction b (HighContrast.adaptedCell q t))
    (hb : ∃ (lam Lam : ℝ) (f : CoeffField d), 0 < lam ∧ lam ≤ Lam ∧
      IsEllipticFieldOn lam Lam (HighContrast.adaptedCell q t) f ∧
        b =ᵐ[volumeMeasureOn (HighContrast.adaptedCell q t)] f)
    (A : BlockMat d) :
    Summable (besovTerm t (fun n w =>
      blockMatVecMul A (cellAverageFamily q t (optimizerField b u) n w -
        cellAverage (HighContrast.adaptedCell q t) (optimizerField b u)))) := by
  classical
  obtain ⟨hs1, hs2⟩ := w3_memVectorL2_optimizer_slots u hb
  have hUfin : volume (HighContrast.adaptedCell q t) ≠ ⊤ := by
    rw [Geometry.volume_adaptedCell]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  have : IsFiniteMeasure (volume.restrict (HighContrast.adaptedCell q t)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_of_le_of_ne le_top hUfin⟩
  set X : Vec d → BlockVec d := optimizerField b u with hXdef
  set C : BlockVec d := cellAverage (HighContrast.adaptedCell q t) X with hCdef
  set X' : Vec d → BlockVec d := fun x => blockMatVecMul A (X x - C) with hX'def
  have hd1 : MemVectorL2 (HighContrast.adaptedCell q t) (fun x => (X x).1 - C.1) :=
    hs1.sub (memLp_const C.1)
  have hd2 : MemVectorL2 (HighContrast.adaptedCell q t) (fun x => (X x).2 - C.2) :=
    hs2.sub (memLp_const C.2)
  have hX'1 : MemVectorL2 (HighContrast.adaptedCell q t) (fun x => (X' x).1) :=
    (w3_memVectorL2_matVecMul A.upperLeft hd1).add (w3_memVectorL2_matVecMul A.upperRight hd2)
  have hX'2 : MemVectorL2 (HighContrast.adaptedCell q t) (fun x => (X' x).2) :=
    (w3_memVectorL2_matVecMul A.lowerLeft hd1).add (w3_memVectorL2_matVecMul A.lowerRight hd2)
  have hX'mem : MemLp (fun x => blockVecDot (X' x) (X' x)) 1
      (volume.restrict (HighContrast.adaptedCell q t)) :=
    w3_memLp_one_blockVecDot hX'1 hX'2
  have hsum' := summable_besov_cellAverageFamily q hq t X' hX'mem
  refine hsum'.congr fun n => ?_
  have hV : ∀ w ∈ triadicIndexBox d n,
      cellAverageFamily q t X' n w = blockMatVecMul A (cellAverageFamily q t X n w - C) := by
    intro w hw
    have hsub : adaptedCellAtCenter q (t - (n : ℤ)) w ⊆ HighContrast.adaptedCell q t :=
      adaptedCellAtCenter_subset_adaptedCell q t n hw
    have hVfin : volume (adaptedCellAtCenter q (t - (n : ℤ)) w) ≠ ⊤ :=
      Geometry.volume_adaptedCellAtCenter_ne_top q (t - (n : ℤ)) w
    exact w3_cellAverage_blockMatVecMul_sub_const hVfin
      (w3_volume_adaptedCellAtCenter_toReal_ne_zero hq (t - (n : ℤ)) w) A X C
      (fun j => w3_integrableOn_slot hsub hVfin hs1 j)
      (fun j => w3_integrableOn_slot hsub hVfin hs2 j)
  have hsumeq : ∑ w ∈ triadicIndexBox d n,
        blockVecDot (cellAverageFamily q t X' n w) (cellAverageFamily q t X' n w)
      = ∑ w ∈ triadicIndexBox d n,
        blockVecDot (blockMatVecMul A (cellAverageFamily q t X n w - C))
          (blockMatVecMul A (cellAverageFamily q t X n w - C)) :=
    Finset.sum_congr rfl fun w hw => by rw [hV w hw]
  unfold besovTerm
  rw [hsumeq]

/-- Summability of the centred family of the optimizer field
(`summable_besov_cellAverageFamily`; if that lemma already has this shape this is a one-liner,
otherwise derive it from `avsum_cellAverageFamily_sq_le` and the geometric weight). -/
theorem summable_besovTerm_centred_minus [NeZero d] (P : Measure (CoeffSpace d)) (jStar : ℕ)
    (F : BlockMat d) (t : ℤ) (e : Vec d) (hgrid : IsUnit (respGrid jStar F)) (a : CoeffSpace d)
    (u : AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hu : IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a) u) :
    Summable (besovTerm t (fun n w =>
      blockMatVecMul (blockSqrt (respM0 F))
        (cellAverageFamily (respGrid jStar F) t (optimizerField (respCoeffMinus F a) u) n w -
          cellAverage (respCell jStar F t) (optimizerField (respCoeffMinus F a) u)))) := by
  have _huUsed := hu
  exact w3_summable_centred_core hgrid t u
    (w3_elliptic_respCoeffMinus (respGrid jStar F) hgrid t F a) (blockSqrt (respM0 F))

/-- The plus twin of the centred-family summability. -/
theorem summable_besovTerm_centred_plus [NeZero d] (P : Measure (CoeffSpace d)) (jStar : ℕ)
    (F : BlockMat d) (t : ℤ) (e : Vec d) (hgrid : IsUnit (respGrid jStar F)) (a : CoeffSpace d)
    (u : AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hu : IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a) u) :
    Summable (besovTerm t (fun n w =>
      blockMatVecMul (blockSqrt (respM0 F))
        (cellAverageFamily (respGrid jStar F) t (optimizerField (respCoeffPlus F a) u) n w -
          cellAverage (respCell jStar F t) (optimizerField (respCoeffPlus F a) u)))) := by
  have _huUsed := hu
  exact w3_summable_centred_core hgrid t u
    (w3_elliptic_respCoeffPlus (respGrid jStar F) hgrid t F a) (blockSqrt (respM0 F))

/-! ## The plus twin (`diagonalWeakNorm_primal_le` is minus only) -/

/-- Plus twin of `diagonalWeakNorm_primal_le`: same statement with
`respEhatPlus`, `respqPlus`, `respCoeffPlus`, `respLsqPlus`.  Paper `p.response.transfer`. -/
theorem diagonalWeakNorm_primal_le_plus [NeZero d] (P : Measure (CoeffSpace d))
    [IsProbabilityMeasure P] (γ : ℝ) (_hγ : γ ∈ Set.Ico (0 : ℝ) 1) (jStar H : ℕ) (F : BlockMat d)
    (t : ℤ) (e : Vec d) (hgrid : IsUnit (respGrid jStar F))
    (hint : HasIntegrableCoarseBlock P (respCell jStar F t)) (a : CoeffSpace d)
    (hbdd : BddAbove {y : ℝ | ∃ m : ℕ, ∃ z ∈ triadicIndexBox d m, y =
      (3 : ℝ) ^ (-(respRho γ * (m : ℝ))) *
        blockSpecBound (blockSub
          (normalizedBlock (coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) z) a)
            (respMean P jStar F t)) (Book.Ch02.blockIdentity d))})
    (u : AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hu : IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a) u) :
    (3 : ℝ) ^ (-((t : ℝ) / 2)) *
        besovSeminorm t (fun n w =>
          blockMatVecMul (blockSqrt (respM0 F))
            (cellAverageFamily (respGrid jStar F) t (optimizerField (respCoeffPlus F a) u) n w -
              cellAverage (respCell jStar F t) (optimizerField (respCoeffPlus F a) u))) ≤
      16 * Real.sqrt (blockSpecBound (normalizedBlock (respEhatPlus P jStar F t) (respM0 F))) *
          Real.sqrt (respLsqPlus P jStar F t e) *
          (weakCellSum (respGrid jStar F) t H (respEhatPlus P jStar F t) (respCoeffPlus F a) +
            weakAverageSum (respGrid jStar F) t H (respRho γ) (respEhatPlus P jStar F t)
              (respCoeffPlus F a)) +
        (16 / (1 - respRho γ) *
            Real.sqrt (blockSpecBound (normalizedBlock (respEhatPlus P jStar F t) (respM0 F)))) *
          (if 1 < respAllScaleMax P γ jStar F t a then
              Real.sqrt (respAllScaleMax P γ jStar F t a)
            else (3 : ℝ) ^ (-(respAlpha γ * (H : ℝ)))) *
          weakOptimizerEnergy (respCell jStar F t) (respCoeffPlus F a) u := by
  exact h6a_diagonalWeakNorm_primal_plus P γ _hγ jStar H F t e hgrid hint a hbdd u hu

/-! ### Local helper for the pathwise bound.

The only algebra the pathwise bound needs beyond `diagonalWeakNorm_primal_le`,
`besovSeminorm_add_const_le` and the summability of the centred family:
`M(v - Y) = M(v - C) + M(C - Y)`, i.e. the `p.response.transfer` recentring of the Besov family from the
pathwise cell average `C = ⟨X_a⟩_{U_t}` to the annealed centre `Y^±`.  The same step appears in
`ProfileWeakSplit.lean`
(`normalized_primal_weak_split` / `profilePrimalWeakRoot_le_randomCentered_add_constant`), where
it is carried by `blockCellAverage_metricRoot_sub_const_diagonalWeakState`; there it is an
`ℝ≥0∞` `tsum` split (`ENNReal.tsum_add`), here it is `besovSeminorm_add_const_le`, which is
why the real-valued route needs the centred-family summability and the `ℝ≥0∞` route did not. -/

private theorem w3_blockMatVecMul_sub_split (M : BlockMat d) (v c y : BlockVec d) :
    blockMatVecMul M (v - y) = blockMatVecMul M (v - c) + blockMatVecMul M (c - y) := by
  refine Prod.ext ?_ ?_ <;> funext i <;>
    simp [blockMatVecMul, matVecMul, Pi.sub_apply, Pi.add_apply, mul_sub,
      Finset.sum_sub_distrib] <;> ring

/-! ## The pathwise bound relative to `Y^±` (`p.response.transfer`) -/

/-- For one `a`: `diagonalWeakNorm_primal_le` for the centred family, `besovSeminorm_add_const_le` with
`c = respRecentreMinus`, the summability of the centred family, and the linearity
`blockMatVecMul M (v - w) = blockMatVecMul M v - blockMatVecMul M w`
(`cellAverageFamily` is `rfl` the cell average at `adaptedCellAtCenter q (t-n) w`).  The constant term
is `3^{-t/2} · 3^{t/2}|c|/(1-3^{-1/2})`. -/
theorem besov_pathwise_le_minus [NeZero d] (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1) (jStar H : ℕ) (F : BlockMat d) (t : ℤ) (e : Vec d)
    (hgrid : IsUnit (respGrid jStar F))
    (hint : HasIntegrableCoarseBlock P (respCell jStar F t)) (a : CoeffSpace d)
    (hbdd : BddAbove {y : ℝ | ∃ m : ℕ, ∃ z ∈ triadicIndexBox d m, y =
      (3 : ℝ) ^ (-(respRho γ * (m : ℝ))) *
        blockSpecBound (blockSub
          (normalizedBlock (coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) z) a)
            (respMean P jStar F t)) (Book.Ch02.blockIdentity d))})
    (u : AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hu : IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a) u) :
    (3 : ℝ) ^ (-((t : ℝ) / 2)) *
        besovSeminorm t (fun n z =>
          blockMatVecMul (blockSqrt (respM0 F))
            (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z)
              (optimizerField (respCoeffMinus F a) u) - respYMinus P jStar F t e)) ≤
      16 * Real.sqrt (respK0SqMinus P jStar F t) * Real.sqrt (respLsqMinus P jStar F t e) *
          (weakCellSum (respGrid jStar F) t H (respEhatMinus P jStar F t) (respCoeffMinus F a) +
            weakAverageSum (respGrid jStar F) t H (respRho γ) (respEhatMinus P jStar F t)
              (respCoeffMinus F a)) +
        (16 / (1 - respRho γ) * Real.sqrt (respK0SqMinus P jStar F t)) *
          (if 1 < respAllScaleMax P γ jStar F t a then
              Real.sqrt (respAllScaleMax P γ jStar F t a)
            else (3 : ℝ) ^ (-(respAlpha γ * (H : ℝ)))) *
          weakOptimizerEnergy (respCell jStar F t) (respCoeffMinus F a) u +
        (1 / (1 - (3 : ℝ) ^ (-(1 / 2 : ℝ)))) *
          Real.sqrt (blockVecDot (respRecentreMinus P jStar F t e a u)
            (respRecentreMinus P jStar F t e a u)) := by
  classical
  have hH6a := diagonalWeakNorm_primal_le P γ hγ jStar H F t e hgrid hint a hbdd u hu
  set M : BlockMat d := blockSqrt (respM0 F) with hM
  set X : Vec d → BlockVec d := optimizerField (respCoeffMinus F a) u with hX
  set C : BlockVec d := cellAverage (respCell jStar F t) X with hC
  set Y : BlockVec d := respYMinus P jStar F t e with hY
  set A : ℕ → (Fin d → ℤ) → BlockVec d :=
    fun n w => blockMatVecMul M (cellAverageFamily (respGrid jStar F) t X n w - C) with hA
  set c : BlockVec d := blockMatVecMul M (C - Y) with hc
  have hfam : (fun (n : ℕ) (z : Fin d → ℤ) => blockMatVecMul M
      (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z) X - Y))
      = fun n w => A n w + c := by
    funext n z
    exact w3_blockMatVecMul_sub_split M _ C Y
  rw [hfam]
  have hsum : Summable (besovTerm t A) :=
    summable_besovTerm_centred_minus P jStar F t e hgrid a u hu
  have hmink := besovSeminorm_add_const_le t A c hsum
  have hnn : (0 : ℝ) ≤ (3 : ℝ) ^ (-((t : ℝ) / 2)) := Real.rpow_nonneg (by norm_num) _
  have hstep := mul_le_mul_of_nonneg_left hmink hnn
  have hcancel : (3 : ℝ) ^ (-((t : ℝ) / 2)) * ((3 : ℝ) ^ ((t : ℝ) / 2) /
      (1 - (3 : ℝ) ^ (-(1 / 2 : ℝ))) * Real.sqrt (blockVecDot c c))
      = (1 / (1 - (3 : ℝ) ^ (-(1 / 2 : ℝ)))) * Real.sqrt (blockVecDot c c) := by
    rw [show (3 : ℝ) ^ ((t : ℝ) / 2) / (1 - (3 : ℝ) ^ (-(1 / 2 : ℝ)))
        = (3 : ℝ) ^ ((t : ℝ) / 2) * (1 - (3 : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹ from div_eq_mul_inv _ _]
    rw [← mul_assoc, ← mul_assoc, ← Real.rpow_add (by norm_num : (0:ℝ) < 3)]
    norm_num
  rw [mul_add, hcancel] at hstep
  have hK : respK0SqMinus P jStar F t
      = blockSpecBound (normalizedBlock (respEhatMinus P jStar F t) (respM0 F)) := rfl
  have hcdef : respRecentreMinus P jStar F t e a u = c := rfl
  rw [hK, hcdef]
  linarith [hstep, hH6a]

/-- The plus twin of the pathwise bound (uses `diagonalWeakNorm_primal_le_plus` and
`summable_besovTerm_centred_plus`). -/
theorem besov_pathwise_le_plus [NeZero d] (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1) (jStar H : ℕ) (F : BlockMat d) (t : ℤ) (e : Vec d)
    (hgrid : IsUnit (respGrid jStar F))
    (hint : HasIntegrableCoarseBlock P (respCell jStar F t)) (a : CoeffSpace d)
    (hbdd : BddAbove {y : ℝ | ∃ m : ℕ, ∃ z ∈ triadicIndexBox d m, y =
      (3 : ℝ) ^ (-(respRho γ * (m : ℝ))) *
        blockSpecBound (blockSub
          (normalizedBlock (coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) z) a)
            (respMean P jStar F t)) (Book.Ch02.blockIdentity d))})
    (u : AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hu : IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a) u) :
    (3 : ℝ) ^ (-((t : ℝ) / 2)) *
        besovSeminorm t (fun n z =>
          blockMatVecMul (blockSqrt (respM0 F))
            (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z)
              (optimizerField (respCoeffPlus F a) u) - respYPlus P jStar F t e)) ≤
      16 * Real.sqrt (respK0SqPlus P jStar F t) * Real.sqrt (respLsqPlus P jStar F t e) *
          (weakCellSum (respGrid jStar F) t H (respEhatPlus P jStar F t) (respCoeffPlus F a) +
            weakAverageSum (respGrid jStar F) t H (respRho γ) (respEhatPlus P jStar F t)
              (respCoeffPlus F a)) +
        (16 / (1 - respRho γ) * Real.sqrt (respK0SqPlus P jStar F t)) *
          (if 1 < respAllScaleMax P γ jStar F t a then
              Real.sqrt (respAllScaleMax P γ jStar F t a)
            else (3 : ℝ) ^ (-(respAlpha γ * (H : ℝ)))) *
          weakOptimizerEnergy (respCell jStar F t) (respCoeffPlus F a) u +
        (1 / (1 - (3 : ℝ) ^ (-(1 / 2 : ℝ)))) *
          Real.sqrt (blockVecDot (respRecentrePlus P jStar F t e a u)
            (respRecentrePlus P jStar F t e a u)) := by
  classical
  have hH6a := diagonalWeakNorm_primal_le_plus P γ hγ jStar H F t e hgrid hint a hbdd u hu
  set M : BlockMat d := blockSqrt (respM0 F) with hM
  set X : Vec d → BlockVec d := optimizerField (respCoeffPlus F a) u with hX
  set C : BlockVec d := cellAverage (respCell jStar F t) X with hC
  set Y : BlockVec d := respYPlus P jStar F t e with hY
  set A : ℕ → (Fin d → ℤ) → BlockVec d :=
    fun n w => blockMatVecMul M (cellAverageFamily (respGrid jStar F) t X n w - C) with hA
  set c : BlockVec d := blockMatVecMul M (C - Y) with hc
  have hfam : (fun (n : ℕ) (z : Fin d → ℤ) => blockMatVecMul M
      (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z) X - Y))
      = fun n w => A n w + c := by
    funext n z
    exact w3_blockMatVecMul_sub_split M _ C Y
  rw [hfam]
  have hsum : Summable (besovTerm t A) :=
    summable_besovTerm_centred_plus P jStar F t e hgrid a u hu
  have hmink := besovSeminorm_add_const_le t A c hsum
  have hnn : (0 : ℝ) ≤ (3 : ℝ) ^ (-((t : ℝ) / 2)) := Real.rpow_nonneg (by norm_num) _
  have hstep := mul_le_mul_of_nonneg_left hmink hnn
  have hcancel : (3 : ℝ) ^ (-((t : ℝ) / 2)) * ((3 : ℝ) ^ ((t : ℝ) / 2) /
      (1 - (3 : ℝ) ^ (-(1 / 2 : ℝ))) * Real.sqrt (blockVecDot c c))
      = (1 / (1 - (3 : ℝ) ^ (-(1 / 2 : ℝ)))) * Real.sqrt (blockVecDot c c) := by
    rw [show (3 : ℝ) ^ ((t : ℝ) / 2) / (1 - (3 : ℝ) ^ (-(1 / 2 : ℝ)))
        = (3 : ℝ) ^ ((t : ℝ) / 2) * (1 - (3 : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹ from div_eq_mul_inv _ _]
    rw [← mul_assoc, ← mul_assoc, ← Real.rpow_add (by norm_num : (0:ℝ) < 3)]
    norm_num
  rw [mul_add, hcancel] at hstep
  have hK : respK0SqPlus P jStar F t
      = blockSpecBound (normalizedBlock (respEhatPlus P jStar F t) (respM0 F)) := rfl
  have hcdef : respRecentrePlus P jStar F t e a u = c := rfl
  rw [hK, hcdef]
  linarith [hstep, hH6a]

