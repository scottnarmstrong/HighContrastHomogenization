import HCPoly.Entry.Analysis.SingularValueMoments
import HCPoly.Entry.Analysis.SingularValueApproximation
import HCPoly.Entry.Analysis.SchattenTraceHolder

/-!
# Lossy trace Holder for singular norms

This file proves the dimension-free lossy product bound used in the trace
Holder route. The loss is the word length `N`, not the matrix dimension.
-/

namespace Homogenization.HighContrast.Analysis

open scoped BigOperators Matrix.Norms.L2Operator

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem list_prod_norm_le {N : ℕ} (A : Fin N → Matrix n n ℝ) :
    ‖(List.ofFn A).prod‖ ≤ ∏ k : Fin N, ‖A k‖ := by
  induction N with
  | zero =>
      rw [List.ofFn_zero, List.prod_nil, Fintype.prod_empty]
      by_cases hn : Nonempty n
      · let := hn
        exact le_of_eq CStarRing.norm_one
      · let : IsEmpty n := not_nonempty_iff.mp hn
        have : Subsingleton (Matrix n n ℝ) := inferInstance
        rw [Subsingleton.elim (1 : Matrix n n ℝ) 0, norm_zero]
        norm_num
  | succ N ih =>
      rw [List.ofFn_succ, List.prod_cons, Fin.prod_univ_succ]
      exact (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_left (ih (fun k => A k.succ)) (norm_nonneg _))

theorem rank_prod_sub_prod_le {N : ℕ}
    (A C : Fin N → Matrix n n ℝ) :
    ((List.ofFn A).prod - (List.ofFn C).prod).rank ≤
      ∑ k, (A k - C k).rank := by
  induction N with
  | zero =>
      simp [Matrix.rank_zero]
  | succ N ih =>
      let Atail : Fin N → Matrix n n ℝ := fun k => A k.succ
      let Ctail : Fin N → Matrix n n ℝ := fun k => C k.succ
      have hprodA :
          (List.ofFn A).prod = A 0 * (List.ofFn Atail).prod := by
        simp only [Atail]
        rw [List.ofFn_succ, List.prod_cons]
      have hprodC :
          (List.ofFn C).prod = C 0 * (List.ofFn Ctail).prod := by
        simp only [Ctail]
        rw [List.ofFn_succ, List.prod_cons]
      have hdecomp :
          (List.ofFn A).prod - (List.ofFn C).prod =
            (A 0 - C 0) * (List.ofFn Atail).prod +
              C 0 * ((List.ofFn Atail).prod - (List.ofFn Ctail).prod) := by
        rw [hprodA, hprodC]
        noncomm_ring
      rw [hdecomp, Fin.sum_univ_succ]
      calc
        ((A 0 - C 0) * (List.ofFn Atail).prod +
              C 0 * ((List.ofFn Atail).prod - (List.ofFn Ctail).prod)).rank
            ≤ ((A 0 - C 0) * (List.ofFn Atail).prod).rank +
                (C 0 * ((List.ofFn Atail).prod - (List.ofFn Ctail).prod)).rank :=
              rank_add_le _ _
        _ ≤ (A 0 - C 0).rank +
                ((List.ofFn Atail).prod - (List.ofFn Ctail).prod).rank := by
              exact Nat.add_le_add (Matrix.rank_mul_le_left _ _) (Matrix.rank_mul_le_right _ _)
        _ ≤ (A 0 - C 0).rank + ∑ k : Fin N, (Atail k - Ctail k).rank := by
              exact Nat.add_le_add_left (ih Atail Ctail) _
        _ = (A 0 - C 0).rank + ∑ k : Fin N, (A k.succ - C k.succ).rank := rfl

private theorem sum_comp_div_le_card_mul_sum {D N : ℕ} (hN : 0 < N)
    (v : ℕ → ℝ) (hv : ∀ i, 0 ≤ v i) :
    ∑ i ∈ Finset.range D, v (i / N) ≤
      (N : ℝ) * ∑ r ∈ Finset.range D, v r := by
  classical
  calc
    ∑ i ∈ Finset.range D, v (i / N)
        = ∑ r ∈ Finset.range D, ∑ i ∈ (Finset.range D).filter (fun i => i / N = r), v r := by
            exact (Finset.sum_fiberwise_of_maps_to'
              (s := Finset.range D) (t := Finset.range D)
              (g := fun i => i / N)
              (fun i hi => Finset.mem_range.2 ((Nat.div_le_self i N).trans_lt
                (Finset.mem_range.1 hi)))
              v).symm
    _ ≤ ∑ r ∈ Finset.range D, (N : ℝ) * v r := by
            refine Finset.sum_le_sum fun r hr => ?_
            have hcard :
                ((Finset.range D).filter (fun i => i / N = r)).card ≤ N := by
              have hcard' :
                  ((Finset.range D).filter (fun i => i / N = r)).card ≤
                    (Finset.range N).card := by
                refine Finset.card_le_card_of_injOn (fun i => i % N) ?_ ?_
                · intro i hi
                  exact Finset.mem_range.2 (Nat.mod_lt i hN)
                · intro a ha b hb hab
                  simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at ha hb
                  have hmod : a % N = b % N := hab
                  calc
                    a = N * (a / N) + a % N := (Nat.div_add_mod a N).symm
                    _ = N * (b / N) + b % N := by rw [ha.2, hb.2, hmod]
                    _ = b := Nat.div_add_mod b N
              simpa [Finset.card_range] using hcard'
            rw [Finset.sum_const, nsmul_eq_mul]
            exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (hv r)
    _ = (N : ℝ) * ∑ r ∈ Finset.range D, v r := by
            rw [Finset.mul_sum]

theorem sum_block_bound {D N : ℕ} (hN : 0 < N) (u v : ℕ → ℝ)
    (hu : Antitone u) (hv : ∀ i, 0 ≤ v i) (h : ∀ r, u (N*r) ≤ v r) :
    ∑ i ∈ Finset.range D, u i ≤ (N:ℝ) * ∑ r ∈ Finset.range D, v r := by
  calc
    ∑ i ∈ Finset.range D, u i ≤ ∑ i ∈ Finset.range D, v (i / N) := by
      refine Finset.sum_le_sum fun i _ => ?_
      exact (hu (Nat.mul_div_le i N)).trans (by simpa [Nat.mul_comm] using h (i / N))
    _ ≤ (N:ℝ) * ∑ r ∈ Finset.range D, v r :=
      sum_comp_div_le_card_mul_sum hN v hv

theorem singularValueAt_prod_le {N : ℕ} (hN : 0 < N)
    (A : Fin N → Matrix n n ℝ) (r : ℕ) :
    singularValueAt ((List.ofFn A).prod) (N*r) ≤ ∏ k, singularValueAt (A k) r := by
  classical
  cases N with
  | zero => omega
  | succ N =>
      choose R hRrank hRnorm using fun k : Fin (N + 1) => exists_rank_approximation (A k) r
      let C : Fin (N + 1) → Matrix n n ℝ := fun k => A k - R k
      let X : Matrix n n ℝ := (List.ofFn A).prod
      let Y : Matrix n n ℝ := X - (List.ofFn C).prod
      have hYrank : Y.rank ≤ (N + 1) * r := by
        calc
          Y.rank ≤ ∑ k, (A k - C k).rank := by
            simpa [X, Y] using rank_prod_sub_prod_le A C
          _ = ∑ k, (R k).rank := by
            refine Finset.sum_congr rfl fun k _ => ?_
            simp [C]
          _ ≤ ∑ _k : Fin (N + 1), r := Finset.sum_le_sum fun k _ => hRrank k
          _ = (N + 1) * r := by
            simp [Finset.sum_const]
      have happrox := singularValueAt_le_norm_sub X Y hYrank
      have hres : X - Y = (List.ofFn C).prod := by
        simp [Y]
      have hnorm :
          ‖X - Y‖ ≤ ∏ k, singularValueAt (A k) r := by
        rw [hres]
        exact (list_prod_norm_le C).trans
          (Finset.prod_le_prod (fun k _ => norm_nonneg (C k)) fun k _ => by
            simpa [C] using hRnorm k)
      exact happrox.trans hnorm

private theorem sum_range_singularValueAt_eq_sum_singularValues₀
    (X : Matrix n n ℝ) (f : ℝ → ℝ) :
    ∑ r ∈ Finset.range (Fintype.card n), f (singularValueAt X r) =
      ∑ i : Fin (Fintype.card n), f (singularValues₀ X i) := by
  rw [← Fin.sum_univ_eq_sum_range]
  exact Finset.sum_congr rfl fun i _ => by
    simp [singularValueAt]

private theorem sum_range_singularValueAt_rpow_eq_sum_singularValues
    (X : Matrix n n ℝ) (p : ℝ) :
    ∑ r ∈ Finset.range (Fintype.card n), singularValueAt X r ^ p =
      ∑ i, singularValues X i ^ p := by
  calc
    ∑ r ∈ Finset.range (Fintype.card n), singularValueAt X r ^ p =
        ∑ i : Fin (Fintype.card n), singularValues₀ X i ^ p :=
      sum_range_singularValueAt_eq_sum_singularValues₀ X (fun x => x ^ p)
    _ = ∑ i, singularValues X i ^ p :=
      sum_singularValues₀ X (fun x => x ^ p)

theorem abs_trace_prod_le_card_mul_prod_singularNorm {N : ℕ} (hN : 0 < N)
    (A : Fin N → Matrix n n ℝ) :
    |Matrix.trace ((List.ofFn A).prod)| ≤
      (N:ℝ) * ∏ k, singularNorm (N:ℝ) (A k) := by
  let X : Matrix n n ℝ := (List.ofFn A).prod
  let D := Fintype.card n
  have hNRnonneg : (0 : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.zero_le N
  calc
    |Matrix.trace ((List.ofFn A).prod)|
        ≤ ∑ i : Fin D, singularValues₀ X i := by
            exact abs_trace_le_sum_singularValues₀ X
    _ = ∑ i ∈ Finset.range D, singularValueAt X i := by
            exact (sum_range_singularValueAt_eq_sum_singularValues₀ X (fun x => x)).symm
    _ ≤ (N:ℝ) * ∑ r ∈ Finset.range D, ∏ k, singularValueAt (A k) r :=
            sum_block_bound hN (singularValueAt X)
              (fun r => ∏ k, singularValueAt (A k) r)
              (singularValueAt_antitone X)
              (fun r => Finset.prod_nonneg fun k _ => singularValueAt_nonneg (A k) r)
              (fun r => singularValueAt_prod_le hN A r)
    _ ≤ (N:ℝ) * ∏ k, (∑ r ∈ Finset.range D,
            singularValueAt (A k) r ^ (N : ℝ)) ^ ((N : ℝ)⁻¹) := by
            exact mul_le_mul_of_nonneg_left
              (sum_prod_le_prod_sum_rpow hN (Finset.range D)
                (fun k r => singularValueAt (A k) r)
                (fun k r _ => singularValueAt_nonneg (A k) r))
              hNRnonneg
    _ = (N:ℝ) * ∏ k, singularNorm (N:ℝ) (A k) := by
            congr 1
            refine Finset.prod_congr rfl fun k _ => ?_
            unfold singularNorm
            rw [sum_range_singularValueAt_rpow_eq_sum_singularValues (A k) (N : ℝ)]

end

end Homogenization.HighContrast.Analysis
