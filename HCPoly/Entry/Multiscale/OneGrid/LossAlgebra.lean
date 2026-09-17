import HCPoly.Entry.Multiscale.OneGrid.ExponentArithmetic

/-!
# Log-determinant loss algebra and the multiplicity bound

Group B of the printed proof (`p.fixed.geometry.one.grid.propagation`): additivity of the
log-determinant loss, its comparison with the synchronized loss, and **conjunct 7**,
`e.fixed.geometry.synchronized.multiplicity`.

Part of the proof of `HCPoly/Entry/Statements/OneGridPropagation.lean`.  Conventions of this group:
`q = 𝒬(𝔪)` is `Geometry.explicitRoundedGrid jStar metric` at every loss, history, profile and drift;
`metric` (not `m`) names the positive matrix, because `m`, `n`, `m₀` are generations; the
source lower scale `e.source.lower.scale` is carried exactly by the
`HCPoly/Entry/OneGridPropagation.lean`; this group's stronger internal
algebraic and history lemmas omit an unused threshold, and this group's generic
integration helpers take finiteness, integrability or measurability inputs that are proved
at their actual use sites, not extra premises of the printed proposition.
-/

open Homogenization.HighContrast (CoeffSpace)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-! ## Group B. Log-determinant loss algebra and the multiplicity bound
(`p.fixed.geometry.one.grid.propagation`) -/

/-- `Δ^q_{j-h,m+h} ≤ Δ̂^q_h(m)` for `m < j ≤ m+h` (`p.fixed.geometry.one.grid.propagation`).  Taking `j = m+h` gives
the `Δ^q_{m,m+h} ≤ Δ̂^q_h(m)` used in Step 3. -/
theorem logDetLoss_le_synchronizedLogDetLoss (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (_hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
      (S : CoeffSpace d → ℝ),
      IsProbabilityMeasure P →
      IsStationaryLaw P →
      IsUnitRangeLaw P →
      CoarseEllipticityDagger P γ E Ψ K S →
      ∀ (h : ℕ), 1 ≤ h →
        ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
          ∀ (metric : Mat d), metric.PosDef →
            ∀ m j : ℤ, (jStar : ℤ) + (h : ℤ) ≤ m → m < j → j ≤ m + (h : ℤ) →
              logDetLoss P (Geometry.explicitRoundedGrid jStar metric) (j - (h : ℤ)) (m + (h : ℤ)) ≤
                synchronizedLogDetLoss P (Geometry.explicitRoundedGrid jStar metric) (h : ℤ) m := by
  intro P E Ψ K S hP hstat _hunit hdag h hh jStar hjStar metric hmetric m j hm1 hmj hjm
  unfold synchronizedLogDetLoss
  have Hnonneg : ∀ a b : ℤ, (jStar : ℤ) ≤ a → a ≤ b →
      0 ≤ logDetLoss P (Geometry.explicitRoundedGrid jStar metric) a b := fun a b ha hab =>
    Annealed.logDetLoss_nonneg d hd P γ E Ψ K S hstat hdag jStar hjStar metric hmetric a b ha hab
  by_cases hcase : j = m + (h : ℤ)
  · subst hcase
    have hmem : (m + (h : ℤ)) ∈ Finset.Icc (m + 1) (m + (h : ℤ)) :=
      Finset.mem_Icc.mpr (by omega)
    have hnonneg' : ∀ a ∈ Finset.Icc (m + 1) (m + (h : ℤ)),
        0 ≤ logDetLoss P (Geometry.explicitRoundedGrid jStar metric) (a - (h : ℤ)) a := by
      intro a ha
      rw [Finset.mem_Icc] at ha
      exact Hnonneg (a - (h : ℤ)) a (by omega) (by omega)
    exact Finset.single_le_sum hnonneg' hmem
  · have hjmem : j ∈ Finset.Icc (m + 1) (m + (h : ℤ)) := Finset.mem_Icc.mpr (by omega)
    have hmhmem : (m + (h : ℤ)) ∈ Finset.Icc (m + 1) (m + (h : ℤ)) :=
      Finset.mem_Icc.mpr (by omega)
    have hnonneg' : ∀ a ∈ Finset.Icc (m + 1) (m + (h : ℤ)),
        0 ≤ logDetLoss P (Geometry.explicitRoundedGrid jStar metric) (a - (h : ℤ)) a := by
      intro a ha
      rw [Finset.mem_Icc] at ha
      exact Hnonneg (a - (h : ℤ)) a (by omega) (by omega)
    have hsplit :
        logDetLoss P (Geometry.explicitRoundedGrid jStar metric) (j - (h : ℤ)) (m + (h : ℤ))
          = logDetLoss P (Geometry.explicitRoundedGrid jStar metric) (j - (h : ℤ)) j +
            logDetLoss P (Geometry.explicitRoundedGrid jStar metric) j (m + (h : ℤ)) :=
      (logDetLoss_add P (Geometry.explicitRoundedGrid jStar metric) (j - (h : ℤ)) j (m + (h : ℤ))).symm
    have hextendEq :
        logDetLoss P (Geometry.explicitRoundedGrid jStar metric) m (m + (h : ℤ))
          = logDetLoss P (Geometry.explicitRoundedGrid jStar metric) m j +
            logDetLoss P (Geometry.explicitRoundedGrid jStar metric) j (m + (h : ℤ)) :=
      (logDetLoss_add P (Geometry.explicitRoundedGrid jStar metric) m j (m + (h : ℤ))).symm
    have hmj_nonneg : 0 ≤ logDetLoss P (Geometry.explicitRoundedGrid jStar metric) m j :=
      Hnonneg m j (by omega) (le_of_lt hmj)
    have hextend :
        logDetLoss P (Geometry.explicitRoundedGrid jStar metric) j (m + (h : ℤ))
          ≤ logDetLoss P (Geometry.explicitRoundedGrid jStar metric) m (m + (h : ℤ)) := by
      linarith [hextendEq]
    have hsub : ({j, m + (h : ℤ)} : Finset ℤ) ⊆ Finset.Icc (m + 1) (m + (h : ℤ)) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with hx | hx
      · rw [hx]; exact hjmem
      · rw [hx]; exact hmhmem
    have hle :
        ∑ a ∈ ({j, m + (h : ℤ)} : Finset ℤ),
            logDetLoss P (Geometry.explicitRoundedGrid jStar metric) (a - (h : ℤ)) a
          ≤ ∑ a ∈ Finset.Icc (m + 1) (m + (h : ℤ)),
              logDetLoss P (Geometry.explicitRoundedGrid jStar metric) (a - (h : ℤ)) a :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun a ha _ => hnonneg' a ha)
    rw [Finset.sum_pair hcase] at hle
    have hmhh : (m + (h : ℤ) - (h : ℤ)) = m := by ring
    rw [hmhh] at hle
    linarith [hsplit, hextend, hle]

/-- **Conjunct 7**, `e.fixed.geometry.synchronized.multiplicity` (`p.fixed.geometry.one.grid.propagation`): expand the synchronized losses into adjacent increments, observe that the smallest
index is at least `j_*` and that each increment occurs at most `h` times. -/
theorem synchronized_multiplicity (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
      (S : CoeffSpace d → ℝ),
      IsProbabilityMeasure P →
      IsStationaryLaw P →
      IsUnitRangeLaw P →
      CoarseEllipticityDagger P γ E Ψ K S →
      ∀ (h : ℕ), 2 * bigQ d γ ≤ h →
        ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
          ∀ (metric : Mat d), metric.PosDef →
            ∀ m₀ : ℤ, (jStar : ℤ) + (h : ℤ) ≤ m₀ →
              ∀ Ksteps : ℕ, 1 ≤ Ksteps →
                ∑ k ∈ Finset.range Ksteps,
                    synchronizedLogDetLoss P (Geometry.explicitRoundedGrid jStar metric) (h : ℤ)
                      (m₀ + (k : ℤ) * (h : ℤ)) ≤
                  (h : ℝ) *
                    logDetLoss P (Geometry.explicitRoundedGrid jStar metric)
                      (m₀ + 1 - (h : ℤ)) (m₀ + (Ksteps : ℤ) * (h : ℤ)) := by
  intro P E Ψ K S hP hstat _hunit hdag h hh jStar hjStar metric hmetric m₀ hm₀ Ksteps _hK
  let := hP
  set q := Geometry.explicitRoundedGrid jStar metric
  have hhpos : 1 ≤ h := by
    have := bigQ_twelve_le d hd γ hγ
    omega
  have hnonneg (a b : ℤ) (ha : (jStar : ℤ) ≤ a) (hab : a ≤ b) :
      0 ≤ logDetLoss P q a b :=
    Annealed.logDetLoss_nonneg d hd P γ E Ψ K S hstat hdag
      jStar hjStar metric hmetric a b ha hab
  have hsum (b : ℤ) (N : ℕ) :
      ∑ k ∈ Finset.range N,
        logDetLoss P q (b + (k : ℤ) * (h : ℤ)) (b + ((k : ℤ) + 1) * (h : ℤ)) =
      logDetLoss P q b (b + (N : ℤ) * (h : ℤ)) := by
    induction N with
    | zero => simp [logDetLoss]
    | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      exact logDetLoss_add P q _ _ _
  have hblock (b : ℤ) : synchronizedLogDetLoss P q (h : ℤ) b =
      ∑ t ∈ Finset.range h, logDetLoss P q (b + 1 + (t : ℤ) - (h : ℤ))
        (b + 1 + (t : ℤ)) := by
    unfold synchronizedLogDetLoss
    symm
    apply Finset.sum_bij (fun (t : ℕ) _ => b + 1 + (t : ℤ))
    · intro t ht
      simp only [Finset.mem_range] at ht
      simp only [Finset.mem_Icc]
      omega
    · intro t ht u hu heq
      omega
    · intro a ha
      simp only [Finset.mem_Icc] at ha
      refine ⟨(a - (b + 1)).toNat, ?_, ?_⟩
      · simp only [Finset.mem_range]
        omega
      · omega
    · intro t _
      rfl
  simp_rw [hblock]
  rw [Finset.sum_comm]
  have hform (t k : ℕ) :
      logDetLoss P q (m₀ + (k : ℤ) * (h : ℤ) + 1 + (t : ℤ) - (h : ℤ))
        (m₀ + (k : ℤ) * (h : ℤ) + 1 + (t : ℤ)) =
      logDetLoss P q (m₀ + 1 + (t : ℤ) - (h : ℤ) + (k : ℤ) * (h : ℤ))
        (m₀ + 1 + (t : ℤ) - (h : ℤ) + ((k : ℤ) + 1) * (h : ℤ)) := by
    congr 1 <;> ring
  simp_rw [hform, hsum]
  calc
    _ ≤ ∑ _t ∈ Finset.range h,
        logDetLoss P q (m₀ + 1 - (h : ℤ)) (m₀ + (Ksteps : ℤ) * (h : ℤ)) := by
      apply Finset.sum_le_sum
      intro t ht
      have ht' := Finset.mem_range.mp ht
      have hmul : (0 : ℤ) ≤ (Ksteps : ℤ) * (h : ℤ) := mul_nonneg (by omega) (by omega)
      have hleft := hnonneg (m₀ + 1 - (h : ℤ)) (m₀ + 1 + (t : ℤ) - (h : ℤ))
        (by omega) (by omega)
      have hright := hnonneg (m₀ + 1 + (t : ℤ) - (h : ℤ) + (Ksteps : ℤ) * (h : ℤ))
        (m₀ + (Ksteps : ℤ) * (h : ℤ)) (by omega) (by omega)
      have h₁ := logDetLoss_add P q (m₀ + 1 - (h : ℤ))
        (m₀ + 1 + (t : ℤ) - (h : ℤ))
        (m₀ + 1 + (t : ℤ) - (h : ℤ) + (Ksteps : ℤ) * (h : ℤ))
      have h₂ := logDetLoss_add P q (m₀ + 1 - (h : ℤ))
        (m₀ + 1 + (t : ℤ) - (h : ℤ) + (Ksteps : ℤ) * (h : ℤ))
        (m₀ + (Ksteps : ℤ) * (h : ℤ))
      linarith only [hleft, hright, h₁, h₂]
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end

end Homogenization.HighContrast.Multiscale
