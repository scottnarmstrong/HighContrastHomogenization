import HCPoly.Entry.Multiscale.ResponseInputs.AdaptedDefs

/-!
# The centred three-row form of the integrated cutoff decomposition (AK.HC (3.45)-(3.54))

The cutoff pairing at a sample coefficient expands pathwise into the cutoff half-energy, the two
cutoff-mean pairings and half the self-pairing of the annealed mean `Y`.  Integrating that
expansion against the law `P` and rearranging gives the identity

`∫J - (1/2) Y₁ · Y₂ = ∫A - ∫(E - J) + (1/2) <∫M₁ - Y₁, Y₂> + (1/2) <Y₁, ∫M₂ - Y₂>`,

whose three rows are the cutoff pairing, the cutoff energy defect and the CENTRED cutoff-mean
row.  Centring the mean row is the mean cancellation of AK.HC (3.45)-(3.54): when the cutoff has
cell average one and the inserted loads are the actual annealed means, `∫M - Y` is the annealed
`(φ - 1)`-weighted mean and is small, whereas the uncentred row is not.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The integral of `vecDot (M a) Y` over `P` is the dot product of `Y` with the vector of
coordinate integrals of `M`: the Fubini step identifying one mean pairing of the integrated
cutoff decomposition of `e.response.cutoff.estimate` (AK.HC (3.45)-(3.54)). -/
theorem integral_vecDot_coord {d : ℕ} {α : Type*} [MeasurableSpace α]
    (P : Measure α) (M : α → Vec d) (Y : Vec d)
    (hM : ∀ i, Integrable (fun a => M a i) P) :
    (∫ a, vecDot (M a) Y ∂P) = vecDot (fun i => ∫ a, M a i ∂P) Y := by
  simp only [vecDot]
  rw [integral_finsetSum Finset.univ (fun i _ => (hM i).mul_const (Y i))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [integral_mul_const]

/-- **The centred three-row integrated cutoff decomposition** (`e.response.cutoff.estimate`,
AK.HC (3.45)-(3.54)).  If the half-pairing `A` is pathwise the affine combination
`E - (1/2) M₁ · Y₂ - (1/2) Y₁ · M₂ + (1/2) Y₁ · Y₂` of the half-energy `E`, the cutoff-mean
coordinates `M₁, M₂`, the annealed mean `Y` and the constant `(1/2) Y₁ · Y₂`, then integrating
against the probability law `P` and identifying the integrated mean pairings by Fubini bounds the
centred response `∫J - (1/2) Y₁ · Y₂` by the absolute cutoff pairing `|∫A|`, the absolute cutoff
energy defect `|∫(E - J)|` and the CENTRED cutoff-mean row
`(1/2) |<∫M₁ - Y₁, Y₂> + <Y₁, ∫M₂ - Y₂>|`. -/
theorem abs_integral_sub_half_vecDot_le_centred {d : ℕ} {α : Type*} [MeasurableSpace α]
    (P : Measure α) [IsProbabilityMeasure P] (Y1 Y2 : Vec d)
    (A E : α → ℝ) (M1 M2 : α → Vec d) (J : α → ℝ)
    (hJ : Integrable J P) (hA : Integrable A P)
    (hW : Integrable (fun a => E a - J a) P)
    (hM1 : ∀ i, Integrable (fun a => M1 a i) P)
    (hM2 : ∀ i, Integrable (fun a => M2 a i) P)
    (hid : ∀ a, A a = E a - (1 / 2 : ℝ) * vecDot (M1 a) Y2
        - (1 / 2 : ℝ) * vecDot Y1 (M2 a) + (1 / 2 : ℝ) * vecDot Y1 Y2) :
    |(∫ a, J a ∂P) - (1 / 2 : ℝ) * vecDot Y1 Y2|
      ≤ |∫ a, A a ∂P| + |∫ a, (E a - J a) ∂P|
        + (1 / 2 : ℝ) * |vecDot ((fun i => ∫ a, M1 a i ∂P) - Y1) Y2
            + vecDot Y1 ((fun i => ∫ a, M2 a i ∂P) - Y2)| := by
  classical
  have _ := hA
  have hE : Integrable E P := by
    refine (hW.add hJ).congr ?_
    filter_upwards with a
    simp only [Pi.add_apply]
    ring
  have hIntM1 : Integrable (fun a => vecDot (M1 a) Y2) P := by
    simp only [vecDot]
    exact integrable_finsetSum Finset.univ (fun i _ => (hM1 i).mul_const (Y2 i))
  have hIntM2 : Integrable (fun a => vecDot Y1 (M2 a)) P := by
    simp only [vecDot]
    exact integrable_finsetSum Finset.univ (fun i _ => (hM2 i).const_mul (Y1 i))
  have hT1 : Integrable (fun a => (1 / 2 : ℝ) * vecDot (M1 a) Y2) P :=
    hIntM1.const_mul _
  have hT2 : Integrable (fun a => (1 / 2 : ℝ) * vecDot Y1 (M2 a)) P :=
    hIntM2.const_mul _
  have hCint : Integrable (fun _ : α => (1 / 2 : ℝ) * vecDot Y1 Y2) P :=
    integrable_const _
  have hAint : (∫ a, A a ∂P)
      = (∫ a, E a ∂P)
        - (1 / 2 : ℝ) * vecDot (fun i => ∫ a, M1 a i ∂P) Y2
        - (1 / 2 : ℝ) * vecDot Y1 (fun i => ∫ a, M2 a i ∂P)
        + (1 / 2 : ℝ) * vecDot Y1 Y2 := by
    have h1 : (∫ a, A a ∂P)
        = ∫ a, (E a - (1 / 2 : ℝ) * vecDot (M1 a) Y2
            - (1 / 2 : ℝ) * vecDot Y1 (M2 a)
            + (1 / 2 : ℝ) * vecDot Y1 Y2) ∂P := by
      refine integral_congr_ae ?_
      filter_upwards with a
      exact hid a
    rw [h1]
    have h2 : (∫ a, (E a - (1 / 2 : ℝ) * vecDot (M1 a) Y2
          - (1 / 2 : ℝ) * vecDot Y1 (M2 a)
          + (1 / 2 : ℝ) * vecDot Y1 Y2) ∂P)
        = (∫ a, (E a - (1 / 2 : ℝ) * vecDot (M1 a) Y2
              - (1 / 2 : ℝ) * vecDot Y1 (M2 a)) ∂P)
          + (∫ a, (1 / 2 : ℝ) * vecDot Y1 Y2 ∂P) :=
      integral_add ((hE.sub hT1).sub hT2) hCint
    rw [h2]
    have h3 : (∫ a, (E a - (1 / 2 : ℝ) * vecDot (M1 a) Y2
          - (1 / 2 : ℝ) * vecDot Y1 (M2 a)) ∂P)
        = (∫ a, (E a - (1 / 2 : ℝ) * vecDot (M1 a) Y2) ∂P)
          - (∫ a, (1 / 2 : ℝ) * vecDot Y1 (M2 a) ∂P) :=
      integral_sub (hE.sub hT1) hT2
    rw [h3]
    have h4 : (∫ a, (E a - (1 / 2 : ℝ) * vecDot (M1 a) Y2) ∂P)
        = (∫ a, E a ∂P) - (∫ a, (1 / 2 : ℝ) * vecDot (M1 a) Y2 ∂P) :=
      integral_sub hE hT1
    rw [h4]
    have h5 : (∫ a, (1 / 2 : ℝ) * vecDot (M1 a) Y2 ∂P)
        = (1 / 2 : ℝ) * vecDot (fun i => ∫ a, M1 a i ∂P) Y2 := by
      rw [integral_const_mul, integral_vecDot_coord P M1 Y2 hM1]
    have h6 : (∫ a, (1 / 2 : ℝ) * vecDot Y1 (M2 a) ∂P)
        = (1 / 2 : ℝ) * vecDot Y1 (fun i => ∫ a, M2 a i ∂P) := by
      rw [integral_const_mul]
      congr 1
      simp only [vecDot]
      rw [integral_finsetSum Finset.univ (fun i _ => (hM2 i).const_mul (Y1 i))]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [integral_const_mul]
    have h7 : (∫ a, (1 / 2 : ℝ) * vecDot Y1 Y2 ∂P) = (1 / 2 : ℝ) * vecDot Y1 Y2 := by
      rw [integral_const]
      simp only [probReal_univ, smul_eq_mul, one_mul]
    rw [h5, h6, h7]
  have hWint : (∫ a, (E a - J a) ∂P) = (∫ a, E a ∂P) - (∫ a, J a ∂P) :=
    integral_sub hE hJ
  have hsub_left : ∀ x y z : Vec d, vecDot (x - y) z = vecDot x z - vecDot y z := by
    intro x y z
    rw [sub_eq_add_neg, vecDot_add_left, vecDot_neg_left, sub_eq_add_neg]
  have hsub_right : ∀ x y z : Vec d, vecDot x (y - z) = vecDot x y - vecDot x z := by
    intro x y z
    rw [sub_eq_add_neg, vecDot_add_right, vecDot_neg_right, sub_eq_add_neg]
  have hId : (∫ a, J a ∂P) - (1 / 2 : ℝ) * vecDot Y1 Y2
      = (∫ a, A a ∂P) - (∫ a, (E a - J a) ∂P)
        + (1 / 2 : ℝ) * (vecDot ((fun i => ∫ a, M1 a i ∂P) - Y1) Y2
            + vecDot Y1 ((fun i => ∫ a, M2 a i ∂P) - Y2)) := by
    rw [hAint, hWint, hsub_left, hsub_right]
    ring
  have hXZ : |(1 / 2 : ℝ) * (vecDot ((fun i => ∫ a, M1 a i ∂P) - Y1) Y2
        + vecDot Y1 ((fun i => ∫ a, M2 a i ∂P) - Y2))|
      = (1 / 2 : ℝ) * |vecDot ((fun i => ∫ a, M1 a i ∂P) - Y1) Y2
          + vecDot Y1 ((fun i => ∫ a, M2 a i ∂P) - Y2)| := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (1 / 2))]
  calc
    |(∫ a, J a ∂P) - (1 / 2 : ℝ) * vecDot Y1 Y2|
        = |(∫ a, A a ∂P) - (∫ a, (E a - J a) ∂P)
            + (1 / 2 : ℝ) * (vecDot ((fun i => ∫ a, M1 a i ∂P) - Y1) Y2
                + vecDot Y1 ((fun i => ∫ a, M2 a i ∂P) - Y2))| := by rw [hId]
    _ ≤ |(∫ a, A a ∂P) - (∫ a, (E a - J a) ∂P)|
          + |(1 / 2 : ℝ) * (vecDot ((fun i => ∫ a, M1 a i ∂P) - Y1) Y2
                + vecDot Y1 ((fun i => ∫ a, M2 a i ∂P) - Y2))| :=
        abs_add_le _ _
    _ ≤ (|∫ a, A a ∂P| + |∫ a, (E a - J a) ∂P|)
          + |(1 / 2 : ℝ) * (vecDot ((fun i => ∫ a, M1 a i ∂P) - Y1) Y2
                + vecDot Y1 ((fun i => ∫ a, M2 a i ∂P) - Y2))| := by
        refine add_le_add ?_ (le_refl _)
        simpa only [sub_eq_add_neg, abs_neg] using
          abs_add_le (∫ a, A a ∂P) (-(∫ a, (E a - J a) ∂P))
    _ = |∫ a, A a ∂P| + |∫ a, (E a - J a) ∂P|
          + (1 / 2 : ℝ) * |vecDot ((fun i => ∫ a, M1 a i ∂P) - Y1) Y2
              + vecDot Y1 ((fun i => ∫ a, M2 a i ∂P) - Y2)| := by
        rw [hXZ]

end

end Homogenization.HighContrast.Multiscale
