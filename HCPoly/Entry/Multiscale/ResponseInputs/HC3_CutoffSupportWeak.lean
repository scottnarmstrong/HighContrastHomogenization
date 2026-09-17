import HCPoly.Entry.Multiscale.ResponseInputs.HC1_DomainBridgeAnnealedBlock

/-!
# Elementary facts about the weak response energy

The weak response energy `respWeakEnergy` is the supremum, over all families of cell
maximizers of the response functional, of the weak energies
`3^{-t} ∫ [M_0^{1/2}(X_t - Y)]^2 dP`.  This file records the two facts used whenever it is
consumed as an upper bound: the supremum is nonnegative, and any single admissible family of
maximizers realizes a member of the defining set, so its weak energy lies below the supremum
once that set is bounded above.  These are the elementary parts of the weak estimate
`e.response.weak.estimate`.
-/

open Homogenization.HighContrast (CoeffSpace)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The weak response energy `W` is nonnegative.  It is the supremum of a set of values
`3^{-t} ∫ [M_0^{1/2}(X_t - Y)]^2 dP`, each of which is nonnegative because the exponential
factor is positive and the integral of a square is nonnegative; the real supremum evaluates
to `0` on the empty set and on a set that is not bounded above. -/
theorem respWeakEnergy_nonneg {d : ℕ} (P : Measure (CoeffSpace d)) (qq : Mat d) (t : ℤ)
    (M0 : BlockMat d) (p q' : Vec d) (b : CoeffSpace d → CoeffField d) (Y : BlockVec d) :
    0 ≤ respWeakEnergy P qq t M0 p q' b Y := by
  rw [respWeakEnergy_eq_sSup_respWeakEnergySet]
  rcases Set.eq_empty_or_nonempty (respWeakEnergySet P qq t M0 p q' b Y) with he | hne
  · rw [he, Real.sSup_empty]
  · by_cases hbdd : BddAbove (respWeakEnergySet P qq t M0 p q' b Y)
    · obtain ⟨c, u, hu, rfl⟩ := hne
      have h3 : (0 : ℝ) < (3 : ℝ) ^ (-(t : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
      have hint : 0 ≤ ∫ a, besovSeminorm t (fun n z =>
          blockMatVecMul (blockSqrt M0)
            (cellAverage (adaptedCellAtCenter qq (t - (n : ℤ)) z)
              (optimizerField (b a) (u a)) - Y)) ^ 2 ∂P :=
        integral_nonneg fun a => sq_nonneg _
      exact le_trans (mul_nonneg h3.le hint) (le_csSup hbdd ⟨u, hu, rfl⟩)
    · rw [Real.sSup_of_not_bddAbove hbdd]

/-- Every admissible family of cell maximizers realizes a member of the defining set of the
weak response energy `W`; consequently its weak energy is at most `W` whenever that set is
bounded above.  This is the direction in which `W` is consumed as an upper bound. -/
theorem le_respWeakEnergy {d : ℕ} (P : Measure (CoeffSpace d)) (qq : Mat d) (t : ℤ)
    (M0 : BlockMat d) (p q' : Vec d) (b : CoeffSpace d → CoeffField d) (Y : BlockVec d)
    (hbdd : BddAbove (respWeakEnergySet P qq t M0 p q' b Y))
    (u : (a : CoeffSpace d) → AHarmonicFunction (b a) (HighContrast.adaptedCell qq t))
    (hu : ∀ a, IsResponseMaximizer (HighContrast.adaptedCell qq t) p q' (b a) (u a)) :
    (3 : ℝ) ^ (-(t : ℝ)) * ∫ a, besovSeminorm t (fun n z =>
        blockMatVecMul (blockSqrt M0)
          (cellAverage (adaptedCellAtCenter qq (t - (n : ℤ)) z)
            (optimizerField (b a) (u a)) - Y)) ^ 2 ∂P
      ≤ respWeakEnergy P qq t M0 p q' b Y := by
  rw [respWeakEnergy_eq_sSup_respWeakEnergySet]
  exact le_csSup hbdd ⟨u, hu, rfl⟩

end

end Homogenization.HighContrast.Multiscale

