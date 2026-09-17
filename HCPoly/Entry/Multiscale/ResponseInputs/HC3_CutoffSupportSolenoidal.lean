import HCPoly.Entry.Multiscale.ResponseInputs.HC1_DomainBridgeAnnealedBlock
import Homogenization.PDE.Harmonic

/-!
# The flux defect of an `A`-harmonic function is solenoidal

For a set `U ⊆ ℝ^d`, a vector field is weakly solenoidal on `U` when its pairing with the
gradient of every compactly supported `H¹₀(U)` test function vanishes
(`Homogenization.IsSolenoidalOn`).  The flux `x ↦ b(x) ∇u(x)` of an `A`-harmonic function is
solenoidal by the definition of `A`-harmonicity, and a constant field is solenoidal against
`H¹₀(U)` tests because the componentwise average of a zero-trace `H¹` gradient vanishes.
Consequently the flux defect obtained by subtracting a constant vector from the flux is again
solenoidal; this is the field that the cutoff pairing of `e.response.cutoff.estimate`
(AK.HC Lemma A.1, (A.4)) pairs against.

The constant-field statement and the defect statement need integrability of the fields being
paired, which in this library is supplied by finiteness of the restricted volume measure (for the
constant) and by an explicit `L²(U)` witness (for the flux); the corresponding hypotheses appear
on the two refined statements below.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- A constant vector field is weakly solenoidal on a finite-measure domain: every zero-trace
`H¹` test gradient has vanishing componentwise integral, so pairing it with a constant vector
gives zero. -/
theorem isSolenoidalOn_const_of_finiteMeasure {d : ℕ} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] (Q : Vec d) :
    IsSolenoidalOn U (fun _ => Q) := by
  intro φ
  exact CorrectionFieldData.integral_vecDot_const_left_eq_zero_of_integral_eq_zero_coords
    (U := U) Q φ.toH1Function.grad_memVectorL2
    (IsPotentialZeroTraceOn.integral_eq_zero φ.isPotentialZeroTraceOn)

/-- On a finite-measure domain, the flux defect `x ↦ b(x) ∇u(x) - Q` is weakly solenoidal
whenever the flux has an `L²(U)` representative: the flux is solenoidal, the constant field is
solenoidal, and both pairings are integrable, so their sum is solenoidal. -/
theorem isSolenoidalOn_fluxDefect_of_finiteMeasure {d : ℕ} {U : Set (Vec d)} {b : CoeffField d}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (u : AHarmonicFunction b U)
    (hflux : MemVectorL2 U (fun x => matVecMul (b x) (u.toH1.grad x))) (Q : Vec d) :
    IsSolenoidalOn U (fun x => matVecMul (b x) (u.toH1.grad x) - Q) := by
  have hconst : MemVectorL2 U (fun _ : Vec d => Q) :=
    MeasureTheory.memLp_const (μ := volumeMeasureOn U) (p := (2 : ENNReal)) (c := Q)
  have hdef : (fun x => matVecMul (b x) (u.toH1.grad x) - Q) =
      (fun x => matVecMul (b x) (u.toH1.grad x)) + (-1 : ℝ) • (fun _ : Vec d => Q) := by
    funext x
    simp [Pi.add_apply, sub_eq_add_neg]
  rw [hdef]
  exact isSolenoidalOn_add_of_memVectorL2 hflux (hconst.const_smul (-1))
    u.isHarmonic.2
    (isSolenoidalOn_smul (isSolenoidalOn_const_of_finiteMeasure (U := U) Q) (-1))

end

end Homogenization.HighContrast.Multiscale
