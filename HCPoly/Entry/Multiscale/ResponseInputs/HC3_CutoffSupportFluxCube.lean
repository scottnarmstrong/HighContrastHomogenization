import HCPoly.Entry.Multiscale.ResponseInputs.H8bEllipticInput

/-!
# The pulled-back flux on the reference cube, with the elliptic datum packaged existentially

The two inputs below restate the square-integrability of the optimizer flux and of its pullback to
the reference cube in the form in which the cutoff argument consumes them: the coefficient is only
assumed to agree almost everywhere on the adapted cell with a field uniformly elliptic there, and
the elliptic constants and representative are introduced by an existential rather than carried as
separate hypotheses.  The a.e.-representative shape is forced by the coefficient carrier, whose
points are a.e. classes, and is enough for every `MemLp` consumer, all of which are a.e. invariant.

Paper: the cutoff estimate `e.response.cutoff.estimate` and its negative-Besov duality bound
(`AK.HC` Lemma A.1, (A.4)), whose flux slot is supplied here.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **The pulled-back flux is `L²` on the reference cube, elliptic datum existentially
quantified.**  If the coefficient `b` agrees almost everywhere on the adapted cell
`HighContrast.adaptedCell q t` with a field `f` uniformly elliptic there, then the pulled-back centred
flux defect `y ↦ q⁻¹ ((optimizerField b u (q y) − Y).2)` of an `b`-harmonic optimizer `u` is square
integrable for the normalized measure of the reference cube.  This is the `hflux` slot of the
generic CG product bridge `abs_cubeAverage_vecDot_centered_scalar_cutoff_le_scaledWeakNormProduct`
used in the cutoff estimate `e.response.cutoff.estimate`. -/
theorem memLp_two_pullback_flux_of_exists {d : ℕ} [NeZero d] {q : Mat d} (hq : IsUnit q) (t : ℤ)
    {b : CoeffField d}
    (hb : ∃ (lam Lam : ℝ) (f : CoeffField d), 0 < lam ∧ lam ≤ Lam ∧
      IsEllipticFieldOn lam Lam (HighContrast.adaptedCell q t) f ∧
        b =ᵐ[volumeMeasureOn (HighContrast.adaptedCell q t)] f)
    (u : AHarmonicFunction b (HighContrast.adaptedCell q t)) (Y : BlockVec d) :
    MemLp (fun y => matVecMul q⁻¹ ((optimizerField b u (matVecMul q y) - Y).2)) 2
      (normalizedCubeMeasure (originCube d t)) := by
  obtain ⟨lam, Lam, f, _, _, hEll, hbf⟩ := hb
  exact memLp_two_normalizedCubeMeasure_pullback_flux hq t hEll hbf u Y

/-- **The flux of an optimizer is `L²` on the cell, elliptic datum existentially quantified.**
If the coefficient `b` agrees almost everywhere on the adapted cell `HighContrast.adaptedCell q t` with
a field `f` uniformly elliptic there, then the flux `x ↦ b x · u.toH1.grad x` of a `b`-harmonic
optimizer `u` is square integrable on the cell.  This is the `hflux` hypothesis of the
integration-by-parts step in the negative-Besov duality bound (`AK.HC` Lemma A.1, (A.4)) behind
the cutoff estimate `e.response.cutoff.estimate`. -/
theorem memVectorL2_flux_of_exists {d : ℕ} [NeZero d] {q : Mat d} (hq : IsUnit q) (t : ℤ)
    {b : CoeffField d}
    (hb : ∃ (lam Lam : ℝ) (f : CoeffField d), 0 < lam ∧ lam ≤ Lam ∧
      IsEllipticFieldOn lam Lam (HighContrast.adaptedCell q t) f ∧
        b =ᵐ[volumeMeasureOn (HighContrast.adaptedCell q t)] f)
    (u : AHarmonicFunction b (HighContrast.adaptedCell q t)) :
    MemVectorL2 (HighContrast.adaptedCell q t) (fun x => matVecMul (b x) (u.toH1.grad x)) := by
  obtain ⟨lam, Lam, f, _, _, hEll, hbf⟩ := hb
  have _ := hq
  have hfluxf : MemVectorL2 (HighContrast.adaptedCell q t)
      (fun x => matVecMul (f x) (u.toH1.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll u.toH1.grad_memVectorL2
  have hae : (fun x => matVecMul (f x) (u.toH1.grad x))
      =ᵐ[volumeMeasureOn (HighContrast.adaptedCell q t)]
        fun x => matVecMul (b x) (u.toH1.grad x) := by
    filter_upwards [hbf] with x hx
    rw [hx]
  exact (memLp_congr_ae hae).mp hfluxf

end

end Homogenization.HighContrast.Multiscale
