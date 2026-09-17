import HCPoly.Entry.Setup.Histories

/-!
# The determinant drift `D_{q,j_*}(m)` and the complete profile `𝒫_q(m;n)`

Near `e.scale.selection.determinant.drift`
(`e.scale.selection.determinant.drift`, `e.scale.selection.complete.profile`):

> Set `D_{q,j_*}(m) := ∑_{j=j_*+1}^{m} 3^{−⅛(1−γ)(m−j)} tr(P^q_{j−1,m} − P^q_{j,m})`.
> For `j_* ≤ n ≤ m`, set
> `𝒫_q(m;n) := 3^{−¼(1−γ)(m−n)}(1 + Ψ_Q(P^q_{n,m})) ℋ_q(n) + ℋ^mean_q(m;n)
> + ∑_{j=n+1}^{m} 3^{−¼(1−γ)(m−j)} e^{QΔ^q_{j,m}} E[|V^q_j|_{S_Q}^Q]`.
> In particular, `𝒫_q(n;n) = ℋ_q(n)`.

Both are transcribed literally.  The identity `𝒫_q(n;n) = ℋ_q(n)` is a statement about the
values, not part of the definition, and is not asserted here.

**Both are real-valued**.  The drift always was: its summand is a trace of a
difference of two normalized means, which the manuscript does not assert to be nonnegative
where it defines the drift.  The profile is real, so the printed sums
`𝒫_q(m;n) + D_{q,j_*}(m)` — which occur in many of the printed statements — are a sum
of two reals and stay literal: no `ENNReal.ofReal` around `D`, and no truncation of a
negative `Ψ_Q` or a negative drift.  What the real reading costs is recorded in
`HCPoly/Entry/Setup/Histories.lean`: these are total real formulas. Before using a history or profile
as the printed expectation, prove the integrability of every needed random integrand and of
the entries defining the annealed blocks. For the real suprema, also prove the relevant
finite/nonempty index-set and boundedness facts. `MemLqSchatten P N H` supplies the moment
condition only for its specified `H`. Where the paper states membership it may be carried as
that printed premise; elsewhere these properties must be derived from the standing source
hypotheses. An estimate of the totalized real value does not itself establish integrability.
No unprinted premise is added to a theorem.

`E[|V^q_j|_{S_Q}^Q]` is the **Bochner** integral of the real function
`a ↦ |V^q_j(a)|_{S_Q}^Q`, not the lower integral of its `ENNReal.ofReal`.  Two reasons:
the value is real, and `lqSchattenNorm` of `HCPoly/Entry/Setup/SchattenNorm.lean` is the same
expectation under its own `1/Q`-th power, so writing this one differently would make
`E[|V^q_j|_{S_Q}^Q]` and `‖V^q_j‖_{L^Q(S_Q)}^Q` two different numbers on a non-integrable
moment.  The integrability premise is `MemLqSchatten P (Q : ℝ) (V^q_j)`, which is the
printed "in `L^Q(S_Q)`" and belongs to the statements, not here.  The Schatten index is the
real `Q` that `absSchattenNorm` takes and the outer power is the natural number `Q`, exactly as
printed.

`j_*` is a natural number, coerced to `ℤ` in the drift's summation range,
where it is compared with the generations; `n` and `m` are integers.

This definition takes the real value of the drift and the `Finset.Icc` ranges.  An
`ℝ≥0∞`-valued formulation of the profile would instead use free exponents (`a`, `ρ_dr`) in
place of the printed `¼(1−γ)` and `⅛(1−γ)`, expand the profile's second term into the mean
history's defining sum, where the print writes `ℋ^mean_q(m;n)`, and use, for its third term,
the mixed norm raised to the power `Q` rather than the printed moment `E[|V^q_j|_{S_Q}^Q]`.
Its drift summand `tr((𝐀hom_{T,q})^{-1}(𝐀hom_{r−1,q} − 𝐀hom_{r,q}))` is the printed
`tr(P^q_{j−1,m} − P^q_{j,m})` only after a cyclicity argument.
-/

open Homogenization.HighContrast (CoeffSpace blockSub blockTrace)
namespace Homogenization.HighContrast

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The determinant drift
`D_{q,j_*}(m) = ∑_{j=j_*+1}^{m} 3^{−⅛(1−γ)(m−j)} tr(P^q_{j−1,m} − P^q_{j,m})`
(`e.scale.selection.determinant.drift`). -/
def determinantDrift (P : Measure (CoeffSpace d)) (γ : ℝ) (q : Mat d) (jStar : ℕ) (m : ℤ) :
    ℝ :=
  ∑ j ∈ Finset.Icc ((jStar : ℤ) + 1) m,
    (3 : ℝ) ^ (-((1 - γ) / 8) * ((m : ℝ) - (j : ℝ))) *
      blockTrace (blockSub (normalizedMean P q (j - 1) m) (normalizedMean P q j m))

/-- The complete profile `𝒫_q(m;n)` of `e.scale.selection.complete.profile`. -/
def profile (P : Measure (CoeffSpace d)) (γ : ℝ) (q : Mat d) (jStar : ℕ) (n m : ℤ) : ℝ :=
  (3 : ℝ) ^ (-((1 - γ) / 4) * ((m : ℝ) - (n : ℝ))) *
        (1 + meanPenalty (bigQ d γ) (normalizedMean P q n m)) *
      history P γ q jStar n +
    meanHistory P γ q n m +
    ∑ j ∈ Finset.Icc (n + 1) m,
      (3 : ℝ) ^ (-((1 - γ) / 4) * ((m : ℝ) - (j : ℝ))) *
          Real.exp ((bigQ d γ : ℝ) * logDetLoss P q j m) *
        ∫ a, absSchattenNorm (bigQ d γ : ℝ) (normalizedFluctuationSelf P q j a) ^ bigQ d γ ∂P

end

end Homogenization.HighContrast
