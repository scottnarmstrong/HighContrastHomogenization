import HCPoly.Entry.Setup.LogDetLoss
import HCPoly.Entry.Setup.MeanPenalty
import HCPoly.Entry.Setup.SchattenNorm
import HCPoly.Entry.Setup.SelectionExponents
import HCPoly.Setup.CoefficientSpace

/-!
# The fluctuation history, the mean history and the history

Near `e.scale.selection.mean.history`
(`e.scale.selection.fluctuation.history`, `e.scale.selection.mean.history`):

> For `m ≥ j_*`, define the fluctuation history by
> `ℋ^fluc_q(m) := E[ sup_{j_* ≤ j ≤ m} 3^{−Qρ_max(m−j)} max_{z ∈ 3^j q ℤ^d ∩ ⋄_m^q}
> |V^q_{j,m}(z)|^Q ]`.
> For `j_* ≤ n ≤ m`, define the mean history by
> `ℋ^mean_q(m;n) := ∑_{j=n}^{m−1} 3^{−¼(1−γ)(m−1−j)} Ψ_Q(P^q_{j,m})`.
> Set `ℋ^mean_q(m) := ℋ^mean_q(m;j_*)` and `ℋ_q(m) := ℋ^fluc_q(m) + ℋ^mean_q(m)`.

`Q` and `ρ_max` are the fixed values of `e.scale.selection.Q.choice`, so `bigQ d γ` and
`rhoMax d γ`; `|·|` is the operator norm `blockOpNorm`; `3^j q ℤ^d` is `adaptedLatticeAtScale q j`
and `⋄_m^q` is `adaptedCell q m`.  The print's `ℋ^mean_q(m)` is the two-argument
`meanHistory P γ q jStar m` and gets no separate name here.

**The three quantities are real-valued**: the expectation is the Bochner
integral, the printed `sup` and `max` are `⨆` in `ℝ`, and `Ψ_Q` is summed as it stands.
What that costs, recorded rather than left to be discovered:

* These are total real formulas. Before using a history or profile as the printed expectation,
  prove the integrability of every needed random integrand and of the entries defining the
  annealed blocks. For the real suprema, also prove the relevant finite/nonempty index-set and
  boundedness facts. `MemLqSchatten P N H` supplies the moment condition only for its specified
  `H`. Where the paper states membership it may be carried as that printed premise; elsewhere
  these properties must be derived from the standing source hypotheses. An estimate of the
  totalized real value does not itself establish integrability. No unprinted premise is added
  to a theorem.
* Nothing is truncated: `Ψ_Q(P^q_{j,m})` enters with whatever sign the formula gives
  (`HCPoly/Entry/Setup/MeanPenalty.lean`), and the printed sums `𝒫 + D` of `HCPoly/Entry/Setup/Profile.lean`
  are a sum of two reals, written literally as the print writes them.

`j_*` is a natural number (near `e.rounded.grid.bounds`), coerced to `ℤ` where it is
compared with the generations `j`, `m`, which range over `ℤ`; the declaration
`explicitRoundedGrid (jStar : ℕ)` stands.  The second argument `n` of `ℋ^mean_q(m;n)` stays an
integer: the print instantiates it both at `j_*` and at a general generation `n ≥ j_*`.

The mean history is summed over the `Finset.Ico n m` range, and the supremum and the
maximum are `⨆`.  The expectation takes real values as the Bochner integral, rather than
values in `ℝ≥0∞` with `∫⁻`.  The three exponents `Q`, `ρ_max` and `a` are not free real
parameters: `Q` and `ρ_max` are fixed by `e.scale.selection.Q.choice` and `¼(1−γ)` is
written out.  The operator norm is `blockOpNorm` itself, not a Loewner encoding, and `|·|`
means that operator norm.  The inner maximum is indexed by the printed index set
`3^j q ℤ^d ∩ ⋄_m^q`.
-/

open Homogenization.HighContrast (CoeffSpace)
namespace Homogenization.HighContrast

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The fluctuation history
`ℋ^fluc_q(m) = E[sup_{j_* ≤ j ≤ m} 3^{−Qρ_max(m−j)} max_{z ∈ 3^j q ℤ^d ∩ ⋄_m^q}
|V^q_{j,m}(z)|^Q]` (`e.scale.selection.fluctuation.history`). -/
def fluctuationHistory (P : Measure (CoeffSpace d)) (γ : ℝ) (q : Mat d) (jStar : ℕ)
    (m : ℤ) : ℝ :=
  ∫ a, ⨆ j ∈ Set.Icc (jStar : ℤ) m,
    (3 : ℝ) ^ (-(bigQ d γ : ℝ) * rhoMax d γ * ((m : ℝ) - (j : ℝ))) *
      ⨆ z ∈ adaptedLatticeAtScale q j ∩ HighContrast.adaptedCell q m,
        blockOpNorm (normalizedFluctuation P q j m z a) ^ bigQ d γ ∂P

/-- The mean history `ℋ^mean_q(m;n) = ∑_{j=n}^{m−1} 3^{−¼(1−γ)(m−1−j)} Ψ_Q(P^q_{j,m})`
(`e.scale.selection.mean.history`).  The print's one-argument `ℋ^mean_q(m)` is this at
`n = j_*`. -/
def meanHistory (P : Measure (CoeffSpace d)) (γ : ℝ) (q : Mat d) (n m : ℤ) : ℝ :=
  ∑ j ∈ Finset.Ico n m,
    (3 : ℝ) ^ (-((1 - γ) / 4) * ((m : ℝ) - 1 - (j : ℝ))) *
      meanPenalty (bigQ d γ) (normalizedMean P q j m)

/-- The history `ℋ_q(m) = ℋ^fluc_q(m) + ℋ^mean_q(m;j_*)` (near `e.scale.selection.mean.history`). -/
def history (P : Measure (CoeffSpace d)) (γ : ℝ) (q : Mat d) (jStar : ℕ) (m : ℤ) : ℝ :=
  fluctuationHistory P γ q jStar m + meanHistory P γ q (jStar : ℤ) m

end

end Homogenization.HighContrast
