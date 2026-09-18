/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Analytic.EuclideanAmbient
import HCPoly.Analytic.ConvexDomains
import HCPoly.Analytic.NormComparison
import HCPoly.Analytic.SingularKernel
import HCPoly.Analytic.TestNorms
import HCPoly.Analytic.EllipsoidGeometry
import HCPoly.Analytic.AntiVacuityInstances
import HCPoly.Analytic.DualNormJunk
import HCPoly.Analytic.CenteringInvariance
import HCPoly.Analytic.WeakPairing
import HCPoly.Analytic.WeightedEnergy
import HCPoly.Analytic.ClassHonesty
import HCPoly.Analytic.ClassCounterexample
import HCPoly.Analytic.ClassPairing
import HCPoly.Analytic.LocalIntegrability
import HCPoly.Analytic.WeakGradientClosure
import HCPoly.Analytic.ClosureH1a
import HCPoly.Analytic.DirichletDomain
import HCPoly.Analytic.NormEquivalence
import HCPoly.Analytic.ScaledCoeff

/-!
# The analytic provider layer for the homogenization theorem

The proofs standing behind the conclusion of
`t.random.homogenization`: the fail-closed behaviour of the
normalized dual norms, the convex domains and the shape datum carried by the
Dirichlet estimate, the weighted Sobolev classes and the absolute convergence of
their pairings, and the membership classes they are read on.

These modules sit below the frozen statement and are imported by no frozen file,
so they may be extended without moving any frozen declaration's pin.
-/
