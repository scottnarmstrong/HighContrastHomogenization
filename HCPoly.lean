/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
-- Project aggregator: the frozen exports (each pulls in exactly its provider
-- chain) and the paper's necessity/sharpness layer, which no export imports.
import HCPoly.Frozen.QuenchedConvergence
import HCPoly.Frozen.PolynomialEntry
import HCPoly.Frozen.PolynomialEntryBridge
import HCPoly.Frozen.Stationarity
import HCPoly.Frozen.UnitRange
import HCPoly.Frozen.CoarseEllipticityDagger
import HCPoly.Frozen.PolynomialHomogenization
import HCPoly.Setup.QualitativeClass
import HCPoly.Setup.Dissolution
import HCPoly.Analytic
import HCPoly.Annealed.Witness
import HCPoly.Annealed.WitnessSigmaField
import HCPoly.Basic
import HCPoly.MainResults

-- The polynomial-entry route: the sixteen printed propositions whose statements the
-- entry theorem is assembled from, and the three statements carried in
-- CoarseGraining's own vocabulary.  `HCPoly.Entry.Statements.PolynomialEntry` itself
-- arrives through `HCPoly.Frozen.PolynomialEntryBridge`.
import HCPoly.Entry.Statements.GlobalSelection
import HCPoly.Entry.Statements.InitialFixedGridScale
import HCPoly.Entry.Statements.MatrixAveraging
import HCPoly.Entry.Statements.OneGridPropagation
import HCPoly.Entry.Statements.ParentChildRecurrence
import HCPoly.Entry.Statements.PositiveGap
import HCPoly.Entry.Statements.ProjectiveStep
import HCPoly.Entry.Statements.ResponseTransfer
import HCPoly.Entry.Statements.ScaleSelection
import HCPoly.Entry.Statements.SourceWhitney
import HCPoly.Entry.Statements.SuccessfulShortBridge
import HCPoly.Entry.Statements.TwoGridTransport
import HCPoly.Entry.Statements.TwoGridWhitney
import HCPoly.Entry.CG.Anchors.ResponseFiniteDefect
import HCPoly.Entry.CG.Anchors.ResponseSubadditiveCountable
import HCPoly.Entry.CG.Anchors.ResponseSummable
