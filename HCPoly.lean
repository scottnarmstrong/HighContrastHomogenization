/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
-- Project aggregator: the frozen exports (each pulls in exactly its provider
-- chain) and the paper's necessity/sharpness layer, which no export imports.
import HCPoly.Frozen.QuenchedConvergence
import HCPoly.Frozen.RandomSourceWindow
import HCPoly.Frozen.FixedGridRecurrence
import HCPoly.Frozen.PortableHistory
import HCPoly.Frozen.RandomSourceControl
import HCPoly.Frozen.RandomSourceAdaptedInitialization
import HCPoly.Frozen.PolynomialEntry
import HCPoly.Frozen.Stationarity
import HCPoly.Frozen.UnitRange
import HCPoly.Frozen.CoarseEllipticityDagger
import HCPoly.Frozen.PolynomialHomogenization
import HCPoly.Frozen.RandomAdaptedResponse
import HCPoly.Frozen.RandomPersistenceTransfer
import HCPoly.Frozen.RandomSourceBridgeShortHop
import HCPoly.Frozen.RandomSourceBridgeTwoGridShiftedDrift
import HCPoly.Frozen.RandomSourceGlobalSelection
import HCPoly.Frozen.RandomSourceGridTransport
import HCPoly.Setup.QualitativeClass
import HCPoly.Setup.Dissolution
import HCPoly.Analytic
import HCPoly.Annealed.Witness
import HCPoly.Annealed.WitnessSigmaField
import HCPoly.Basic
import HCPoly.MainResults
