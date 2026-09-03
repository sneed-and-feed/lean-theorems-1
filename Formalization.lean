import Formalization.GrahamPollak
import Formalization.BollobasTwoFamilies
import Formalization.OreHamiltonian
import Formalization.BondyInducedSubsets
import Formalization.DescartesSigns
import Formalization.DeBruijnErdos
import Formalization.ErdosKoRado
import Formalization.SylvesterGallai
import Formalization.HallMarriage
import Formalization.FriendshipTheorem
import Formalization.RadonHelly
import Formalization.TverbergsTheorem
import Formalization.DilworthTheorem
import Formalization.ErdosSzekeresConvex
import Formalization.TuckersLemma
import Formalization.FriendshipWindmill
import Formalization.FranklWilson
import Formalization.ColorfulHelly
import Formalization.SpernerND
import Formalization.ColorfulCaratheodory
import Formalization.KonigMatching

/-!
# Root Formalization Library: Repo 1
Imports all verified Tier-1 Palomar submission packages and active queue suites.
Retired and superseded theories are decoupled below to ensure minimal compilation overhead,
shield against upstream Mathlib drift, and preserve complete audit integrity.
-/

-- ==============================================================================
-- 🛑 Decoupled Retired & Superseded Theories (Archived in Place for Audit Integrity)
-- ==============================================================================
-- Class A: Substantive Historical & Pedagogical Packages
-- import Formalization.EulerPolyhedron   -- Retired: AP-18, AP-26 (Combinatorial maps, assumed χ = 2)
-- import Formalization.DesarguesVector   -- Retired: Synthetic projective geometry / Wiedijk #53
-- import Formalization.SchursTheorem      -- Retired: Classical sum-free integer coloring & crude bound
-- import Formalization.SpernersLemma     -- Superseded: 1D/2D instances superseded by General n-D Sperner
-- import Formalization.Sperner3D         -- Superseded: 3D instance superseded by General n-D Sperner
-- import Formalization.KneserLovasz      -- Retired: AP-18, AP-26 (Kneser upper bound; Lovász lower unformalized)
-- import Formalization.PicksTheorem      -- Retired: AP-07 (Lattice polygons / Wiedijk #92)

-- Class B: Hollow Anti-Pattern Stubs
-- import Formalization.ArtGalleryTheorem -- Retired: AP-18, AP-26 (Assumes 3-colorability as hypothesis)
-- import Formalization.BecksTheorem      -- Retired: AP-26 (Double counting gives O(1) lines, misses Ω(n²))
-- import Formalization.CauchyArmLemma    -- Retired: AP-10, AP-18 (Explicitly restricted by n ≤ 2)
-- import Formalization.CrossingLemma     -- Retired: AP-02, AP-18 (Proves dummy real scalars via linarith)
-- import Formalization.ElekesSumProduct  -- Retired: AP-02, AP-07 (Dummy struct baking in crossing bounds)
-- import Formalization.ErdosUnitDistances -- Retired: AP-02, AP-07 (Dummy real struct baking in crossing bounds)
-- import Formalization.SzemerediTrotter  -- Retired: AP-07 (Carrier bakes Crossing Lemma directly)
-- import Formalization.TutteOneFactor    -- Retired: AP-01, AP-18 (1-line definitional wrapper over Mathlib)
