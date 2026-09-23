import RootedKP.ProbeRootCounting
import RootedKP.ActivityBounds
import RootedKP.EndpointCounting
import RootedKP.CollarCells
import RootedKP.HoneycombSymmetry
import RootedKP.LoopTableLink
import RootedKP.KPCompletion
import RootedKP.EndpointConvolution
import RootedKP.PathConfinement
import RootedKP.BoundaryCycle
import RootedKP.BoundaryCountCertificates
import RootedKP.BoundarySideBound
import RootedKP.BoundaryCoordinates
import RootedKP.EndpointGrowth
import RootedKP.BoundaryPrefixBounds
import RootedKP.BoundaryCycleAdjacency
import RootedKP.FinalPrefixKP
import RootedKP.CertifiedKP

/-!
Entry point for the AKLT scalar rooted-KP and root-counting certificate.
`CertifiedKP.lean` assembles the geometric, numerical, arithmetic, and heap
arguments. See SPECIFICATION.md for the precise statement and STATUS.md
for the build and recursive axiom audit status.
-/
