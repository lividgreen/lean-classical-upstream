module

public import ShannonInfo.AxiomAudit
public import ShannonInfo.BitGuessing
public import ShannonInfo.ChengCCC
public import ShannonInfo.CslibFrontier.Probability.Conditioning
public import ShannonInfo.CslibFrontier.Probability.Divergence
public import ShannonInfo.CslibFrontier.Probability.Entropy
public import ShannonInfo.CslibFrontier.Probability.PMF.Bind
public import ShannonInfo.CslibFrontier.Probability.PMF.Event
public import ShannonInfo.CslibFrontier.Probability.PMF.Expect
public import ShannonInfo.CslibFrontier.Probability.PMF.Filter
public import ShannonInfo.CslibFrontier.Probability.PMF.Map
public import ShannonInfo.CslibFrontier.Probability.Product
public import ShannonInfo.CslibFrontier.Probability.ProductConditioning
public import ShannonInfo.CslibFrontier.Probability.ProductConditioning.SideInformation
public import ShannonInfo.CslibFrontier.Probability.StatisticalDistance
public import ShannonInfo.CslibFrontier.Probability.StatisticalDistance.CloseTo
public import ShannonInfo.CslibFrontier.Probability.StatisticalDistance.TotalVariation
public import ShannonInfo.FiniteInfoTheory

/-!
# `ShannonInfo`

Finite-discrete Shannon information theory.

Entropy, mutual information, the data-processing and Fano inequalities, and the lower bound on
forgetting of Cheng's Theorem 4 derived from them, and the bound on the bits of a uniform string
that a guesser reading a short message and the earlier bits gets right.

This root module imports every module of the library root, including its axiom audit.
-/
