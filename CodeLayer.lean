module

public import CodeLayer.AdditiveComplexity
public import CodeLayer.AxiomAudit
public import CodeLayer.BinaryConstant
public import CodeLayer.BinaryKraft
public import CodeLayer.BitStringPrimrec
public import CodeLayer.Code.BitGates
public import CodeLayer.Code.EvalLaws
public import CodeLayer.Code.SizeArith
public import CodeLayer.PolyTime
public import CodeLayer.PrefixInvariance
public import CodeLayer.PriorNormalization
public import CodeLayer.SerializationParse
public import CodeLayer.TimeCost

/-!
# `CodeLayer`

The code layer: the machinery of programs as Gödel-numbered `Nat.Partrec.Code`.

It holds the additive program-length measure and its serialization, the binary constant and
the binary Kraft inequality, the evaluation laws and bit-gate and size-arithmetic libraries,
the step-counting cost model, and polynomial time over it.

This root module imports every module of the library root, including its axiom audit.
-/
