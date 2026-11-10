import TensorFixedQuantumClosure
import FixedQuantumClosure
import TensorFixedQuantumStrong
import IidErasureTheorem
import ResourceAccounting
import LatentResourceAccounting
import LatentMonotoneTheorem
import TensorGeneralCircuit
import UncorrectableMachine
import UncorrectableMachineSized
import ProductCode
import DistanceDetermination
import PaddingInvariance
import UncorrectableProbability
import PointHardness
import DistanceWeight
import DistanceExtraction
import SatCosetWeight
import SatToDistance
import SatLogicalQubit
import SatHardness
import HybridEstimator
import HybridSymmetry
import UnionEstimator
import CompletenessFormula
import CompletenessConverse
import ListCertificate
import ExactTable
import EnumeratorExample
import PaperExamples
import SamplingBounds
import RankSampling
import EnumeratorFormula
import UncorrectableFormula
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let selected : Array Name := #[`TensorFixedQuantumClosure, `FixedQuantumClosure, `TensorFixedQuantumStrong, `IidErasureTheorem, `ResourceAccounting, `LatentResourceAccounting, `LatentMonotoneTheorem, `TensorGeneralCircuit, `UncorrectableMachine, `UncorrectableMachineSized, `ProductCode, `DistanceDetermination, `PaddingInvariance, `UncorrectableProbability, `PointHardness, `DistanceWeight, `DistanceExtraction, `SatCosetWeight, `SatToDistance, `SatLogicalQubit, `SatHardness, `HybridEstimator, `HybridSymmetry, `UnionEstimator, `CompletenessFormula, `CompletenessConverse, `ListCertificate, `ExactTable, `EnumeratorExample, `PaperExamples, `SamplingBounds, `RankSampling, `EnumeratorFormula, `UncorrectableFormula]
  let header := env.header
  let mut count : Nat := 0
  let mut modules : Nat := 0
  for idx in [:header.moduleNames.size] do
    if selected.contains header.moduleNames[idx]! then
      modules := modules + 1
      for name in header.moduleData[idx]!.constNames do
        let axs ← collectAxioms name
        for ax in axs do
          unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
            throwError "Unexpected axiom {ax} in {name}"
        count := count + 1
  unless modules == selected.size do throwError "Missing audited module"
  if count == 0 then throwError "No declarations audited"
  logInfo m!"AUDIT_MODULES {modules}"
  logInfo m!"AUDIT_COUNT {count}"
