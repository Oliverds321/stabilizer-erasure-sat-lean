import FixedQuantumClosure
import TensorFixedQuantumClosure
import TensorFixedQuantumStrong
import IidErasureTheorem
import DistanceDetermination
import PaddingInvariance
import UncorrectableProbability
import PointHardness
import HybridEstimator
import ResourceAccounting
import EnumeratorExample
import HybridSymmetry
import ProductCode
import UncorrectableMachine
import UncorrectableMachineSized
import LatentResourceAccounting
import LatentMonotoneTheorem
import TensorGeneralCircuit
import PaperExamples
import SamplingBounds
import RankSampling
import EnumeratorFormula
import UncorrectableFormula
import DistanceWeight
import CompletenessFormula
import UnionEstimator
import DistanceExtraction
import SatCosetWeight
import SatToDistance
import SatHardness
import SatLogicalQubit
import ExactTable
import CompletenessConverse
import ListCertificate

/-! Axiom audit, by name, of the theorems cited in the manuscript.
Expected for every line: a subset of `propext`, `Classical.choice`,
`Quot.sound`. Compile this file against the compiled modules of the
development.
-/

-- Closed machine theorems (formal-verification section of the manuscript)
#print axioms QecReliability.IidErasure.iid_erasure_machine_guarantee
#print axioms QecReliability.TensorMachine.Runtime.FixedQuantum.isotropic_tensor_machine_guarantee_strong
#print axioms QecReliability.TensorMachine.Runtime.FixedQuantum.isotropic_tensor_machine_guarantee
#print axioms QecReliability.TensorMachine.Runtime.tensor_machine_guarantee
#print axioms QecReliability.LatentMachine.Runtime.FixedQuantum.isotropic_polynomial_endpoint_machine_guarantee

-- Anchored antitone repair (Lemma 11): two-tail form and general interval form
#print axioms QecReliability.PosetShapeRepair.repair_spec
#print axioms QecReliability.PosetShapeRepair.repair_interval
#print axioms QecReliability.PosetShapeRepair.repair_eq_one_iff

-- Distance determination (Proposition 12)
#print axioms QecReliability.DistanceDetermination.zero_prefix_iff
#print axioms QecReliability.DistanceDetermination.first_nonzero_iff
#print axioms QecPhysical.Stabilizer.Lift.distance_determination

-- Padding step of the sparse-hardness corollary
#print axioms QecReliability.Padding.pad_isotropic
#print axioms QecReliability.Padding.erasureScore_pad
#print axioms QecReliability.Padding.isotropicLift_fidelity_pad
#print axioms QecReliability.Padding.rowSpace_padRows
#print axioms QecReliability.Padding.rowIncidences_padRows

-- Uncorrectable-erasure probability: mathematical core of the uncorrectable-probability corollary
#print axioms QecPhysical.Stabilizer.Uncorrectable.uncorrectable_iff_certificate
#print axioms QecPhysical.Stabilizer.Uncorrectable.uncorrectable_mono
#print axioms QecPhysical.Stabilizer.Uncorrectable.channel_infidelity_le_uncorrectableProb
#print axioms QecPhysical.Stabilizer.Uncorrectable.uncorrectableProb_eq_bernstein
#print axioms QecPhysical.Stabilizer.Uncorrectable.layerFraction_monotone
#print axioms QecPhysical.Stabilizer.Uncorrectable.repairedFraction_monotone
#print axioms QecPhysical.Stabilizer.Uncorrectable.repairedFraction_rel
#print axioms QecPhysical.Stabilizer.Uncorrectable.repairedFraction_eq_zero_iff
#print axioms QecPhysical.Stabilizer.Uncorrectable.repairedCurve_rel
#print axioms QecPhysical.Stabilizer.Uncorrectable.repairedCurve_monotoneOn

-- A point estimate determines the distance (tail-sandwich proposition), and the distance certificate
#print axioms QecPhysical.Stabilizer.Uncorrectable.tail_sandwich
#print axioms QecPhysical.Stabilizer.Uncorrectable.infidelity_point_determines_distance
#print axioms QecPhysical.Stabilizer.Uncorrectable.channel_point_determines_distance
#print axioms QecPhysical.Stabilizer.Uncorrectable.uncorrectableProb_point_determines_distance
#print axioms QecPhysical.Stabilizer.Uncorrectable.isDistance_unique
#print axioms QecPhysical.Stabilizer.Uncorrectable.exists_isDistance
#print axioms QecPhysical.Stabilizer.Uncorrectable.distance_le_iff_certificate

-- Identities behind the hybrid estimator of the computed section
#print axioms QecPhysical.Stabilizer.Uncorrectable.finrank_localized_add_finrank
#print axioms QecPhysical.Stabilizer.Uncorrectable.ambiguity_add_ambiguity_compl
#print axioms QecPhysical.Stabilizer.Uncorrectable.erasureScore_eq_dual
#print axioms QecPhysical.Stabilizer.Uncorrectable.layerAverage_erasureScore_dual
#print axioms QecPhysical.Stabilizer.Uncorrectable.exists_minimalUncorrectable_subset
#print axioms QecPhysical.Stabilizer.Uncorrectable.uncorrectable_iff_exists_mins
#print axioms QecPhysical.Stabilizer.Uncorrectable.sum_union_eq_karpLuby
#print axioms QecPhysical.Stabilizer.Uncorrectable.layer_sum_infidelityScore_eq_karpLuby
#print axioms QecPhysical.Stabilizer.Uncorrectable.bernsteinCurve_rel_of_coeff

-- Symmetry reduction of the minimal-set search and the stratified split
#print axioms QecPhysical.Stabilizer.Uncorrectable.symplectic_permute
#print axioms QecPhysical.Stabilizer.Uncorrectable.ambiguity_map_of_preserved
#print axioms QecPhysical.Stabilizer.Uncorrectable.isMinimalUncorrectable_map
#print axioms QecPhysical.Stabilizer.Uncorrectable.minimal_eq_image_through_representative
#print axioms QecPhysical.Stabilizer.Uncorrectable.orbit_isMinimalUncorrectable
#print axioms QecPhysical.Stabilizer.Uncorrectable.sum_eq_karpLuby_add_remainder
#print axioms QecPhysical.Stabilizer.Uncorrectable.remainder_minimal_card
#print axioms QecPhysical.Stabilizer.Uncorrectable.remainder_correctable

-- Resource accounting (Proposition 2) as conjuncts of closed theorems
#print axioms QecReliability.IidErasure.iid_erasure_machine_guarantee_resources
#print axioms QecReliability.TensorMachine.Runtime.FixedQuantum.isotropic_tensor_machine_guarantee_resources

-- Worked examples: enumerators do not determine the curve, and small codes
#print axioms QecPhysical.Stabilizer.EnumeratorExample.layerSum_R
#print axioms QecPhysical.Stabilizer.EnumeratorExample.layerSum_B
#print axioms QecPhysical.Stabilizer.EnumeratorExample.physical_R
#print axioms QecPhysical.Stabilizer.EnumeratorExample.physical_B
#print axioms QecPhysical.Stabilizer.EnumeratorExample.physical_difference
#print axioms QecPhysical.Stabilizer.EnumeratorExample.curves_differ
#print axioms QecPhysical.Stabilizer.EnumeratorExample.stabilizer_enumerators_eq
#print axioms QecPhysical.Stabilizer.EnumeratorExample.normalizer_enumerators_eq
#print axioms QecPhysical.Stabilizer.EnumeratorExample.bare_infidelity
#print axioms QecPhysical.Stabilizer.EnumeratorExample.bare_uncorrectableProb
#print axioms QecPhysical.Stabilizer.EnumeratorExample.four_correctable

-- Multiclass theorem for general circuits; one-class monotone corollary; latent theorem with resources
#print axioms QecReliability.TensorMachineG.Runtime.FixedQuantum.isotropic_tensor_machine_guarantee_general
#print axioms QecReliability.LatentMonotone.latent_monotone_machine_guarantee
#print axioms QecReliability.LatentMonotone.output_prefix
#print axioms QecReliability.LatentMachine.Runtime.FixedQuantum.isotropic_latent_machine_guarantee_resources
#print axioms QecReliability.LatentCoefficients.endpoint_coefficients

-- Uncorrectable-erasure probability at machine level, through the repeated code
#print axioms QecReliability.ProductCode.power_isotropic
#print axioms QecReliability.ProductCode.ambiguity_rep
#print axioms QecReliability.ProductCode.uncorrectableProb_sandwich
#print axioms QecReliability.ProductCode.uncorrectable_relative_of_half
#print axioms QecReliability.ProductCode.rowSpace_rowsPower
#print axioms QecReliability.UncorrectableMachine.fidelity_dup
#print axioms QecReliability.UncorrectableMachine.uncorrectable_machine_guarantee
#print axioms QecReliability.UncorrectableMachine.uncorrectable_machine_guarantee_sized

-- Worked examples of the text and the sampling section
#print axioms QecPhysical.Stabilizer.PaperExamples.tail_bound
#print axioms QecPhysical.Stabilizer.PaperExamples.tail_mass_eq_binomial
#print axioms QecPhysical.Stabilizer.PaperExamples.repetition_single_uncorrectable
#print axioms QecPhysical.Stabilizer.PaperExamples.repetition_single_average_fidelity
#print axioms QecPhysical.Stabilizer.PaperExamples.bell_good_on_normalizer
#print axioms QecPhysical.Stabilizer.PaperExamples.bell_good_counts
#print axioms QecPhysical.Stabilizer.PaperExamples.witness_count
#print axioms QecPhysical.Stabilizer.PaperExamples.bell4_witnesses_E13
#print axioms QecPhysical.Stabilizer.PaperExamples.bell4_witnesses_E34
#print axioms QecPhysical.Stabilizer.PaperExamples.xor_latentCurve
#print axioms QecPhysical.Stabilizer.PaperExamples.xor_physical
#print axioms QecPhysical.Stabilizer.PaperExamples.pad_hess_posDef
#print axioms QecPhysical.Stabilizer.PaperExamples.pad_not_logConcave
#print axioms QecPhysical.Stabilizer.SamplingBounds.binomial_tail_chernoff
#print axioms QecPhysical.Stabilizer.SamplingBounds.kl_pos
#print axioms QecPhysical.Stabilizer.SamplingBounds.infidelity_exponential
#print axioms QecPhysical.Stabilizer.SamplingBounds.allZero_prob
#print axioms QecPhysical.Stabilizer.SamplingBounds.failure_prob_ge
#print axioms QecPhysical.Stabilizer.SamplingBounds.sample_size

-- Distance as minimum logical weight; the completeness formula of the computed section
#print axioms QecPhysical.Stabilizer.Uncorrectable.isDistance_iff_minWeight
#print axioms QecPhysical.Stabilizer.Uncorrectable.uncorrectable_iff_logical
#print axioms QecPhysical.Stabilizer.Completeness.certFormula_unsat
#print axioms QecPhysical.Stabilizer.Completeness.certFormula_checked

-- Hardness reduction as computable functions; exact distance from a SAT oracle
#print axioms QecPhysical.Stabilizer.DistanceExtraction.distanceOfTable_correct
#print axioms QecPhysical.Stabilizer.DistanceExtraction.distanceOfPoint_correct
#print axioms QecPhysical.Stabilizer.DistanceExtraction.distanceOfPointU_correct
#print axioms QecPhysical.Stabilizer.DistanceExtraction.isDistance_padRows
#print axioms QecPhysical.Stabilizer.DistanceExtraction.sparsePad_sparse
#print axioms QecPhysical.Stabilizer.DistanceExtraction.cor_sparsehard_extraction
#print axioms QecPhysical.Stabilizer.DistanceExtraction.cor_pointhard_extraction
#print axioms QecPhysical.Stabilizer.DistanceExtraction.cor_pointhard_extractionU
#print axioms QecPhysical.Stabilizer.Completeness.certFormula_sat_iff
#print axioms QecPhysical.Stabilizer.Completeness.distance_le_iff_sat
#print axioms QecPhysical.Stabilizer.Completeness.distance_isLeast
#print axioms QecPhysical.Stabilizer.Completeness.sat_at_n_iff_exists_distance

-- Computed section: variance of the union estimator, verified exact tables, end-to-end list certificates
#print axioms QecPhysical.Stabilizer.UnionEstimator.mean_sample
#print axioms QecPhysical.Stabilizer.UnionEstimator.second_moment_le
#print axioms QecPhysical.Stabilizer.UnionEstimator.variance_le
#print axioms QecPhysical.Stabilizer.UnionEstimator.stabilizer_union_estimator
#print axioms QecPhysical.Stabilizer.ListCertificate.symmetric_certificate
#print axioms QecPhysical.Stabilizer.ListCertificate.plain_certificate
#print axioms QecPhysical.Stabilizer.ListCertificate.complete_symmetric
#print axioms QecPhysical.Stabilizer.ListCertificate.distance_of_complete
#print axioms QecPhysical.Stabilizer.ListCertificate.leading_layer_sum

-- Direct reduction from SAT to the distance of a CSS code, and its composition with the extraction
#print axioms QecReliability.SatReduction.reduce_isotropic
#print axioms QecReliability.SatReduction.reduce_correct
#print axioms QecReliability.SatReduction.reduce_isDistance_le_iff
#print axioms QecReliability.SatReduction.reduce_isDistance_eq
#print axioms QecReliability.SatReduction.reduce_exists_isDistance
#print axioms QecReliability.SatReduction.reduce_size
#print axioms QecReliability.SatReduction.reduce_finrank
#print axioms QecReliability.SatReduction.reduce_logical_qubits
#print axioms QecReliability.SatReduction.sat_iff_table
#print axioms QecReliability.SatReduction.sat_iff_point
#print axioms QecReliability.SatReduction.sat_iff_pointU

-- Sampling section, last remark: averaging the exact rank values
#print axioms QecPhysical.Stabilizer.RankSampling.patternWeight_sum
#print axioms QecPhysical.Stabilizer.RankSampling.allCorrectable_prob
#print axioms QecPhysical.Stabilizer.RankSampling.failure_prob_ge
#print axioms QecPhysical.Stabilizer.RankSampling.rank_sample_size

-- Weight enumerators as model counts of 3-CNF formulas
#print axioms QecPhysical.Stabilizer.Enumerator.normWeightFormula_count
#print axioms QecPhysical.Stabilizer.Enumerator.normWeightFormula_width
#print axioms QecPhysical.Stabilizer.Enumerator.normWeightFormula_vars
#print axioms QecPhysical.Stabilizer.Enumerator.normWeightVars_eq
#print axioms QecPhysical.Stabilizer.Enumerator.stabWeightFormula_count
#print axioms QecPhysical.Stabilizer.Enumerator.stabWeightFormula_width
#print axioms QecPhysical.Stabilizer.Enumerator.stabWeightFormula_vars
#print axioms QecPhysical.Stabilizer.Enumerator.stabWeightVars_eq

-- Uncorrectable sets of size j as the projected models of one 3-CNF
#print axioms QecPhysical.Stabilizer.UncorrectableFormula.uncorrectableProb_eq_counts
#print axioms QecPhysical.Stabilizer.UncorrectableFormula.uncFormula_projected
#print axioms QecPhysical.Stabilizer.UncorrectableFormula.uncFormula_count
#print axioms QecPhysical.Stabilizer.UncorrectableFormula.uncFormula_contract

-- Statements, as elaborated
#check @QecReliability.IidErasure.iid_erasure_machine_guarantee_resources
#check @QecPhysical.Stabilizer.Uncorrectable.ambiguity_add_ambiguity_compl
#check @QecPhysical.Stabilizer.Uncorrectable.sum_union_eq_karpLuby
#check @QecPhysical.Stabilizer.Uncorrectable.channel_point_determines_distance
#check @QecPhysical.Stabilizer.Uncorrectable.minimal_eq_image_through_representative
#check @QecPhysical.Stabilizer.Uncorrectable.sum_eq_karpLuby_add_remainder
#check @QecReliability.TensorMachineG.Runtime.FixedQuantum.isotropic_tensor_machine_guarantee_general
#check @QecReliability.UncorrectableMachine.uncorrectable_machine_guarantee_sized
#check @QecPhysical.Stabilizer.Completeness.certFormula_checked
#check @QecReliability.SatReduction.reduce_correct
#check @QecReliability.SatReduction.sat_iff_table
#check @QecReliability.IidErasure.iid_erasure_machine_guarantee
#check @QecReliability.TensorMachine.Runtime.FixedQuantum.isotropic_tensor_machine_guarantee_strong
#check @QecPhysical.Stabilizer.Lift.distance_determination
#check @QecReliability.Padding.isotropicLift_fidelity_pad
#check @QecPhysical.Stabilizer.Uncorrectable.repairedCurve_rel
#check @QecPhysical.Stabilizer.Enumerator.normWeightFormula_count
#check @QecPhysical.Stabilizer.Enumerator.stabWeightFormula_count
#check @QecPhysical.Stabilizer.RankSampling.rank_sample_size
#check @QecPhysical.Stabilizer.UncorrectableFormula.uncFormula_contract
