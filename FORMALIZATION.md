# What is formalized

Paper statements and the Lean declarations that prove them. The declarations are in
the Lean 4.34.1 graph (sources in `lean/`). All of them are covered by the two audits
in `tools/audit/`, which report only the axioms `propext`, `Classical.choice` and
`Quot.sound`. Verbatim statements with file and line numbers:
`docs/FORMAL_STATEMENTS.md`. Numbering follows the manuscript in `paper/`; its
Appendix C has the same correspondence.

| Paper statement | Lean | Notes |
|---|---|---|
| Theorem 1 and Corollary 3 (iid flagged erasure, unconditional) | `QecReliability.IidErasure.iid_erasure_machine_guarantee` | One fixed machine with OpenAI's verified SAT engine: optimality of the flag decoder, run, time and space bounds on every coin string, antitone coefficients with exact endpoints, `f̂_j = 1 ↔ f_j = 1`, two-tail accuracy. The same guarantee for an arbitrary engine satisfying the SAT contract, with its running time as a parameter: `QecReliability.TensorMachine.Runtime.tensor_machine_guarantee`. |
| Proposition 2 (query count, bit length, query size) | conjuncts of `QecReliability.IidErasure.iid_erasure_machine_guarantee_resources` and `QecReliability.TensorMachine.Runtime.FixedQuantum.isotropic_tensor_machine_guarantee_resources` | |
| Remarks 4, 5, 6 | not formalized | Remark 4 is conditional on a part of OpenAI's manuscript that is not formalized; Remark 5 instantiates a Lean theorem of a different development at paper level. |
| Lemma 11 (anchored repair) | `QecReliability.PosetShapeRepair.repair_interval` | |
| Proposition 12 (distance determination) | `QecReliability.DistanceDetermination.zero_prefix_iff`, `QecPhysical.Stabilizer.Lift.distance_determination` | |
| Proposition 13 and Corollary 14 (distance from satisfiability; NP-hard for sparse inputs) | padding step: module `PaddingInvariance` (`QecReliability.Padding.*`); reduction from SAT: modules `SatCosetWeight`, `SatToDistance`, `SatLogicalQubit`, `SatHardness` | The NP-hardness conclusion itself is paper-level (see below). |
| Proposition 15, Corollary 16 (one point value determines the distance) | module `PointHardness`; `QecPhysical.Stabilizer.Uncorrectable.infidelity_point_determines_distance`, `...channel_point_determines_distance`, `...uncorrectableProb_point_determines_distance`; distance = minimum logical weight: `QecPhysical.Stabilizer.Uncorrectable.isDistance_iff_minWeight` | NP-hardness conclusion paper-level. |
| Corollaries 14 and 16 as explicit reductions; exact distance from a SAT oracle | module `DistanceExtraction` (`QecPhysical.Stabilizer.DistanceExtraction.cor_sparsehard_extraction`, `...cor_pointhard_extraction`); `QecReliability.SatReduction.sat_iff_point`; `QecPhysical.Stabilizer.Completeness.distance_le_iff_sat`, `...distance_isLeast` | |
| Corollary 17 and Remark 18 (uncorrectable probability) | mathematical core: module `UncorrectableProbability`; machine level through the repeated code: `QecReliability.UncorrectableMachine.uncorrectable_machine_guarantee(_sized)` with module `ProductCode` | The direct algorithm of the proof is proved at formula level (module `UncorrectableFormula`: `uncFormula_projected`, `uncFormula_count`, `uncorrectableProb_eq_counts`); a machine that runs it is not formalized. |
| Weight enumerators do not determine the curve; all worked examples | modules `EnumeratorExample`, `PaperExamples` | |
| Sampling section (tail bounds, Chernoff bound, sample size) | `QecPhysical.Stabilizer.PaperExamples.tail_bound`, modules `SamplingBounds`, `RankSampling` (`rank_sample_size`: averaging the exact rank values) | |
| Theorem 19 (latent circuit), arbitrary circuit | `QecReliability.LatentMachine.Runtime.FixedQuantum.isotropic_polynomial_endpoint_machine_guarantee`, `...isotropic_latent_machine_guarantee_resources` | Exact endpoints and unit coefficients, bit length, call count, query size for `r > 0`. |
| Theorem 19, monotone circuit | `QecReliability.LatentMonotone.latent_monotone_machine_guarantee` | Antitone coefficients, prefix of zero-infidelity layers. |
| Theorem 20 (multiclass), monotone circuit | `QecReliability.TensorMachine.Runtime.FixedQuantum.isotropic_tensor_machine_guarantee_strong` | |
| Theorem 20, general circuit | `QecReliability.TensorMachineG.Runtime.FixedQuantum.isotropic_tensor_machine_guarantee_general` | A separate fixed machine without the repair step. |
| Lemma 21 (explicit all-length hash) | not formalized | The machines use a fixed explicit certificate whose constants exceed `2^(2^58)`. |
| Section 7: identities behind the hybrid estimator | modules `HybridEstimator`, `HybridSymmetry` | |
| Section 7: completeness of the lists of minimal uncorrectable sets, distances, leading coefficients | modules `CompletenessFormula`, `CompletenessConverse`; `QecPhysical.Stabilizer.ListCertificate.symmetric_certificate`; checking programs `tools/lrat/CertifyList.lean`, `tools/lrat/CertifyCode.lean` | The certificates of the individual codes are LRAT refutations checked by these programs; results in `experiments/erasure/results/certificate_CODE.json` and `certified_lean_CODE.json`. For codes whose runs are not complete, `certified_CODE.json` records certificates of the Python-written formula checked by `tools/lrat/CheckLrat.lean`. |
| Section 7: variance of the union estimator; exhaustive reference tables | module `UnionEstimator`; module `ExactTable` with `tools/exact/ExactTable.lean` | Verified enumeration run for the small codes listed in `experiments/erasure/results/exact_lean_CODE.json`; other exhaustive tables are computed in Python. |

## What is not formalized, and why

| Item | Reason |
|---|---|
| Explicit hash of Appendix A (Lemma 21) | Requires a formalization of linear-size pairwise-independent hashing (Spielman-type codes) at all lengths. The machine theorems use a fixed certificate instead. |
| Remark 5 (a second machine-checked engine) | That engine uses a different machine model (`Turing.FinTM2`) and input conventions; a bridge comparable to the one built for the OpenAI engine would be needed. |
| NP-hardness conclusions of Corollaries 14 and 16 | The reduction from SAT is formalized (Proposition "Distance from satisfiability", with one logical qubit, and its composition with the extraction). Not formalized: the Cook–Levin theorem, a formal notion of NP, and the polynomial running time of the reduction (its output size is bounded in Lean). |
| Direct algorithm of Corollary 17 as a machine | Would need a further machine program (the E-projection of the Bad count). The repeated-code theorem covers the statement up to the endpoint and a `log(1/ε)` factor. |
| Exact distance and enumerators from a SAT or counting oracle as machines | New machine programs would be needed; the formulas are proved correct (`distance_le_iff_sat`, `distance_isLeast`; module `EnumeratorFormula`: `normWeightFormula_count`, `stabWeightFormula_count`). |
| One machine choosing between repair and no repair | Monotonicity of a circuit is not testable in polynomial time; the paper makes the choice an input. |
| Tape-level count of engine invocations | The engine is embedded in the machine; the count is not exposed as a separate tape-level statement. |
| Numerical content of Section 7 | Experiments (`experiments/erasure/`); the identities they use and the certificate checkers are formalized as listed above. |

## Trusted base

- The Lean 4.34.1 kernel and toolchain, the pinned Mathlib and dependencies,
  and OpenAI's verified SAT development at commit `4eaee87548250b2682affda7d05d947c05554bae` with the
  modifications described in `third_party/openai-math-4eaee875/NOTICE`.
- The kernel replay with `leanchecker` covers all 6,157 modules of the graph.
- The experiments additionally trust the SAT solvers and model counters named
  in `experiments/erasure/README.md`, except where a result is certified by a
  checked LRAT proof.
