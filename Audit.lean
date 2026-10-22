import Manuscript
import Lean.Util.CollectAxioms

/-! Exhaustive transitive axiom audit, including private declarations.
Both actual end-to-end branches and all stated counting consequences are required.
The mathematical correspondence review complements this syntactic/kernel audit. -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let required : Array Name := #[
    ``Manuscript.theorem_1_1_higher_primitive,
    ``Manuscript.theorem_1_1_sk_primitive,
    ``Manuscript.proposition_5_2_higher_primitive,
    ``Manuscript.proposition_5_2_sk_primitive,
    ``Manuscript.RestrictedMachine.Exec.deterministic,
    ``Manuscript.RestrictedRecursiveMachine.Exec.deterministic,
    ``Manuscript.RestrictedSupportSharpCost.physical_trace_bound,
    ``Manuscript.SKRestrictedCandidateSharpCost.raw_candidate_bound,
    ``Manuscript.RestrictedSKSharpOuter.program_exec,
    ``Manuscript.SKColorfulCoefficientOutput.end_to_end,
    ``Manuscript.SKPhysicalEstimator.unbiased,
    ``Manuscript.SKPhysicalEstimator.coloring_mse,
    ``Manuscript.theorem_1_1_higher,
    ``Manuscript.theorem_1_1_sk,
    ``Manuscript.raw_cutoff_constant_pos,
    ``Manuscript.HigherOrderFinal.canonical_end_to_end,
    ``Manuscript.SKFinal.end_to_end,
    ``Manuscript.HigherOrderCorollaries.relative_counting,
    ``Manuscript.HigherOrderCorollaries.polynomial_confidence,
    ``Manuscript.SKCorollaries.relative_counting,
    ``Manuscript.SKCorollaries.polynomial_confidence,
    ``Manuscript.UniformTau.tau_tendsto_zero_fourth,
    ``Manuscript.UniformTau.tau_polynomial_tendsto_zero,
    ``Manuscript.UniformTau.tau_eventually_zero_of_bounded,
    ``Manuscript.UniformMixedMass.uniform_graphical_mass,
    ``Manuscript.UniformPhysicalMass.physical_edge_tail,
    ``Manuscript.UniformLowerTail.physical_lower_tail_uniform,
    ``Manuscript.UniformLowerTail.raw_negative_moment_uniform,
    ``Manuscript.HigherOrderAlgorithm.mse_bound,
    ``Manuscript.HigherOrderExecution.execute_polynomial,
    ``Manuscript.SKAlgorithm.mse_bound,
    ``Manuscript.SKTheorem.accuracy,
    ``Manuscript.SKGhostCoefficient.algorithm_eq_physical,
    ``Manuscript.SKPhysicalExecution.execute_value,
    ``Manuscript.CutoffExecution.cutoffSearch_correct,
    ``Manuscript.CurrentCutoff.lemma_5_1,
    ``Manuscript.OutputMeasurability.higher_canonical_execute_measurable,
    ``Manuscript.OutputMeasurability.sk_execute_measurable,
    ``Manuscript.OutputMeasurability.higher_failure_measurable,
    ``Manuscript.OutputMeasurability.sk_failure_measurable,
    ``Manuscript.OutputMeasurability.higher_relative_success_measurable,
    ``Manuscript.OutputMeasurability.sk_relative_success_measurable,
    ``Manuscript.SKChargeProjection.projectedAlgorithm_eq_generated,
    ``Manuscript.SKChargeProjection.projectedAlgorithm_eq_disorder,
    ``Manuscript.SKChargeProjection.manuscript_array_size,
    ``Manuscript.SKProjectedOutput.output_eq_execute,
    ``Manuscript.SKProjectedOutput.accuracy,
    ``Manuscript.EdgePreparationInstructions.prepareEdge_realized,
    ``Manuscript.EdgePreparationInstructions.prepareEdge_physical,
    ``Manuscript.Model.normalizedPartition_eq_graph_sum,
    ``Manuscript.FieldExpansion.log_partition_decomposition,
    ``Manuscript.SignPolynomial.second_moment,
    ``Manuscript.SignPolynomial.noise_inflation_identity,
    ``Manuscript.ConditionalLowerTail.reverse_hypercontractivity,
    ``Manuscript.ConditionalLowerTail.partition_negative_moment_le_graph_mass,
    ``Manuscript.ConditionalLowerTail.partition_lower_tail_le_graph_mass,
    ``Manuscript.SupportExponent.degreeExponent_ge_kappa,
    ``Manuscript.SupportDegrees.twice_support_le_totalDegree_add_boundary,
    ``Manuscript.SupportDegrees.actual_degreeExponent_ge_kappa,
    ``Manuscript.SupportEvaluation.localG_eq_exp_spin_sum,
    ``Manuscript.SupportEvaluation.retained_local_sum,
    ``Manuscript.SupportEvaluation.collapsed_local_sum,
    ``Manuscript.DisorderOrthogonality.independent_coefficients_second_moment,
    ``Manuscript.DisorderOrthogonality.normalizedPartition_second_moment,
    ``Manuscript.DisorderOrthogonality.physical_retained_family_error,
    ``Manuscript.DisorderLowerTail.integrable_restrictedNegativeMoment,
    ``Manuscript.DisorderLowerTail.restricted_negative_moment,
    ``Manuscript.DisorderLowerTail.physical_restricted_negative_moment,
    ``Manuscript.GhostParity.augment_erase,
    ``Manuscript.GhostParity.degreeState_add,
    ``Manuscript.MomentExponents.tailExponent_le_neg]
  for name in required do
    unless (env.find? name).any (fun ci => ci.isTheorem) do
      throwError "Missing required component theorem {name}"
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  let mut theorems : Nat := 0
  let mut manuscriptTheorems : Nat := 0
  let mut names : Array Name := #[]
  for (name, _) in env.constants.toList do
    let userName := (privateToUserName? name).getD name
    let inLocalModule := match env.getModuleIdxFor? name with
      | none => true
      | some i =>
        let moduleName := env.header.moduleNames[i]!
        (`Manuscript).isPrefixOf moduleName || (`SpinGlass).isPrefixOf moduleName
    if inLocalModule || (`Manuscript).isPrefixOf userName || (`SpinGlass).isPrefixOf userName then
      names := names.push name
  for name in names.qsort Name.lt do
    let axioms ← collectAxioms name
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Disallowed axiom {ax} in {name}"
    checked := checked + 1
    if let some (.thmInfo _) := env.find? name then
      theorems := theorems + 1
      let userName := (privateToUserName? name).getD name
      if (`Manuscript).isPrefixOf userName then
        manuscriptTheorems := manuscriptTheorems + 1
      logInfo m!"CHECKED {name}; axioms = {axioms.toList}"
  unless manuscriptTheorems > 0 do
    throwError "No new manuscript theorems found"
  logInfo m!"AXIOM AUDIT PASSED: {theorems} theorem declarations; {checked} total declarations; {manuscriptTheorems} manuscript theorem declarations."
  logInfo "REQUIRED ENDPOINTS PRESENT: both actual Theorem 1.1 branches and stated counting corollaries."
