module

import AffineCurveCounting
import Lean.Util.CollectAxioms

/-! Audit every exported declaration in this project's mathematical modules and the vendored
Bombieri–Vaaler dependency. Imported declarations carry Lean's transitive axiom metadata.
This is an axiom audit, not an independent kernel implementation or a proof of the target. -/

open Lean Elab Command

set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let modules := env.allImportedModuleNames
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut own : Nat := 0
  let mut vendor : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let some mod := modules[idx.toNat]? | throwError "Missing module for {name}"
    let isOwn := (`AffineCurveCounting).isPrefixOf mod
    let isVendor := (`ArithmeticHeights).isPrefixOf mod
    if !isOwn && !isVendor then continue
    let axioms ← collectAxioms name
    let bad := axioms.filter fun a => !allowed.contains a
    unless bad.isEmpty do
      throwError "Disallowed axioms in {name}: {bad}"
    if isOwn then own := own + 1 else vendor := vendor + 1
  unless own > 0 ∧ vendor > 0 do
    throwError "Audit coverage failure: project={own}, vendor={vendor}"
  logInfo m!"Axiom audit passed: {own} project and {vendor} vendor declarations; only {allowed}."

#print axioms Int.Matrix.exists_ne_zero_mulVec_eq_zero_iSup_abs_le_det_rpow
#print axioms AffineCurveCounting.exists_small_vanishing_polynomial
#print axioms AffineCurveCounting.exists_auxiliary_not_dvd
#print axioms AffineCurveCounting.coefficient_height_elimination
#print axioms AffineCurveCounting.triangular_pow_dvd_polynomial_eval_minorGcd
#print axioms AffineCurveCounting.sum_log_prime_powers_le_log
