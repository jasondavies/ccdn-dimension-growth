module

import CCDN
import Solution
import Lean.Util.CollectAxioms

/-! Audit every exported declaration in this project's mathematical modules, the vendored
Bombieri–Vaaler dependency and the `Solution` module that proves the compared statements.
Imported declarations carry Lean's transitive axiom metadata. This is an axiom audit, not an
independent kernel implementation or a proof of the target. -/

open Lean Elab Command

set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let modules := env.allImportedModuleNames
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut own : Nat := 0
  let mut vendor : Nat := 0
  let mut submission : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let some mod := modules[idx.toNat]? | throwError "Missing module for {name}"
    let isOwn := (`CCDN).isPrefixOf mod
    let isVendor := (`ArithmeticHeights).isPrefixOf mod
    let isSubmission := mod == `Solution
    if !isOwn && !isVendor && !isSubmission then continue
    let axioms ← collectAxioms name
    let bad := axioms.filter fun a => !allowed.contains a
    unless bad.isEmpty do
      throwError "Disallowed axioms in {name}: {bad}"
    if isOwn then own := own + 1
    else if isVendor then vendor := vendor + 1
    else submission := submission + 1
  unless own > 0 ∧ vendor > 0 ∧ submission > 0 do
    throwError "Audit coverage failure: project={own}, vendor={vendor}, submission={submission}"
  logInfo m!"Axiom audit passed: {own} project, {vendor} vendor and {submission} submission \
    declarations; only {allowed}."

/-! The compared statements (see `comparator.json`). -/

#print axioms CCDN.Submission.affineCount_set_finite
#print axioms CCDN.Submission.projectiveCount_set_finite
#print axioms CCDN.Submission.projective_dimension_growth
#print axioms CCDN.Submission.projective_curve_bound
#print axioms CCDN.Submission.affine_curve_bound
#print axioms CCDN.Submission.affine_hypersurface_bound
#print axioms CCDN.Submission.affine_hypersurface_bound_rat
#print axioms CCDN.Submission.projective_plane_curve_lower_bound
#print axioms CCDN.Submission.classGroup_two_torsion_bound

/-! The library endpoints they are derived from. -/

#print axioms CCDN.projective_dimension_growth_cubic
#print axioms CCDN.projectiveCurveBound
#print axioms CCDN.affineCurveBound
#print axioms CCDN.top_form_hypersurface_dimension_growth_cubic
#print axioms CCDN.rational_top_form_hypersurface_dimension_growth_cubic
#print axioms CCDN.projective_integral_curve_lower_bound
#print axioms CCDN.classGroup_two_torsion_bound
