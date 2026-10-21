/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

import CCDN
import CCDNPaper
import Solution
import Lean.Util.CollectAxioms

/-! Audit every exported declaration in this project's two libraries (the main library `CCDN`
and the paper library `CCDNPaper`), the vendored Bombieri–Vaaler and Mertens dependencies and
the `Solution` module that proves the compared statements. Imported declarations carry Lean's
transitive axiom metadata. This is an axiom audit, not an independent kernel implementation or a
proof of the target. -/

open Lean Elab Command

set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let modules := env.allImportedModuleNames
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut main : Nat := 0
  let mut paper : Nat := 0
  let mut vendor : Nat := 0
  let mut submission : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let some mod := modules[idx.toNat]? | throwError "Missing module for {name}"
    let isMain := (`CCDN).isPrefixOf mod
    let isPaper := (`CCDNPaper).isPrefixOf mod
    let isVendor := (`ArithmeticHeights).isPrefixOf mod || (`Mertens).isPrefixOf mod
    let isSubmission := mod == `Solution
    if !isMain && !isPaper && !isVendor && !isSubmission then continue
    let axioms ← collectAxioms name
    let bad := axioms.filter fun a => !allowed.contains a
    unless bad.isEmpty do
      throwError "Disallowed axioms in {name}: {bad}"
    if isMain then main := main + 1
    else if isPaper then paper := paper + 1
    else if isVendor then vendor := vendor + 1
    else submission := submission + 1
  unless main > 0 ∧ paper > 0 ∧ vendor > 0 ∧ submission > 0 do
    throwError "Audit coverage failure: main={main}, paper={paper}, vendor={vendor}, \
      submission={submission}"
  logInfo m!"Axiom audit passed: {main} main-library, {paper} paper-library, {vendor} vendor \
    and {submission} submission declarations; only {allowed}."

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

#print axioms CCDN.projective_dimension_growth
#print axioms CCDN.projectiveCurveBound
#print axioms CCDN.affineCurveBound
#print axioms CCDN.affine_hypersurface_dimension_growth
#print axioms CCDN.affine_hypersurface_dimension_growth_rat
#print axioms CCDN.projective_integral_curve_lower_bound
#print axioms CCDN.classGroup_two_torsion_bound
