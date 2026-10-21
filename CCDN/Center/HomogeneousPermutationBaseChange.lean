/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.ProjectivePermutation
public import CCDN.Projection.LinearProjectionFiltration
import CCDN.Projection.ProjectionScalarExtension
/-! Homogeneous ideals and coordinate permutations commute with scalar
extension, so choosing a nonempty chart preserves geometric primeness. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

lemma projectivePermutedIdeal_eq_projection_kernel
    {K : Type*} [Field K] {n : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) K))
    (e : Equiv.Perm (Fin (n + 1))) :
    projectivePermutedIdeal J e =
      RingHom.ker (projectionCoordinateMap J (fun i => X (e i))) := by
  ext f
  rw [mem_projectivePermutedIdeal, mem_projectionCoordinateMap_ker, rename_eq_aeval]
  rfl

theorem projectivePermutedIdeal_scalar_extension
    {K L : Type*} [Field K] [Field L] [Algebra K L] {n : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) K))
    (e : Equiv.Perm (Fin (n + 1))) :
    (projectivePermutedIdeal J e).map (map (algebraMap K L)) =
      projectivePermutedIdeal (J.map (map (algebraMap K L))) e := by
  rw [projectivePermutedIdeal_eq_projection_kernel, projection_kernel_scalar_extension,
    projectivePermutedIdeal_eq_projection_kernel]
  simp only [map_X]

end
end CCDN
