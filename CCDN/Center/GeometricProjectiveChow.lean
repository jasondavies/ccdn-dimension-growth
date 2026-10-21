/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.ProjectivePermutation
public import CCDN.Center.ProjectiveChowIncidence
public import CCDN.Hilbert.FilteredHilbertPolynomial
public import CCDN.Hilbert.LinearProjectionFiltration
import CCDN.Algebra.ProjectionScalarExtension
import CCDN.Algebra.ProjectiveChartScalarExtension
import CCDN.Algebra.WeightedHomogeneousTransform
import CCDN.Center.GeometricProjectiveCurveProjection
import CCDN.Center.ProjectiveChowEquation
import CCDN.Center.ProjectiveClosureRecovery
import CCDN.Center.ProjectiveIncidencePermutation
import CCDN.Hilbert.HomogeneousPrimeComponents

/-!
A geometrically integral homogeneous prime ideal has an incidence equation
defined over its original coefficient field, without a prescribed chart.

Homogeneous ideals and coordinate permutations commute with scalar
extension, so choosing a nonempty chart preserves geometric primeness.
-/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

private lemma projectivePermutedIdeal_eq_projection_kernel
    {K : Type*} [Field K] {n : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) K))
    (e : Equiv.Perm (Fin (n + 1))) :
    projectivePermutedIdeal J e =
      RingHom.ker (projectionCoordinateMap J (fun i => X (e i))) := by
  ext f
  rw [mem_projectivePermutedIdeal, mem_projectionCoordinateMap_ker, rename_eq_aeval]
  rfl

private theorem projectivePermutedIdeal_scalar_extension
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

namespace CCDN
noncomputable section
open MvPolynomial

/-- Let `J` be a homogeneous prime ideal over `K` whose projective variety has dimension `m` and
which stays prime over the algebraically closed field `L`. Then there is an irreducible
polynomial `F` over `K` whose image over `L` is a projective Chow equation of the extension of
`J` to `L`, with some row degrees `δ`. -/
theorem exists_geometric_projective_chow_without_chart
    {K L : Type*} [Field K] [Field L] [Algebra K L] [IsAlgClosed L] {n m : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 2)) K)) [J.IsPrime]
    [(J.map (map (algebraMap K L))).IsPrime]
    (hJ : IsHomogeneousIdeal J)
    (hdim : (filteredHilbertPolynomial J).natDegree = m + 1) :
    ∃ (F : MvPolynomial (Fin (m + 1) × Fin (n + 2)) K) (δ : Fin (m + 1) → ℕ),
      Irreducible F ∧
      IsProjectiveChowEquation (J.map (map (algebraMap K L))) (map (algebraMap K L) F) δ := by
  classical
  obtain ⟨e, hJ', hX, hp⟩ := exists_projectivePermutedIdeal_chart J hJ (by omega)
  let J' := projectivePermutedIdeal J e
  have : J'.IsPrime := projectivePermutedIdeal_isPrime J e
  let : (J'.map (map (algebraMap K L))).IsPrime :=
    projectivePermutedIdeal_geometrically_prime J e
  obtain ⟨d,_,hdimdeg⟩ := exists_hasAffineDimensionDegree J' (Ideal.IsPrime.ne_top ‹J'.IsPrime›)
    ((congrArg Polynomial.natDegree hp).trans hdim)
  obtain ⟨hm,_⟩ := projectiveChartIdeal_hilbertPolynomial_parameters J' hJ' hX m d hdimdeg
  let : ((projectiveChartIdeal J').map (map (algebraMap K L))).IsPrime :=
    projectiveChartIdeal_geometrically_prime J' hX
  obtain ⟨F,δ,_,hF,hFL⟩ := exists_geometric_projective_chow_incidence_equation
    (L := L) (projectiveChartIdeal J') hm
  let ρ := chowColumnPermutation (r := m + 1) e
  refine ⟨rename ρ F,δ,?_,?_,?_,?_⟩
  · exact (MulEquiv.irreducible_iff (renameEquiv K ρ)).mpr hF
  · rw [map_rename]
    exact (MulEquiv.irreducible_iff (renameEquiv L ρ)).mpr hFL.irreducible
  · intro i
    rw [map_rename]
    apply weighted_homogeneous_rename (chowRowWeight i) (chowRowWeight i) ρ _ _ (δ i)
      (hFL.row_homogeneous i)
    intro q
    rfl
  · intro U
    rw [map_rename, eval_rename, hFL.eval_eq_zero_iff,
      projectiveClosureIdeal_chartIdeal_eq J' hJ' hX]
    change U ∘ chowColumnPermutation e ∈ projectiveChowIncidenceLocus (m + 1)
      ((projectivePermutedIdeal J e).map (map (algebraMap K L))) ↔ _
    rw [projectivePermutedIdeal_scalar_extension]
    exact projectiveChowIncidenceLocus_permuted (J.map (map (algebraMap K L)))
      (homogeneous_ideal_scalar_extension J hJ) e U

end
end CCDN
