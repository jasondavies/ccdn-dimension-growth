module

public import AffineCurveCounting.ProjectiveIncidencePermutation
public import AffineCurveCounting.ProjectiveChartScalarExtension

/-! Homogeneous ideals and coordinate permutations commute with scalar
extension, so choosing a nonempty chart preserves geometric primeness. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

theorem homogeneous_ideal_scalar_extension
    {K L : Type*} [Field K] [Field L] [Algebra K L] {n : ℕ}
    (J : Ideal (MvPolynomial (Fin n) K))
    (hJ : ∀ f ∈ J, ∀ M, homogeneousComponent M f ∈ J) :
    ∀ f ∈ J.map (map (algebraMap K L)), ∀ M,
      homogeneousComponent M f ∈ J.map (map (algebraMap K L)) := by
  intro f hf M
  by_contra hnot
  obtain ⟨φ,hφ⟩ := exists_coefficientLinearPolynomial_not_mem J _ hnot
  apply hφ
  rw [coefficientLinearPolynomial_homogeneousComponent]
  exact hJ _ (coefficientLinearPolynomial_mem_scalar_extension J f hf φ) M

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
end AffineCurveCounting
