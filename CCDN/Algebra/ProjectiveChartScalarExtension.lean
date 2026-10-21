module

public import CCDN.Projection.ProjectionScalarExtension
public import CCDN.Algebra.ProjectiveChartIdeal
public import CCDN.Algebra.HomogeneousLinearDescent
public import CCDN.Auxiliary.ScaledHypersurfaceBadPrimes
/-! Projective affine charts commute with extension of coefficients.
In particular the standard chart of a geometrically integral projective
variety is geometrically integral. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

lemma coefficientLinearPolynomial_affineChart
    {K L : Type*} [Field K] [Field L] [Algebra K L] {n : ℕ}
    (φ : L →ₗ[K] K) (f : MvPolynomial (Fin (n + 1)) L) :
    coefficientLinearPolynomial φ (affineChart n f) =
      affineChart n (coefficientLinearPolynomial φ f) := by
  have h := coefficientLinearPolynomial_aeval φ
    (Fin.cons (1 : MvPolynomial (Fin n) K) X) f
  have he : (fun i : Fin (n + 1) => map (algebraMap K L)
      ((Fin.cons (1 : MvPolynomial (Fin n) K) X :
        Fin (n + 1) → MvPolynomial (Fin n) K) i)) =
      (Fin.cons 1 X : Fin (n + 1) → MvPolynomial (Fin n) L) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  rw [he] at h
  exact h

lemma coefficientLinearPolynomial_boundedHomogenize
    {K L : Type*} [Field K] [Field L] [Algebra K L] {n D : ℕ}
    (φ : L →ₗ[K] K) (f : MvPolynomial (Fin n) L) (hf : f.totalDegree ≤ D) :
    coefficientLinearPolynomial φ (boundedHomogenize D f) =
      boundedHomogenize D (coefficientLinearPolynomial φ f) := by
  apply affineChart_injective_on_homogeneous
    (coefficientLinearPolynomial_homogeneous φ _ (boundedHomogenize_homogeneous f hf))
    (boundedHomogenize_homogeneous _ ((coefficientLinearPolynomial_degree φ f).trans hf))
  rw [← coefficientLinearPolynomial_affineChart,
    affineChart_boundedHomogenize, affineChart_boundedHomogenize]

lemma projectiveChartIdeal_mem_iff_boundedHomogenize
    {K : Type*} [Field K] {n D : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) K)) [I.IsPrime]
    (hX : X 0 ∉ I) (f : MvPolynomial (Fin n) K) (hf : f.totalDegree ≤ D) :
    f ∈ projectiveChartIdeal I ↔ boundedHomogenize D f ∈ I := by
  apply coordinate_kernel_mem_iff_homogenize I _ (IsFractionRing.injective _ _) _ f hf
  intro h
  apply hX
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  exact (IsFractionRing.injective (MvPolynomial (Fin (n + 1)) K ⧸ I)
    (FractionRing (MvPolynomial (Fin (n + 1)) K ⧸ I))) (by simpa using h)

theorem projectiveChartIdeal_scalar_extension
    {K L : Type*} [Field K] [Field L] [Algebra K L] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) K)) [I.IsPrime]
    [(I.map (map (algebraMap K L))).IsPrime] (hX : X 0 ∉ I) :
    (projectiveChartIdeal I).map (map (algebraMap K L)) =
      projectiveChartIdeal (I.map (map (algebraMap K L))) := by
  have hXL : X 0 ∉ I.map (map (algebraMap K L)) := by
    simpa only [map_X] using
      (not_congr (mem_ideal_scalar_extension_iff (L := L) I (X 0))).mpr hX
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro f hf
    rw [Ideal.mem_comap, projectiveChartIdeal_mem_iff_boundedHomogenize
      _ hXL _ (show (map (algebraMap K L) f).totalDegree ≤ f.totalDegree from
        Finset.sup_mono (support_map_subset _ _))]
    have hm : map (algebraMap K L) (boundedHomogenize f.totalDegree f) =
        boundedHomogenize f.totalDegree (map (algebraMap K L) f) := by
      rw [← scaledHomogenize_one, scaledHomogenize_map, map_one, scaledHomogenize_one]
    rw [← hm]
    exact Ideal.mem_map_of_mem _
      ((projectiveChartIdeal_mem_iff_boundedHomogenize I hX f le_rfl).mp hf)
  · intro g hg
    by_contra hnot
    obtain ⟨φ, hφ⟩ := exists_coefficientLinearPolynomial_not_mem (projectiveChartIdeal I) g hnot
    apply hφ
    rw [projectiveChartIdeal_mem_iff_boundedHomogenize I hX _
      (coefficientLinearPolynomial_degree φ g), ← coefficientLinearPolynomial_boundedHomogenize
      φ g le_rfl]
    exact coefficientLinearPolynomial_mem_scalar_extension I _
      ((projectiveChartIdeal_mem_iff_boundedHomogenize _ hXL g le_rfl).mp hg) φ

theorem projectiveChartIdeal_geometrically_prime
    {K L : Type*} [Field K] [Field L] [Algebra K L] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) K)) [I.IsPrime]
    [(I.map (map (algebraMap K L))).IsPrime] (hX : X 0 ∉ I) :
    ((projectiveChartIdeal I).map (map (algebraMap K L))).IsPrime := by
  rw [projectiveChartIdeal_scalar_extension I hX]
  infer_instance

end
end CCDN
