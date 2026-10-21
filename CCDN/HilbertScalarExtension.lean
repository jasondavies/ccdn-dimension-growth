module

public import CCDN.PolynomialLinearDescent
public import CCDN.FilteredHilbertPolynomial

/-! Scalar extension preserves the filtered Hilbert polynomial.
Coefficient-linear functionals descend elements of the extended ideal.
A functional nonzero on a leading coefficient preserves its leading exponent. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial
open scoped MonomialOrder

lemma coefficientLinearPolynomial_zero {K L : Type*}
    [Field K] [Field L] [Algebra K L] {n : ℕ} (φ : L →ₗ[K] K) :
    coefficientLinearPolynomial (n := n) φ 0 = 0 := by
  ext a
  simp [coefficientLinearPolynomial_coeff]

lemma coefficientLinearPolynomial_add {K L : Type*}
    [Field K] [Field L] [Algebra K L] {n : ℕ}
    (φ : L →ₗ[K] K) (f g : MvPolynomial (Fin n) L) :
    coefficientLinearPolynomial φ (f + g) =
      coefficientLinearPolynomial φ f + coefficientLinearPolynomial φ g := by
  ext a
  simp [coefficientLinearPolynomial_coeff]

lemma coefficientLinearPolynomial_mul_map {K L : Type*}
    [Field K] [Field L] [Algebra K L] {n : ℕ}
    (φ : L →ₗ[K] K) (g : MvPolynomial (Fin n) L) (f : MvPolynomial (Fin n) K) :
    coefficientLinearPolynomial φ (g * map (algebraMap K L) f) =
      coefficientLinearPolynomial φ g * f := by
  classical
  ext a
  rw [coefficientLinearPolynomial_coeff, coeff_mul, coeff_mul, map_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [coeff_map, coefficientLinearPolynomial_coeff]
  simpa only [Algebra.smul_def, smul_eq_mul, mul_comm, Algebra.algebraMap_self, RingHom.id_apply] using
    φ.map_smul (f.coeff b.2) (g.coeff b.1)

/-- Every coefficient-linear image of an extended ideal element belongs
to the original ideal. -/
theorem coefficientLinearPolynomial_mem_scalar_extension
    {K L : Type*} [Field K] [Field L] [Algebra K L] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K))
    (g : MvPolynomial (Fin n) L) (hg : g ∈ I.map (map (algebraMap K L)))
    (φ : L →ₗ[K] K) :
    coefficientLinearPolynomial φ g ∈ I := by
  have hh : ∀ (ψ : L →ₗ[K] K) (r : MvPolynomial (Fin n) L),
      coefficientLinearPolynomial ψ (r * g) ∈ I := by
    induction hg using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, hf, rfl⟩ := hx
      intro ψ r
      rw [coefficientLinearPolynomial_mul_map]
      exact I.mul_mem_left _ hf
    | zero =>
      intro ψ r
      rw [mul_zero, coefficientLinearPolynomial_zero]
      exact I.zero_mem
    | add x y _ _ hx hy =>
      intro ψ r
      rw [mul_add, coefficientLinearPolynomial_add]
      exact I.add_mem (hx ψ r) (hy ψ r)
    | smul a x _ hx =>
      intro ψ r
      simpa only [smul_eq_mul, mul_assoc] using hx ψ (r * a)
  simpa only [one_mul] using hh φ 1

lemma coefficientLinearPolynomial_monomialOrder_degree
    {K L : Type*} [Field K] [Field L] [Algebra K L] {n : ℕ}
    (φ : L →ₗ[K] K) (g : MvPolynomial (Fin n) L) (m : MonomialOrder (Fin n))
    (hφ : φ (g.coeff (m.degree g)) ≠ 0) :
    m.degree (coefficientLinearPolynomial φ g) = m.degree g := by
  apply m.toSyn.injective
  apply le_antisymm
  · apply MonomialOrder.degree_le_iff.mpr
    intro a ha
    apply m.le_degree
    rw [mem_support_iff] at ha ⊢
    intro hz
    apply ha
    rw [coefficientLinearPolynomial_coeff, hz, map_zero]
  · apply m.le_degree
    rw [mem_support_iff, coefficientLinearPolynomial_coeff]
    exact hφ

theorem standardExponents_scalar_extension
    {K L : Type*} [Field K] [Field L] [Algebra K L] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) (m : MonomialOrder (Fin n)) :
    Ideal.standardExponents (I.map (map (algebraMap K L))) m = Ideal.standardExponents I m := by
  classical
  have hmapinj : Function.Injective (map (algebraMap K L) :
      MvPolynomial (Fin n) K → MvPolynomial (Fin n) L) :=
    map_injective _ (algebraMap K L).injective
  have hmapdeg (f : MvPolynomial (Fin n) K) :
      m.degree (map (algebraMap K L) f) = m.degree f := by
    simp only [MonomialOrder.degree]
    rw [support_map_of_injective f (algebraMap K L).injective]
  ext a
  constructor
  · intro ha f hf hf0
    have hh := ha (map (algebraMap K L) f) (Ideal.mem_map_of_mem _ hf)
      (map_ne_zero_iff _ hmapinj |>.mpr hf0)
    simpa only [hmapdeg] using hh
  · intro ha g hg hg0
    have hc := (m.coeff_degree_ne_zero_iff).mpr hg0
    obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_ne_zero K hc
    have hdescent := coefficientLinearPolynomial_mem_scalar_extension I g hg φ
    have hnonzero : coefficientLinearPolynomial φ g ≠ 0 := by
      intro he
      have hh := coefficientLinearPolynomial_coeff φ g (m.degree g)
      have hz : φ (g.coeff (m.degree g)) = 0 := by simpa [he] using hh.symm
      exact hφ hz
    simpa only [coefficientLinearPolynomial_monomialOrder_degree φ g m hφ] using
      ha _ hdescent hnonzero

theorem filteredCoordinateSpace_finrank_scalar_extension
    {K L : Type*} [Field K] [Field L] [Algebra K L] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) (N : ℕ) :
    Module.finrank L (filteredCoordinateSpace (I.map (map (algebraMap K L))) N) =
      Module.finrank K (filteredCoordinateSpace I N) := by
  rw [filteredCoordinateSpace_finrank_eq_standard_card,
    filteredCoordinateSpace_finrank_eq_standard_card]
  simp only [Ideal.boundedStandardExponents, standardExponents_scalar_extension]

theorem filteredHilbertPolynomial_scalar_extension
    {K L : Type*} [Field K] [Field L] [Algebra K L] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) :
    filteredHilbertPolynomial (I.map (map (algebraMap K L))) = filteredHilbertPolynomial I := by
  apply filteredHilbertPolynomial_eq_of_eventual
  obtain ⟨N, hN⟩ := filteredHilbertPolynomial_spec I
  refine ⟨N, fun M hM => ?_⟩
  rw [hN M hM, filteredCoordinateSpace_finrank_scalar_extension]

end
end CCDN
