module

public import CCDN.ProjectionScalarExtension
public import Mathlib.LinearAlgebra.Finsupp.Defs

/-! Coefficient-linear descent for arbitrary polynomial variable types.
A finite expansion in a coefficient-field basis proves exact ideal descent,
including nested-polynomial substitutions, without a supplied injectivity
or flatness hypothesis. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Module

/-- Apply a linear coefficient map without changing any monomial. -/
def polynomialCoefficientLinear {R A B σ : Type*} [CommSemiring R]
    [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (φ : A →ₗ[R] B) : MvPolynomial σ A →ₗ[R] MvPolynomial σ B :=
  (AddMonoidAlgebra.coeffLinearEquiv R).symm.toLinearMap ∘ₗ
    Finsupp.mapRange.linearMap φ ∘ₗ (AddMonoidAlgebra.coeffLinearEquiv R).toLinearMap

@[simp] lemma polynomialCoefficientLinear_coeff {R A B σ : Type*}
    [CommSemiring R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (φ : A →ₗ[R] B) (f : MvPolynomial σ A) (e : σ →₀ ℕ) :
    (polynomialCoefficientLinear φ f).coeff e = φ (f.coeff e) := rfl

@[simp] lemma polynomialCoefficientLinear_C {R A B σ : Type*}
    [CommSemiring R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (φ : A →ₗ[R] B) (a : A) :
    polynomialCoefficientLinear (σ := σ) φ (C a) = C (φ a) := by
  classical
  ext e
  simp only [polynomialCoefficientLinear_coeff, coeff_C]
  split_ifs <;> simp

lemma polynomialCoefficientLinear_mul_compatible {R A B σ : Type*}
    [CommSemiring R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (φ : A →ₗ[R] B) (θ : B →+* A)
    (hφ : ∀ a b, φ (a * θ b) = φ a * b)
    (f : MvPolynomial σ A) (g : MvPolynomial σ B) :
    polynomialCoefficientLinear φ (f * map θ g) =
      polynomialCoefficientLinear φ f * g := by
  classical
  ext e
  rw [polynomialCoefficientLinear_coeff, coeff_mul, coeff_mul, map_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [coeff_map, polynomialCoefficientLinear_coeff, hφ]

lemma polynomialCoefficientLinear_mul_map {K L σ : Type*}
    [Field K] [Field L] [Algebra K L]
    (φ : L →ₗ[K] K) (f : MvPolynomial σ L) (g : MvPolynomial σ K) :
    polynomialCoefficientLinear φ (f * map (algebraMap K L) g) =
      polynomialCoefficientLinear φ f * g := by
  apply polynomialCoefficientLinear_mul_compatible
  intro a b
  simpa only [Algebra.smul_def, smul_eq_mul, mul_comm, Algebra.algebraMap_self,
    RingHom.id_apply] using φ.map_smul b a

/-- Coefficient functionals send elements of an extended ideal into the
original ideal, for any variable type. -/
theorem polynomialCoefficientLinear_mem_scalar_extension {K L σ : Type*}
    [Field K] [Field L] [Algebra K L]
    (I : Ideal (MvPolynomial σ K)) (g : MvPolynomial σ L)
    (hg : g ∈ I.map (map (algebraMap K L))) (φ : L →ₗ[K] K) :
    polynomialCoefficientLinear φ g ∈ I := by
  have hh : ∀ (ψ : L →ₗ[K] K) (r : MvPolynomial σ L),
      polynomialCoefficientLinear ψ (r * g) ∈ I := by
    induction hg using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, hf, rfl⟩ := hx
      intro ψ r
      rw [polynomialCoefficientLinear_mul_map]
      exact I.mul_mem_left _ hf
    | zero =>
      intro ψ r
      rw [mul_zero, map_zero]
      exact I.zero_mem
    | add x y _ _ hx hy =>
      intro ψ r
      rw [mul_add, map_add]
      exact I.add_mem (hx ψ r) (hy ψ r)
    | smul a x _ hx =>
      intro ψ r
      simpa only [smul_eq_mul, mul_assoc] using hx ψ (r * a)
  simpa only [one_mul] using hh φ 1

/-- Every polynomial over the extension is a finite sum of base-field
polynomials obtained by its basis-coordinate functionals. -/
theorem polynomial_coefficient_basis_expansion {K L σ ι : Type*}
    [Field K] [Field L] [Algebra K L]
    (b : Basis ι K L) (g : MvPolynomial σ L) :
    ∃ s : Finset ι,
      g = ∑ i ∈ s, C (b i) *
        map (algebraMap K L) (polynomialCoefficientLinear (b.coord i) g) := by
  classical
  let s := g.support.biUnion (fun e => (b.repr (g.coeff e)).support)
  refine ⟨s, ?_⟩
  ext e
  simp only [coeff_sum, coeff_C_mul, coeff_map, polynomialCoefficientLinear_coeff]
  have hb := b.linearCombination_repr (g.coeff e)
  change (b.repr (g.coeff e)).sum (fun i c => c • b i) = g.coeff e at hb
  by_cases he : e ∈ g.support
  · have hsub : (b.repr (g.coeff e)).support ⊆ s := by
      intro i hi
      exact Finset.mem_biUnion.mpr ⟨e, he, hi⟩
    calc
      g.coeff e = ∑ i ∈ (b.repr (g.coeff e)).support, (b.repr (g.coeff e)) i • b i := hb.symm
      _ = ∑ i ∈ s, (b.repr (g.coeff e)) i • b i := by
        apply Finset.sum_subset hsub
        intro i _ hi
        simp only [Finsupp.notMem_support_iff.mp hi, zero_smul]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        simp only [Basis.coord_apply, Algebra.smul_def, mul_comm]
  · have hz : g.coeff e = 0 := notMem_support_iff.mp he
    simp [hz]

/-- Exact membership in the scalar-extended ideal is detected by all
coefficient-linear functionals. -/
theorem mem_scalar_extension_iff_polynomialCoefficientLinear {K L σ : Type*}
    [Field K] [Field L] [Algebra K L]
    (I : Ideal (MvPolynomial σ K)) (g : MvPolynomial σ L) :
    g ∈ I.map (map (algebraMap K L)) ↔
      ∀ φ : L →ₗ[K] K, polynomialCoefficientLinear φ g ∈ I := by
  constructor
  · intro hg φ
    exact polynomialCoefficientLinear_mem_scalar_extension I g hg φ
  · intro h
    obtain ⟨s, hs⟩ := polynomial_coefficient_basis_expansion (Module.Free.chooseBasis K L) g
    rw [hs]
    apply Ideal.sum_mem
    intro i _
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (h _))

end
end CCDN
