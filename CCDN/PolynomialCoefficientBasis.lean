module

public import CCDN.PolynomialLinearSpecialization
public import Mathlib.LinearAlgebra.Dimension.Localization

/-! A coefficient-field basis remains a basis after adjoining arbitrary
polynomial parameters. This records the scalar extension and its
fraction-field degree for the generic primitive-element argument. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial
attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- Coefficientwise extension is linear over the full parameter ring. -/
def coefficientPolynomialLinearMap {K A σ : Type*}
    [Field K] [CommRing A] [Algebra K A] (l : A →ₗ[K] K) :
    MvPolynomial σ A →ₗ[MvPolynomial σ K] MvPolynomial σ K where
  toFun := coefficientLinearMap l
  map_add' := map_add _
  map_smul' p q := by
    simpa only [Algebra.smul_def,MvPolynomial.algebraMap_def,
      Algebra.algebraMap_self,RingHom.id_apply] using coefficientLinearMap_map_mul l p q

lemma coefficient_polynomial_mul_C {A σ : Type*} [CommRing A]
    (q : MvPolynomial σ A) (a : A) (d : σ →₀ ℕ) :
    (q * C a).coeff d = q.coeff d * a := by
  rw [mul_comm,coeff_C_mul,mul_comm]

/-- The coefficient-coordinate isomorphism for a finite coefficient basis. -/
def polynomialCoefficientEquiv {K A σ ι : Type*}
    [Field K] [CommRing A] [Algebra K A] [Fintype ι]
    (b : Module.Basis ι K A) :
    MvPolynomial σ A ≃ₗ[MvPolynomial σ K] (ι → MvPolynomial σ K) where
  toFun q i := coefficientLinearMap (b.coord i) q
  invFun c := ∑i, map (algebraMap K A) (c i) * C (b i)
  map_add' q r := by
    funext i
    exact (coefficientLinearMap (b.coord i)).map_add q r
  map_smul' p q := by
    funext i
    exact (coefficientPolynomialLinearMap (b.coord i)).map_smul p q
  left_inv q := by
    ext d
    simp only [coeff_sum,coefficient_polynomial_mul_C,coeff_map,coefficientLinearMap_coeff,
      Module.Basis.coord_apply]
    simpa only [Algebra.smul_def] using b.sum_repr (q.coeff d)
  right_inv c := by
    classical
    funext i
    ext d
    simp only [coefficientLinearMap_coeff,coeff_sum,coefficient_polynomial_mul_C,coeff_map,map_sum,
      ← Algebra.smul_def,map_smul,Module.Basis.coord_apply,Module.Basis.repr_self]
    simp [Finsupp.single_apply]

/-- A finite basis of the coefficient algebra gives a basis over
the polynomial parameter ring. -/
def polynomialCoefficientBasis {K A σ ι : Type*}
    [Field K] [CommRing A] [Algebra K A] [Fintype ι]
    (b : Module.Basis ι K A) :
    Module.Basis ι (MvPolynomial σ K) (MvPolynomial σ A) :=
  Module.Basis.ofEquivFun (polynomialCoefficientEquiv b)

lemma polynomial_coefficient_finrank {K A σ ι : Type*}
    [Field K] [CommRing A] [Algebra K A] [Fintype ι]
    (b : Module.Basis ι K A) :
    Module.finrank (MvPolynomial σ K) (MvPolynomial σ A) = Fintype.card ι :=
  Module.finrank_eq_card_basis (polynomialCoefficientBasis b)

/-- Adjoining independent rational parameters preserves the degree of an
finite field extension. The tower instances specify the natural
inclusions of coefficient and parameter rings. -/
theorem polynomial_fraction_extension_finrank
    {K A R F σ ι : Type*} [Field K] [Field A] [Algebra K A]
    [Field R] [Field F] [Fintype ι]
    [Algebra (MvPolynomial σ K) R] [IsFractionRing (MvPolynomial σ K) R]
    [Algebra (MvPolynomial σ A) F] [IsFractionRing (MvPolynomial σ A) F]
    [Algebra (MvPolynomial σ K) F] [Algebra R F]
    [IsScalarTower (MvPolynomial σ K) R F]
    [IsScalarTower (MvPolynomial σ K) (MvPolynomial σ A) F]
    (b : Module.Basis ι K A) : Module.finrank R F = Fintype.card ι := by
  rw [IsFractionRing.finrank_eq (MvPolynomial σ K) R (MvPolynomial σ A) F]
  exact polynomial_coefficient_finrank b

end
end CCDN
