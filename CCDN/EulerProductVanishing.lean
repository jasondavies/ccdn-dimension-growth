module

public import CCDN.EulerGenericFactors

/-! Characteristic-independent vanishing on products. A generic integral
identity is proved in the fraction field and then specialized; this includes
inseparable and repeated factors in every characteristic. -/

@[expose] public section
namespace CCDN
noncomputable section
open Polynomial

lemma bivariateMap_injective {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (hφ : Function.Injective φ) :
    Function.Injective (bivariateMap φ) :=
  Polynomial.map_injective _ (Polynomial.map_injective φ hφ)

theorem genericEulerProduct_minor_eq_zero
    (k a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a + b = k + 2)
    (rows : Fin ((k + 2) ^ 2 - 1) → ℕ × ℕ)
    (cols : Fin ((k + 2) ^ 2 - 1) → EulerColumns k) :
    ((eulerClosedFormCoefficientMatrix k
      (genericEulerFactorLeft a b * genericEulerFactorRight a b)).submatrix rows cols).det = 0 := by
  let R := MvPolynomial (EulerFactorParameters a b) ℤ
  let F := FractionRing R
  let φ := algebraMap R F
  let G := genericEulerFactorLeft a b
  let H := genericEulerFactorRight a b
  have hφ := IsFractionRing.injective R F
  have hmap := bivariateMap_injective φ hφ
  have hg : bivariateTotalDegree (bivariateMap φ G) ≤ a :=
    (bivariateTotalDegree_map_le φ G).trans (eulerPolynomialFromCoefficients_degree a _)
  have hh : bivariateTotalDegree (bivariateMap φ H) ≤ b :=
    (bivariateTotalDegree_map_le φ H).trans (eulerPolynomialFromCoefficients_degree b _)
  have hne : eulerFactorPair a b (bivariateMap φ G) (bivariateMap φ H) ≠ 0 := by
    intro hz
    have he := eulerFactorPair_map φ a b G H
    rw [hz] at he
    apply genericEulerFactorPair_ne_zero a b ha hb
    apply Prod.ext
    · apply hmap
      simpa only [Prod.fst_zero, map_zero] using congrArg Prod.fst he
    · apply hmap
      simpa only [Prod.snd_zero, map_zero] using congrArg Prod.snd he
  obtain ⟨u, hu, hk⟩ := exists_eulerFactorKernel k a b ha hb hab
    (bivariateMap φ G) (bivariateMap φ H) hg hh hne
  have hz := eulerClosedForm_minor_eq_zero_of_kernel k _ u hu hk rows cols
  apply hφ
  rw [map_zero, eulerClosedForm_minor_map, map_mul]
  exact hz

/-- Every maximal Euler minor vanishes on a product with two positive
degree budgets, over an arbitrary commutative coefficient ring. -/
theorem eulerClosedForm_minor_eq_zero_of_product
    {R : Type*} [CommRing R] (k a b : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = k + 2)
    (g h : R[X][X]) (hg : bivariateTotalDegree g ≤ a)
    (hh : bivariateTotalDegree h ≤ b)
    (rows : Fin ((k + 2) ^ 2 - 1) → ℕ × ℕ)
    (cols : Fin ((k + 2) ^ 2 - 1) → EulerColumns k) :
    ((eulerClosedFormCoefficientMatrix k (g * h)).submatrix rows cols).det = 0 := by
  let φ := genericEulerFactorSpecialization a b g h
  have hz := congrArg φ (genericEulerProduct_minor_eq_zero k a b ha hb hab rows cols)
  rw [map_zero, eulerClosedForm_minor_map, map_mul,
    genericEulerFactorLeft_specialize a b g h hg,
    genericEulerFactorRight_specialize a b g h hh] at hz
  exact hz

end
end CCDN
