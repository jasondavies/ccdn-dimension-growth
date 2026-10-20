module

public import CCDN.EulerPairBasisValues

/-! Euler columns and their coefficient minors commute with every coefficient
ring homomorphism, including specialization and reduction in any characteristic. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Module

lemma eulerPairCoordinates_basis_left {R : Type*} [CommRing R] (k : ℕ) (i : EulerLowIndex k) :
    eulerPairCoordinates R k (eulerPairBasis R k (.inl i)) =
      (monomial ((boundedExponentEquivSym (Fin 2) k).symm i).val 1, 0) := by
  simp [eulerPairCoordinates, eulerPairBasis, Basis.prod_apply, eulerLowBasis_apply]

lemma eulerPairCoordinates_basis_right {R : Type*} [CommRing R] (k : ℕ) (i : EulerLowIndex k) :
    eulerPairCoordinates R k (eulerPairBasis R k (.inr (.inl i))) =
      (0, monomial ((boundedExponentEquivSym (Fin 2) k).symm i).val 1) := by
  simp [eulerPairCoordinates, eulerPairBasis, Basis.prod_apply, eulerLowBasis_apply]

lemma eulerPairCoordinates_basis_radial {R : Type*} [CommRing R] (k : ℕ) (i : EulerTopIndex k) :
    eulerPairCoordinates R k (eulerPairBasis R k (.inr (.inr i))) =
      (X 1 * monomial ((exactExponentEquivSym (Fin 2) k).symm i).val 1,
        -(X 0 * monomial ((exactExponentEquivSym (Fin 2) k).symm i).val 1)) := by
  simp [eulerPairCoordinates, eulerPairBasis, Basis.prod_apply, eulerTopBasis_apply]

lemma eulerPairCoordinates_basis_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (k : ℕ) (i : EulerColumns k) :
    (map φ (eulerPairCoordinates R k (eulerPairBasis R k i)).1,
      map φ (eulerPairCoordinates R k (eulerPairBasis R k i)).2) =
      eulerPairCoordinates S k (eulerPairBasis S k i) := by
  rcases i with i | i | i
  · rw [eulerPairCoordinates_basis_left, eulerPairCoordinates_basis_left]
    simp
  · rw [eulerPairCoordinates_basis_right, eulerPairCoordinates_basis_right]
    simp
  · rw [eulerPairCoordinates_basis_radial, eulerPairCoordinates_basis_radial]
    simp

lemma eulerBivariatePair_basis_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (k : ℕ) (i : EulerColumns k) :
    (bivariateMap φ (eulerBivariatePair R k (eulerPairBasis R k i)).1,
      bivariateMap φ (eulerBivariatePair R k (eulerPairBasis R k i)).2) =
      eulerBivariatePair S k (eulerPairBasis S k i) := by
  simp only [eulerBivariatePair, LinearMap.comp_apply, LinearMap.prodMap_apply,
    AlgEquiv.toLinearMap_apply, bivariatePolynomialEquiv_map]
  have hh := eulerPairCoordinates_basis_map φ k i
  apply Prod.ext
  · exact congrArg (bivariatePolynomialEquiv S) (congrArg Prod.fst hh)
  · exact congrArg (bivariatePolynomialEquiv S) (congrArg Prod.snd hh)

/-- The exact-order coefficient matrix specializes entry by entry over any
commutative coefficient ring. -/
theorem eulerClosedFormCoefficientMatrix_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (k : ℕ) (f : Polynomial (Polynomial R)) :
    (eulerClosedFormCoefficientMatrix k f).map φ =
      eulerClosedFormCoefficientMatrix k (bivariateMap φ f) := by
  ext i j
  change φ (((closedFormOperator f (eulerBivariatePair R k (eulerPairBasis R k j))).coeff i.1).coeff i.2) = _
  rw [← bivariateMap_coeff, bivariateMap_closedFormOperator, eulerBivariatePair_basis_map]
  rfl

theorem eulerClosedForm_minor_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (k r : ℕ) (f : Polynomial (Polynomial R))
    (a : Fin r → ℕ × ℕ) (c : Fin r → EulerColumns k) :
    φ (((eulerClosedFormCoefficientMatrix k f).submatrix a c).det) =
      ((eulerClosedFormCoefficientMatrix k (bivariateMap φ f)).submatrix a c).det := by
  rw [φ.map_det]
  change (((eulerClosedFormCoefficientMatrix k f).map φ).submatrix a c).det = _
  rw [eulerClosedFormCoefficientMatrix_map]

/-- Characteristic-zero irreducibility supplies a nonzero integer
minor of order d^2-1. No universal irreducibility theorem is assumed. -/
theorem exists_eulerClosedForm_integer_minor
    {F : Type*} [Field F] [CharZero F] [IsAlgClosed F]
    (k : ℕ) (f : Polynomial (Polynomial ℤ))
    (hf : Irreducible (bivariateMap (Int.castRingHom F) f))
    (a : F) (ha : a ≠ 0)
    (hl : (bivariateMap (Int.castRingHom F) f).leadingCoeff = Polynomial.C a)
    (hdeg : (bivariateMap (Int.castRingHom F) f).natDegree = k + 2) :
    ∃ (rows : Fin ((k + 2) ^ 2 - 1) → ℕ × ℕ)
      (cols : Fin ((k + 2) ^ 2 - 1) → EulerColumns k),
      Function.Injective rows ∧ Function.Injective cols ∧
      ((eulerClosedFormCoefficientMatrix k f).submatrix rows cols).det ≠ 0 := by
  obtain ⟨rows, cols, hr, hc, hdet⟩ := exists_eulerClosedForm_nonzero_minor k _ hf a ha hl hdeg
  refine ⟨rows, cols, hr, hc, ?_⟩
  intro hz
  apply hdet
  rw [← eulerClosedForm_minor_map, hz, map_zero]

end
end CCDN
