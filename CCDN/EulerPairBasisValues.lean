module

public import CCDN.EulerPairBasis
public import CCDN.FiniteRowMinor

/-! Explicit monomial values of the Euler basis and nonzero minors of the
correct Noether order d^2-1. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Module

lemma euler_restrict_basis_val {R : Type*} [CommRing R]
    (S : Set (Fin 2 →₀ ℕ)) (i : S) :
    (basisRestrictSupport R S i).val = monomial i.val 1 := by
  classical
  change AddMonoidAlgebra.ofCoeff
    (((Finsupp.supportedEquivFinsupp (M := R) (R := R) S).symm
      (Finsupp.single i 1)).val) = _
  rw [Finsupp.supportedEquivFinsupp_symm_single]
  rfl

lemma eulerLowBasis_apply {R : Type*} [CommRing R] (k : ℕ) (i : EulerLowIndex k) :
    (eulerLowBasis R k i).val =
      monomial ((boundedExponentEquivSym (Fin 2) k).symm i).val 1 := by
  classical
  unfold eulerLowBasis
  erw [Basis.reindex_apply]
  exact euler_restrict_basis_val _ _

lemma eulerTopBasis_apply {R : Type*} [CommRing R] (k : ℕ) (i : EulerTopIndex k) :
    (eulerTopBasis R k i).val =
      monomial ((exactExponentEquivSym (Fin 2) k).symm i).val 1 := by
  classical
  unfold eulerTopBasis
  erw [Basis.map_apply, Basis.reindex_apply]
  erw [LinearEquiv.coe_ofEq_apply]
  exact euler_restrict_basis_val _ _

theorem eulerClosedFormCoefficientMatrix_rank
    {F : Type*} [Field F] [CharZero F] [IsAlgClosed F]
    (k : ℕ) (f : Polynomial (Polynomial F)) (hf : Irreducible f)
    (a : F) (ha : a ≠ 0) (hl : f.leadingCoeff = Polynomial.C a)
    (hdeg : f.natDegree = k + 2) :
    (eulerClosedFormCoefficientMatrix k f).rank = (k + 2) ^ 2 - 1 := by
  have hi := eulerClosedFormCoefficientMatrix_columns_independent k f hf a ha hl hdeg
  have hr : (eulerClosedFormCoefficientMatrix k f).rank = Fintype.card (EulerColumns k) := by
    rw [Matrix.rank_eq_finrank_span_cols, linearIndependent_iff_card_eq_finrank_span.mp hi,
      Set.finrank]
  rw [hr, card_eulerColumns]

/-- A nonzero maximal minor has precisely the universal Noether
order d^2-1. -/
theorem exists_eulerClosedForm_nonzero_minor
    {F : Type*} [Field F] [CharZero F] [IsAlgClosed F]
    (k : ℕ) (f : Polynomial (Polynomial F)) (hf : Irreducible f)
    (a : F) (ha : a ≠ 0) (hl : f.leadingCoeff = Polynomial.C a)
    (hdeg : f.natDegree = k + 2) :
    ∃ (rows : Fin ((k + 2) ^ 2 - 1) → ℕ × ℕ)
      (cols : Fin ((k + 2) ^ 2 - 1) → EulerColumns k),
      Function.Injective rows ∧ Function.Injective cols ∧
      ((eulerClosedFormCoefficientMatrix k f).submatrix rows cols).det ≠ 0 := by
  exact exists_nonzero_minor_of_rank_le _ _
    (eulerClosedFormCoefficientMatrix_rank k f hf a ha hl hdeg).ge

end
end CCDN
