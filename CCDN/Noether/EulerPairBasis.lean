/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Noether.EulerClosedFormRank
public import CCDN.Algebra.HomogeneousMonomials
public import CCDN.ForMathlib.MvPolynomial
/-! Canonical monomial coordinates for the d^2-1 Euler parameters and the
coefficient matrix of their closed-form operator. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Module

abbrev EulerLowIndex (k : ℕ) := Sym (Option (Fin 2)) k
abbrev EulerTopIndex (k : ℕ) := Sym (Fin 2) k
abbrev EulerColumns (k : ℕ) := EulerLowIndex k ⊕ (EulerLowIndex k ⊕ EulerTopIndex k)

/-- The usual monomial basis of the total-degree-at-most space. -/
def eulerLowBasis (R : Type*) [CommRing R] (k : ℕ) :
    Basis (EulerLowIndex k) R (restrictTotalDegree (Fin 2) R k) := by
  classical
  exact (basisRestrictSupport R {p : Fin 2 →₀ ℕ | p.degree ≤ k}).reindex
    (Finsupp.degreeLeEquivSym (Fin 2) k)

/-- The usual monomial basis of the homogeneous space. -/
def eulerTopBasis (R : Type*) [CommRing R] (k : ℕ) :
    Basis (EulerTopIndex k) R (homogeneousSubmodule (Fin 2) R k) := by
  classical
  let e : restrictSupport R {p : Fin 2 →₀ ℕ | p.degree = k} ≃ₗ[R]
      homogeneousSubmodule (Fin 2) R k :=
    LinearEquiv.ofEq _ _ (homogeneousSubmodule_eq_finsupp_supported (Fin 2) R k).symm
  exact ((basisRestrictSupport R {p : Fin 2 →₀ ℕ | p.degree = k}).reindex
    (degreeEqEquivSym (Fin 2) k)).map e


/-- Thus every basis vector is either a single low monomial or one radial
syzygy pair (yQ,-xQ); no coefficient-dependent basis is chosen. -/
def eulerPairBasis (R : Type*) [CommRing R] (k : ℕ) :
    Basis (EulerColumns k) R (EulerPairSpace R k) :=
  (eulerLowBasis R k).prod ((eulerLowBasis R k).prod (eulerTopBasis R k))

theorem card_eulerColumns (k : ℕ) : Fintype.card (EulerColumns k) = (k + 2) ^ 2 - 1 := by
  rw [← Module.finrank_eq_card_basis (eulerPairBasis ℚ k), finrank_eulerPairSpace]

/-- The equation's coefficients enter the matrix linearly. The column set
has cardinality d^2-1, and rows are ordinary coefficient positions. -/
def eulerClosedFormCoefficientMatrix {R : Type*} [CommRing R] (k : ℕ)
    (f : Polynomial (Polynomial R)) : Matrix (ℕ × ℕ) (EulerColumns k) R :=
  fun i j => ((eulerClosedFormOperator k f (eulerPairBasis R k j)).coeff i.1).coeff i.2

/-- Linear independence of all d^2-1 coefficient columns for an
irreducible equation with constant outer leading coefficient. -/
theorem eulerClosedFormCoefficientMatrix_columns_independent
    {F : Type*} [Field F] [CharZero F] [IsAlgClosed F]
    (k : ℕ) (f : Polynomial (Polynomial F)) (hf : Irreducible f)
    (a : F) (ha : a ≠ 0) (hl : f.leadingCoeff = Polynomial.C a)
    (hdeg : f.natDegree = k + 2) :
    LinearIndependent F (eulerClosedFormCoefficientMatrix k f).col := by
  have hi := eulerClosedFormOperator_injective_of_constant_leading k f hf a ha hl hdeg
  have h := ((eulerPairBasis F k).linearIndependent.map' (eulerClosedFormOperator k f)
    (LinearMap.ker_eq_bot.mpr hi)).map' (bivariateCoefficients F)
      (LinearMap.ker_eq_bot.mpr bivariateCoefficients_injective)
  exact h

end
end CCDN
