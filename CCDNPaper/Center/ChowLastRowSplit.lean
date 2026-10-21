/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDNPaper.Center.ChowIncidenceMinimalPolynomial

/-! Split off the final hyperplane's free coefficients from the
Chow incidence coordinate ring. This is a polynomial-ring isomorphism,
not a specialization. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

local instance chowFirstPolynomialRing {K σ τ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) :
    CommRing (MvPolynomial τ (MvPolynomial σ K ⧸ I)) := by
  letI : CommRing (MvPolynomial σ K ⧸ I) := inferInstance
  infer_instance

local instance chowNestedPolynomialRing {K σ τ υ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) :
    CommRing (MvPolynomial υ (MvPolynomial τ (MvPolynomial σ K ⧸ I))) := by
  let : CommRing (MvPolynomial τ (MvPolynomial σ K ⧸ I)) := inferInstance
  infer_instance

/-- The equivalence splitting the index set `Fin (m + 1) × Fin n` into the indices of the last
row and the indices of the first `m` rows. -/
def chowLastRowVariables (m n : ℕ) :
    (Fin (m + 1) × Fin n) ≃ (Fin n ⊕ (Fin m × Fin n)) where
  toFun q := Fin.lastCases (Sum.inl q.2) (fun i => Sum.inr (i,q.2)) q.1
  invFun q := q.elim (fun j => (Fin.last m,j)) (fun q => (q.1.castSucc,q.2))
  left_inv q := by
    rcases q with ⟨i,j⟩
    exact Fin.lastCases (by simp) (fun k => by simp) i
  right_inv q := by cases q <;> simp

/-- The isomorphism of the Chow incidence coordinate ring of `m + 1` hyperplanes with polynomials
in the free coefficients of the last hyperplane over the polynomial ring in those of the first
`m` hyperplanes. -/
def chowLastRowSplit {K : Type*} [Field K] {n : ℕ} (m : ℕ)
    (I : Ideal (MvPolynomial (Fin n) K)) :
    ChowIncidenceCoordinateRing m I ≃ₐ[MvPolynomial (Fin n) K ⧸ I]
      MvPolynomial (Fin n) (MvPolynomial (Fin m × Fin n) (MvPolynomial (Fin n) K ⧸ I)) :=
  (renameEquiv _ (chowLastRowVariables m n)).trans (sumAlgEquiv _ _ _)

/-- `chowLastRowSplit` sends a free coefficient of the last hyperplane to the corresponding outer
variable. -/
@[simp] lemma chowLastRowSplit_X_last {K : Type*} [Field K] {m n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) (j : Fin n) :
    chowLastRowSplit m I (X (Fin.last m,j)) = X j := by
  simp [chowLastRowSplit,chowLastRowVariables]

/-- `chowLastRowSplit` sends a free coefficient of one of the first `m` hyperplanes to the
corresponding inner variable, as a constant outer polynomial. -/
@[simp] lemma chowLastRowSplit_X_first {K : Type*} [Field K] {m n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) (i : Fin m) (j : Fin n) :
    chowLastRowSplit m I (X (i.castSucc,j)) = C (X (i,j)) := by
  simp [chowLastRowSplit,chowLastRowVariables]

/-- `chowLastRowSplit` sends a constant of the coordinate ring `K[X]/I` to the doubly constant
polynomial. -/
@[simp] lemma chowLastRowSplit_C {K : Type*} [Field K] {m n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) (a : MvPolynomial (Fin n) K ⧸ I) :
    chowLastRowSplit m I (C a) = C (C a) := by
  simp [chowLastRowSplit]

/-- Under `chowLastRowSplit`, the incidence-substituted constant coefficient of the last
hyperplane becomes `-∑ j, X j * x_j` in the outer variables, where `x_j` are the coordinate
functions of `I`. -/
lemma chowLastRowSplit_incidence_last {K : Type*} [Field K] {m n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) :
    chowLastRowSplit m I (chowIncidenceMap (m + 1) I (X (Fin.last m,0))) =
      -(∑ j : Fin n, X j * C (C (Ideal.Quotient.mk I (X j)))) := by
  simp [chowIncidenceMap]

/-- Under `chowLastRowSplit`, the incidence-substituted constant coefficient of one of the first
`m` hyperplanes becomes the constant outer polynomial given by the incidence substitution for
`m` hyperplanes. -/
lemma chowLastRowSplit_incidence_first {K : Type*} [Field K] {m n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) (i : Fin m) :
    chowLastRowSplit m I (chowIncidenceMap (m + 1) I (X (i.castSucc,0))) =
      C (chowIncidenceMap m I (X (i,0))) := by
  classical
  simp only [chowIncidenceMap,aeval_X,Fin.cases_zero]
  rw [map_neg,map_sum]
  have hC : C (-∑ j : Fin n, X (i,j) * C (Ideal.Quotient.mk I (X j))) =
      -(∑ j : Fin n, (C (X (i,j)) : MvPolynomial (Fin n)
        (MvPolynomial (Fin m × Fin n) (MvPolynomial (Fin n) K ⧸ I))) *
        C (C (Ideal.Quotient.mk I (X j)))) := by
    let φ : MvPolynomial (Fin m × Fin n) (MvPolynomial (Fin n) K ⧸ I) →+*
      MvPolynomial (Fin n) (MvPolynomial (Fin m × Fin n) (MvPolynomial (Fin n) K ⧸ I)) := C
    change φ _ = _
    rw [φ.map_neg]
    change -(φ.toAddMonoidHom (∑ j : Fin n, X (i,j) * C (Ideal.Quotient.mk I (X j)))) = _
    rw [map_sum]
    congr 1
    exact Finset.sum_congr rfl (fun j _ => φ.map_mul _ _)
  rw [hC]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [map_mul,chowLastRowSplit_X_first,chowLastRowSplit_C]

end
end CCDN
