module

public import CCDN.Center.GenericPolynomialIndependence
public import CCDN.Center.ChowIncidenceNonzero
/-! Generic hyperplane evaluations retain the full number of independent
coordinates of the affine variety, together with their coefficient variables. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

theorem generic_linear_independence
    {K A : Type*} [Field K] [CommRing A] [IsDomain A] [Algebra K A]
    {m n : ℕ} (x : Fin n → A) (c : Fin m → Fin n)
    (hc : AlgebraicIndependent K (fun i => x (c i))) :
    AlgebraicIndependent K (Sum.elim
      (fun q : Fin (m + 1) × Fin n => (X q : MvPolynomial (Fin (m + 1) × Fin n) A))
      (fun i : Fin m => -(∑ j, X (i.castSucc,j) * C (x j)))) := by
  classical
  let a : Fin (m + 1) × Fin n → K := fun q =>
    Fin.lastCases 0 (fun i => if q.2 = c i then -1 else 0) q.1
  apply generic_polynomial_independence _ a
  have he (i : Fin m) :
      eval (fun q => algebraMap K A (a q))
        (-(∑ j, X (i.castSucc,j) * C (x j))) = x (c i) := by
    simp [a,apply_ite,ite_mul]
  simpa only [he] using hc

def chowIndependentVariables (m n : ℕ) :
    ((Fin (m + 1) × Fin n) ⊕ Fin m) → Fin (m + 1) × Fin (n + 1) :=
  Sum.elim (fun q => (q.1,q.2.succ)) (fun i => (i.castSucc,0))

theorem chowIncidence_independent_coordinates {K : Type*} [Field K] {m n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (hm : (filteredHilbertPolynomial I).natDegree = m) :
    AlgebraicIndependent K (fun q =>
      chowIncidenceMap (m + 1) I (X (chowIndependentVariables m n q))) := by
  classical
  obtain ⟨U,hU,hAI⟩ := exists_hilbert_dimension_independent_coordinates I
    (Ideal.IsPrime.ne_top ‹I.IsPrime›)
  have hcard : Fintype.card U = m := by
    simpa only [Nat.card_eq_fintype_card,hm] using hU
  let e : Fin m ≃ U := (Fintype.equivFinOfCardEq hcard).symm
  have hi : AlgebraicIndependent K (fun i : Fin m =>
      (Ideal.Quotient.mk I) (X (e i).val)) := hAI.comp e e.injective
  have hg := generic_linear_independence
    (fun j => (Ideal.Quotient.mk I) (X j)) (fun i => (e i).val) hi
  convert hg using 1
  funext q
  cases q <;> simp [chowIndependentVariables,chowIncidenceMap]

end
end CCDN
