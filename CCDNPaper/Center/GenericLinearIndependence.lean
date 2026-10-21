/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Hilbert.FilteredHilbertPolynomial
public import CCDNPaper.Center.ChowIncidenceIdeal
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
import CCDN.Hilbert.CoordinateIndependence
import CCDNPaper.Center.GenericPolynomialIndependence

/-! Generic hyperplane evaluations retain the full number of independent
coordinates of the affine variety, together with their coefficient variables. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

private theorem generic_linear_independence
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

/-- The hyperplane coefficient indices consisting of all nonconstant coefficients of `m + 1`
hyperplanes together with the constant coefficients of the first `m` hyperplanes. -/
def chowIndependentVariables (m n : ℕ) :
    ((Fin (m + 1) × Fin n) ⊕ Fin m) → Fin (m + 1) × Fin (n + 1) :=
  Sum.elim (fun q => (q.1,q.2.succ)) (fun i => (i.castSucc,0))

/-- If the affine variety of the prime ideal `I` has dimension `m`, then under the incidence
substitution for `m + 1` hyperplanes, the images of the coefficient variables indexed by
`chowIndependentVariables m n` are algebraically independent over `K`. -/
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
