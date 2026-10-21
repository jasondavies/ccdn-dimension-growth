/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Center.ProjectiveChowIncidence
public import CCDN.Hilbert.FilteredHilbertPolynomial
import CCDN.Center.ClosureNormalizationInfinite
import CCDN.Center.FixedCoordinateGenericNormalization
import CCDN.Center.HomogeneousProjectionNoBasePoint
import CCDN.Center.ProjectiveChowEquation
import CCDN.Center.ProjectiveIncidenceClosed

/-!
A finite normalization retaining X0 supplies a hyperplane tuple outside
projective incidence whose last hyperplane is X0=0. Consequently the degree
in its constant coefficient equals the entire last block degree.

A nonzero evaluation with only one active coordinate in a hyperplane
block identifies its separate degree with the degree in that coordinate.
-/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

private lemma chow_row_weight_eq_sum {r s : ℕ} (i : Fin r)
    (e : (Fin r × Fin s) →₀ ℕ) :
    Finsupp.weight (chowRowWeight i) e = ∑ j, e (i,j) := by
  classical
  rw [Finsupp.weight_eq_sum, Fintype.sum_prod_type]
  simp [chowRowWeight]

private theorem chow_row_degreeOf_le
    {K : Type*} [Field K] {r s : ℕ}
    (F : MvPolynomial (Fin r × Fin s) K) (i : Fin r) (j : Fin s) (d : ℕ)
    (hF : F.IsWeightedHomogeneous (chowRowWeight i) d) :
    F.degreeOf (i,j) ≤ d := by
  apply degreeOf_le_iff.mpr
  intro e he
  have hh := Finsupp.le_weight (chowRowWeight (s := s) i)
    (s := (i,j)) (by simp [chowRowWeight]) e
  exact hh.trans_eq (hF (mem_support_iff.mp he))

private theorem chow_row_degreeOf_eq_of_eval_ne_zero
    {K : Type*} [Field K] {r s : ℕ}
    (F : MvPolynomial (Fin r × Fin s) K) (i : Fin r) (j : Fin s) (d : ℕ)
    (hF : F.IsWeightedHomogeneous (chowRowWeight i) d)
    (u : Fin r × Fin s → K) (hu : ∀ k, k ≠ j → u (i,k) = 0)
    (hne : eval u F ≠ 0) : F.degreeOf (i,j) = d := by
  classical
  apply le_antisymm (chow_row_degreeOf_le F i j d hF)
  rw [F.as_sum, map_sum] at hne
  obtain ⟨e,he,hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  rw [eval_monomial] at hterm
  have hprod : ∀ q ∈ e.support, u q ^ e q ≠ 0 :=
    Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul hterm)
  have hother (k : Fin s) (hk : k ≠ j) : e (i,k) = 0 := by
    by_contra hz
    have hh := hprod (i,k) (Finsupp.mem_support_iff.mpr hz)
    rw [hu k hk, zero_pow hz] at hh
    exact hh rfl
  have hw : Finsupp.weight (chowRowWeight i) e = e (i,j) := by
    rw [chow_row_weight_eq_sum]
    exact Finset.sum_eq_single j (fun k _ hk => hother k hk)
      (fun h => False.elim (h (Finset.mem_univ j)))
  calc
    d = Finsupp.weight (chowRowWeight i) e := (hF (mem_support_iff.mp he)).symm
    _ = e (i,j) := hw
    _ ≤ F.degreeOf (i,j) := monomial_le_degreeOf (i,j) he

end
end CCDN

namespace CCDN
noncomputable section
open MvPolynomial

private theorem exists_hyperplane_axis_outside_closure_incidence
    {K : Type*} [Field K] [Infinite K] {m n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (hm : (filteredHilbertPolynomial I).natDegree = m) :
    ∃ U : Fin (m + 1) × Fin (n + 1) → K,
      U (Fin.last m,0) = 1 ∧ (∀ j, j ≠ 0 → U (Fin.last m,j) = 0) ∧
      U ∉ projectiveChowIncidenceLocus (m + 1) (projectiveClosureIdeal I) := by
  classical
  obtain ⟨_,_,hdim,_⟩ := filteredHilbertPolynomial_positive_multiplicity I
    (Ideal.IsPrime.ne_top ‹I.IsPrime›)
  have hmn : m ≤ n := by simpa only [hm,Fintype.card_fin] using hdim
  obtain ⟨a,ha,_,_,hint⟩ := exists_closure_normalization_infinite_of_le m n hmn I hm
  obtain ⟨c,hc⟩ := homogeneous_linear_forms_coefficient_representation a ha
  let U : Fin (m + 1) × Fin (n + 1) → K := fun q =>
    Fin.lastCases (Fin.cases 1 (fun _ => 0) q.2)
      (fun i => Fin.cases 0 (fun j => c (i,j)) q.2) q.1
  have hlast (x : Fin (n + 1) → K) : ∑ j, U (Fin.last m,j) * x j = x 0 := by
    simp only [U, Fin.lastCases_last]
    rw [Fin.sum_univ_succ]
    simp
  have hrow (i : Fin m) (x : Fin (n + 1) → K) :
      ∑ j, U (i.castSucc,j) * x j = eval x (rename Fin.succ (a i)) := by
    have he : a i = ∑ j, C (c (i,j)) * X j := (congrFun hc i).symm
    rw [he]
    simp only [U,Fin.lastCases_castSucc,Fin.sum_univ_succ,Fin.cases_zero,
      Fin.cases_succ,zero_mul,zero_add,map_sum,map_mul,rename_C,rename_X,eval_C,eval_X]
  refine ⟨U,by simp [U],?_,?_⟩
  · intro j
    refine Fin.cases (fun hj => (hj rfl).elim) (fun k _ => ?_) j
    simp [U]
  · intro hU
    obtain ⟨x,hx,hI,hrel⟩ := (projectiveChowIncidenceLocus_iff_cone
      (projectiveClosureIdeal I) (projectiveClosureIdeal_homogeneous I) U).mp hU
    apply hx
    apply homogeneous_integral_projection_zero_fiber (projectiveClosureIdeal I)
      (projectiveClosureIdeal_homogeneous I) (closureProjectionCoordinates a)
      (closureProjectionCoordinates_homogeneous a ha) hint x
    · intro f hf
      simpa only [aeval_eq_eval] using hI f hf
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · have hh := hrel (Fin.last m)
        rw [hlast] at hh
        simpa only [closureProjectionCoordinates,Fin.cons_zero,aeval_X] using hh
      · have hh := hrel j.castSucc
        rw [hrow] at hh
        simpa only [closureProjectionCoordinates,Fin.cons_succ,aeval_eq_eval] using hh

/-- Let `I` be a prime ideal over an algebraically closed field whose filtered Hilbert
polynomial has degree `m`, and let `F` generate the Chow incidence ideal with `m + 1` hyperplane
rows. If `F` is homogeneous of degree `d` in the last row of coefficients, then its degree in the
constant coefficient `(Fin.last m, 0)` of that row is exactly `d`. -/
theorem chow_generator_last_coordinate_degree
    {K : Type*} [Field K] [IsAlgClosed K] {m n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (hm : (filteredHilbertPolynomial I).natDegree = m)
    (F : MvPolynomial (Fin (m + 1) × Fin (n + 1)) K)
    (hgen : chowIncidenceIdeal (m + 1) I = Ideal.span {F})
    (d : ℕ) (hd : F.IsWeightedHomogeneous (chowRowWeight (Fin.last m)) d) :
    F.degreeOf (Fin.last m,0) = d := by
  obtain ⟨U,_,hU,hnot⟩ := exists_hyperplane_axis_outside_closure_incidence I hm
  have hne : eval U F ≠ 0 :=
    (chow_incidence_generator_eval_eq_zero_iff (m + 1) I F hgen U).not.mpr hnot
  exact chow_row_degreeOf_eq_of_eval_ne_zero F (Fin.last m) 0 d hd U hU hne

end
end CCDN
