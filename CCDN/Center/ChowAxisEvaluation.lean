/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Center.ChowIncidenceGrading
public import CCDN.Center.ProjectiveChowIncidence
public import CCDN.Hilbert.FilteredHilbertPolynomial
import CCDN.Center.ChowRowCoordinateDegree
import CCDN.Center.ClosureNormalizationInfinite
import CCDN.Center.FixedCoordinateGenericNormalization
import CCDN.Center.HomogeneousProjectionNoBasePoint
import CCDN.Center.ProjectiveChowEquation
import CCDN.Center.ProjectiveIncidenceClosed
/-! A finite normalization retaining X0 supplies a hyperplane tuple outside
projective incidence whose last hyperplane is X0=0. Consequently the degree
in its constant coefficient equals the entire last block degree. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

theorem exists_hyperplane_axis_outside_closure_incidence
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
