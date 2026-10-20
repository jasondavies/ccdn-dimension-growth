module

public import CCDN.FiniteRowMinor
public import CCDN.ChowLinearSpecialization
public import Mathlib.Data.Fin.Embedding
public import CCDN.PolynomialPredicates

/-! The literal center projection from Section 5: its coordinates are the
maximal minors obtained by adjoining the point as the first row of a center
matrix. Its kernel is exactly the span of the independent center rows, and
its linear coefficients are signed Plücker coordinates of that center. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Matrix

def centerMinorProjection {K : Type*} [Field K] {r n : ℕ}
    (A : Matrix (Fin r) (Fin n) K) (x : Fin n → K) (c : Fin (r + 1) ↪ Fin n) : K :=
  (Matrix.submatrix (Fin.cons x (fun i j => A i j)) id c).det

/-- Laplace expansion gives the linear coordinate of the center map. -/
def centerMinorProjectionForm {K : Type*} [Field K] {r n : ℕ}
    (A : Matrix (Fin r) (Fin n) K) (c : Fin (r + 1) ↪ Fin n) : MvPolynomial (Fin n) K :=
  ∑ j : Fin (r + 1), C ((-1 : K) ^ (j : ℕ) * (A.submatrix id (j.succAboveEmb.trans c)).det) * X (c j)

lemma centerMinorProjectionForm_homogeneous {K : Type*} [Field K] {r n : ℕ}
    (A : Matrix (Fin r) (Fin n) K) (c : Fin (r + 1) ↪ Fin n) :
    (centerMinorProjectionForm A c).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ (fun j _ => isHomogeneous_C_mul_X _ (c j))

lemma centerMinorProjectionForm_eval {K : Type*} [Field K] {r n : ℕ}
    (A : Matrix (Fin r) (Fin n) K) (c : Fin (r + 1) ↪ Fin n) (x : Fin n → K) :
    eval x (centerMinorProjectionForm A c) = centerMinorProjection A x c := by
  classical
  rw [centerMinorProjection, Matrix.det_succ_row_zero]
  simp only [centerMinorProjectionForm, map_sum, map_mul, eval_C, eval_X]
  apply Finset.sum_congr rfl
  intro j _
  have he : Matrix.submatrix (Matrix.submatrix (Fin.cons x (fun i j => A i j)) id c)
      Fin.succ j.succAbove = A.submatrix id (j.succAboveEmb.trans c) := by
    ext a b
    change (Fin.cons x (fun i j => A i j) : Fin (r + 1) → Fin n → K) a.succ (c (j.succAbove b)) = A a (c (j.succAbove b))
    rw [Fin.cons_succ]
  rw [he]
  change (-1 : K) ^ (j : ℕ) * _ * x (c j) = (-1 : K) ^ (j : ℕ) * x (c j) * _
  ring

/-- Vanishing of every projection coordinate is exactly membership in
the center; no generic-position or matrix-rank condition is supplied beyond
independence of the rows defining that center. -/
theorem centerMinorProjection_eq_zero_iff {K : Type*} [Field K] {r n : ℕ}
    (A : Matrix (Fin r) (Fin n) K) (hA : LinearIndependent K A.row) (x : Fin n → K) :
    centerMinorProjection A x = 0 ↔ x ∈ Submodule.span K (Set.range A.row) := by
  classical
  constructor
  · intro hz
    by_contra hx
    have hi : LinearIndependent K (Fin.cons x (fun i j => A i j) : Fin (r + 1) → (Fin n → K)) :=
      linearIndependent_finCons.mpr ⟨hA, hx⟩
    obtain ⟨c, hc, hdet⟩ := exists_nonzero_minor_of_independent_rows (Fin.cons x (fun i j => A i j)) hi
    exact hdet (congrFun hz ⟨c, hc⟩)
  · intro hx
    funext c
    change (Matrix.submatrix (Fin.cons x (fun i j => A i j)) id c).det = 0
    apply Matrix.det_eq_zero_of_not_linearIndependent_rows
    intro hi
    have hh : LinearIndependent K (Fin.cons x (fun i j => A i j) : Fin (r + 1) → (Fin n → K)) :=
      LinearIndependent.of_comp (LinearMap.funLeft K K c) hi
    exact (linearIndependent_finCons.mp hh).2 hx

/-- One coefficient, as a degree-one polynomial in Plücker variables. -/
def centerPluckerCoefficient {K : Type*} [Field K] {r n : ℕ}
    (c : Fin (r + 1) ↪ Fin n) (k : Fin n) : MvPolynomial (Fin r ↪ Fin n) K :=
  ∑ j : Fin (r + 1), if c j = k then C ((-1 : K) ^ (j : ℕ)) * X (j.succAboveEmb.trans c) else 0

lemma centerPluckerCoefficient_homogeneous {K : Type*} [Field K] {r n : ℕ}
    (c : Fin (r + 1) ↪ Fin n) (k : Fin n) :
    (centerPluckerCoefficient (K := K) c k).IsHomogeneous 1 := by
  classical
  apply IsHomogeneous.sum
  intro j _
  split_ifs
  · exact isHomogeneous_C_mul_X _ _
  · exact isHomogeneous_zero _ K 1

/-- The matrix entries of the projection are linear expressions in the
maximal minors of the center rows, exactly as in the source's Plücker map. -/
theorem centerMinorProjectionForm_eq_plucker_coefficients
    {K : Type*} [Field K] {r n : ℕ}
    (A : Matrix (Fin r) (Fin n) K) (c : Fin (r + 1) ↪ Fin n) :
    centerMinorProjectionForm A c =
      ∑ k, C (eval (fun e : Fin r ↪ Fin n => (A.submatrix id e).det)
        (centerPluckerCoefficient c k)) * X k := by
  classical
  simp only [centerMinorProjectionForm, centerPluckerCoefficient, map_sum,
    apply_ite, map_mul, eval_C, eval_X, map_zero, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp

/-- The literal maximal-minor projection is finite on a homogeneous source
whenever the center rows span a projective plane disjoint from that source. -/
theorem centerMinorProjection_integral_of_disjoint
    {K : Type*} [Field K] [IsAlgClosed K] {r n : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hJ : IsHomogeneousIdeal J)
    (A : Matrix (Fin r) (Fin (n + 1)) K) (hA : LinearIndependent K A.row)
    (hcenter : ∀ p ∈ projectiveIdealZeroLocus J,
      p.rep ∉ Submodule.span K (Set.range A.row)) :
    (projectionCoordinateMap J (centerMinorProjectionForm A)).IsIntegral := by
  classical
  apply integral_projection_of_homogeneous_origin_fiber (L := K) J hJ _
    (centerMinorProjectionForm_homogeneous A)
  intro x hx
  by_contra hx0
  have hxJ : ∀ f ∈ J, eval x f = 0 := fun f hf => hx f (Ideal.mem_sup_left hf)
  have hz : centerMinorProjection A x = 0 := by
    funext c
    rw [← centerMinorProjectionForm_eval]
    exact hx _ (Ideal.mem_sup_right (Ideal.subset_span ⟨c, rfl⟩))
  have hspan := (centerMinorProjection_eq_zero_iff A hA x).mp hz
  let p := Projectivization.mk K x hx0
  have hp : p ∈ projectiveIdealZeroLocus J := by
    intro v hv he f hf
    conv_lhs => rw [← sum_homogeneousComponent f]
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro M _
    exact (homogeneous_eval_zero_iff_projective_eq
      (homogeneousComponent_isHomogeneous M f) hv hx0 he).mpr (hxJ _ (hJ f hf M))
  apply hcenter p hp
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' K p.rep x p.rep_nonzero hx0).mp p.mk_rep
  rw [← ha]
  exact Submodule.smul_mem _ a hspan

end
end CCDN
