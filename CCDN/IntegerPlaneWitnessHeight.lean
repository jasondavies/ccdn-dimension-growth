module

public import CCDN.IntegerPlaneHeight
public import CCDN.IntegerPlaneWitness
public import CCDN.ClosedFormMinorCharge

/-! Explicit height estimates for the evaluated universal bad-prime witness. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

lemma universalPlaneBadWitness_eval {σ : Type*}
    (f : MvPolynomial σ ℤ)
    (rows : Fin (2 * f.totalDegree ^ 2 - 1) → ℕ × ℕ)
    (cols : Fin (2 * f.totalDegree ^ 2 - 1) → ClosedFormColumns f.totalDegree)
    (v : PlaneParameters σ → ℤ) :
    eval v (universalPlaneBadWitness f rows cols) =
      ((universalPlaneSection f v).coeff f.totalDegree).coeff 0 *
        ((closedFormCoefficientMatrix f.totalDegree (universalPlaneSection f v)).submatrix rows cols).det := by
  rw [universalPlaneBadWitness, map_mul, closedForm_minor_map]
  congr 1
  exact (bivariateMap_coeff (eval v) (universalPlanePolynomial f) f.totalDegree 0).symm

/-- The evaluated witness is a leading coefficient times an actual integer
minor; both are controlled by the height of the same plane section. -/
theorem universalPlaneBadWitness_eval_log_bound {σ : Type*} [Fintype σ]
    (f : MvPolynomial σ ℤ) (hd : 1 ≤ f.totalDegree)
    (rows : Fin (2 * f.totalDegree ^ 2 - 1) → ℕ × ℕ)
    (cols : Fin (2 * f.totalDegree ^ 2 - 1) → ClosedFormColumns f.totalDegree)
    (v : PlaneParameters σ → ℤ) (S : ℝ) (hS : 1 ≤ S)
    (hf : BivariateCoefficientBound (universalPlaneSection f v) S)
    (hw : eval v (universalPlaneBadWitness f rows cols) ≠ 0) :
    Real.log |(eval v (universalPlaneBadWitness f rows cols) : ℝ)| ≤
      Real.log S + (27 * (f.totalDegree : ℝ) ^ 4) *
        (1 + Real.log S / (f.totalDegree : ℝ) ^ 2) := by
  let g := universalPlaneSection f v
  let c := (g.coeff f.totalDegree).coeff 0
  let D := ((closedFormCoefficientMatrix f.totalDegree g).submatrix rows cols).det
  have he : eval v (universalPlaneBadWitness f rows cols) = c * D :=
    universalPlaneBadWitness_eval f rows cols v
  have hc : c ≠ 0 := fun h => hw (by rw [he, h, zero_mul])
  have hD : D ≠ 0 := fun h => hw (by rw [he, h, mul_zero])
  have ht : bivariateTotalDegree g ≤ f.totalDegree :=
    universalPlanePolynomial_specialization_totalDegree f (eval v)
  have hb := closedForm_minor_log_height f.totalDegree (2 * f.totalDegree ^ 2 - 1)
    hd (Nat.sub_le _ _) g S hS hf
    ((bivariate_natDegree_le_totalDegree g).trans ht)
    (fun i => (bivariate_coefficient_natDegree_le_totalDegree g i).trans ht) rows cols hD
  have hl := Real.log_le_log (abs_pos.mpr (Int.cast_ne_zero.mpr hc)) (hf f.totalDegree 0)
  rw [he, Int.cast_mul, abs_mul, Real.log_mul
    (abs_ne_zero.mpr (Int.cast_ne_zero.mpr hc)) (abs_ne_zero.mpr (Int.cast_ne_zero.mpr hD))]
  exact add_le_add hl hb

end
end CCDN
