/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Auxiliary.AuxiliaryNonmultiple
public import CCDN.Determinant.HeightDeterminant
public import CCDN.Height.IntegerCoefficientHeight
public import CCDN.Height.CountingHypotheses
import CCDN.Auxiliary.PlaneAuxiliaryDegree
import CCDN.Auxiliary.PlaneAuxiliaryLargeHeight
import CCDN.Auxiliary.PlaneAuxiliarySelection
import CCDN.Determinant.PolynomialMapDeterminant
/-! Auxiliary nonmultiples and explicit degree choices for polynomial images
of the original integer plane curve. Sharp finite-field counts remain explicit. -/

@[expose] public section
namespace CCDN
noncomputable section

theorem polynomial_map_exists_auxiliary_small_height
    {F : Type*} [Field F] [CharZero F] [IsAlgClosed F] {d M t : ℕ}
    (order : MonomialOrder (Fin 3)) (f : MvPolynomial (Fin 3) ℤ)
    (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) (hd : 0 < d) (hdM : d ≤ M)
    {q : MvPolynomial (Fin 2) ℤ} {H : ℝ} (hq : IsBoundedPlaneCurve F q d H)
    (τ : Fin 3 → MvPolynomial (Fin 2) ℤ)
    (z : Fin t → Fin 2 → ℤ) (hz : ∀ i, MvPolynomial.eval (z i) q = 0)
    {B C : ℝ} (himage : IsBoxZeroFamily f B (fun i j => MvPolynomial.eval (z i) (τ j)))
    (hC : 0 ≤ C)
    (hML : Real.log B ≤ M)
    (hheight : Real.log |((order.leadingCoeff f : ℤ) : ℝ)| ≤ 4 * d * Real.log B)
    (hthreshold : 2 * Real.exp (heightDeterminantError C + 23) * (d : ℝ) ^ 3 *
      (1 + Real.log H / (d : ℝ) ^ 2) * B ^ (2 / (d : ℝ)) /
        |((order.leadingCoeff f : ℤ) : ℝ)| ^ (1 / (d : ℝ) ^ 2) < M)
    (hcount : PlaneResidueCountBound C d q) :
    ∃ g, IsPointAuxiliary f g M (fun i j => MvPolynomial.eval (z i) (τ j)) := by
  classical
  by_contra hnone
  obtain ⟨s, _, _, hr, hc⟩ := polynomial_map_no_auxiliary_height_comparison
    order f hf hf0 hd hdM hq τ z hz himage hC (dvd_of_not_exists_isPointAuxiliary hnone) hcount
  have hH := hq.one_le_height
  have hB := himage.one_le_radius
  have hL : 1 ≤ |((order.leadingCoeff f : ℤ) : ℝ)| := by
    exact_mod_cast Int.one_le_abs (order.leadingCoeff_ne_zero_iff.mpr hf0)
  have hlog := plane_auxiliary_log_degree_bound hd hdM hr hB hL hML hheight hc
  have hA : 0 < 1 + Real.log H / (d : ℝ) ^ 2 := by
    have := Real.log_nonneg hH
    positivity
  have hbound := plane_degree_bound_of_log_bound hd (lt_of_lt_of_le hd hdM)
    (by linarith) (by linarith) hA hlog
  exact (not_lt_of_ge hbound) hthreshold


theorem polynomial_map_exists_auxiliary_large_height
    {F : Type*} [Field F] [CharZero F] [IsAlgClosed F] {d M t : ℕ}
    (order : MonomialOrder (Fin 3)) (f : MvPolynomial (Fin 3) ℤ)
    (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) (hd : 0 < d) (hMlarge : 32 * d ≤ M)
    {q : MvPolynomial (Fin 2) ℤ} {H : ℝ} (hq : IsBoundedPlaneCurve F q d H)
    (τ : Fin 3 → MvPolynomial (Fin 2) ℤ)
    (z : Fin t → Fin 2 → ℤ) (hz : ∀ i, MvPolynomial.eval (z i) q = 0)
    {B C : ℝ} (himage : IsBoxZeroFamily f B (fun i j => MvPolynomial.eval (z i) (τ j)))
    (hC : 0 ≤ C)
    (T : ℝ) (hT : 0 ≤ T)
    (hheight : 4 * d * Real.log B ≤ Real.log H)
    (hposition : Real.log H ≤ Real.log |((order.leadingCoeff f : ℤ) : ℝ)| + T * (d : ℝ) ^ 2)
    (hthreshold : 8 * Real.exp (heightDeterminantError C + 6 + T) * (d : ℝ) ^ 3 < M)
    (hcount : PlaneResidueCountBound C d q) :
    ∃ g, IsPointAuxiliary f g M (fun i j => MvPolynomial.eval (z i) (τ j)) := by
  classical
  have hdM : d ≤ M := by omega
  by_contra hnone
  obtain ⟨s, _, _, hr, hc⟩ := polynomial_map_no_auxiliary_height_comparison
    order f hf hf0 hd hdM hq τ z hz himage hC (dvd_of_not_exists_isPointAuxiliary hnone) hcount
  have hH := hq.one_le_height
  have hB := himage.one_le_radius
  have hL : 1 ≤ |((order.leadingCoeff f : ℤ) : ℝ)| := by
    exact_mod_cast Int.one_le_abs (order.leadingCoeff_ne_zero_iff.mpr hf0)
  have hlog := plane_auxiliary_large_height_log_bound hd hMlarge hr hB hL hH hT
    hheight hposition hc
  have hbound := plane_large_degree_bound_of_log_bound hd (lt_of_lt_of_le hd hdM) hlog
  exact (not_lt_of_ge hbound) hthreshold


theorem polynomial_map_auxiliary_small_height_degree
    {F : Type*} [Field F] [CharZero F] [IsAlgClosed F] {d t : ℕ}
    (order : MonomialOrder (Fin 3)) (f : MvPolynomial (Fin 3) ℤ)
    (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) (hd : 0 < d)
    {q : MvPolynomial (Fin 2) ℤ} {H : ℝ} (hq : IsBoundedPlaneCurve F q d H)
    (τ : Fin 3 → MvPolynomial (Fin 2) ℤ)
    (z : Fin t → Fin 2 → ℤ) (hz : ∀ i, MvPolynomial.eval (z i) q = 0)
    {B C : ℝ} (himage : IsBoxZeroFamily f B (fun i j => MvPolynomial.eval (z i) (τ j)))
    (hC : 0 ≤ C)
    (hheight : Real.log |((order.leadingCoeff f : ℤ) : ℝ)| ≤ 4 * d * Real.log B)
    (hcount : PlaneResidueCountBound C d q) :
    ∃ M : ℕ, (M : ℝ) ≤ d + Real.log B +
      2 * Real.exp (heightDeterminantError C + 23) * (d : ℝ) ^ 3 *
        (1 + Real.log H / (d : ℝ) ^ 2) * B ^ (2 / (d : ℝ)) /
          |((order.leadingCoeff f : ℤ) : ℝ)| ^ (1 / (d : ℝ) ^ 2) + 2 ∧
      ∃ g, IsPointAuxiliary f g M (fun i j => MvPolynomial.eval (z i) (τ j)) := by
  let R := 2 * Real.exp (heightDeterminantError C + 23) * (d : ℝ) ^ 3 *
    (1 + Real.log H / (d : ℝ) ^ 2) * B ^ (2 / (d : ℝ)) /
      |((order.leadingCoeff f : ℤ) : ℝ)| ^ (1 / (d : ℝ) ^ 2)
  have hB := himage.one_le_radius
  have hR : 0 ≤ R := by
    have := Real.log_nonneg hq.one_le_height
    have hB0 : 0 ≤ B := by linarith
    dsimp only [R]
    positivity
  obtain ⟨M, hdM, hML, hth, hM⟩ := auxiliary_integer_degree_selection d (Real.log_nonneg hB) hR
  refine ⟨M, hM, ?_⟩
  exact polynomial_map_exists_auxiliary_small_height order f hf hf0 hd hdM hq τ z hz himage hC
    hML hheight hth hcount


theorem polynomial_map_auxiliary_large_height_degree
    {F : Type*} [Field F] [CharZero F] [IsAlgClosed F] {d t : ℕ}
    (order : MonomialOrder (Fin 3)) (f : MvPolynomial (Fin 3) ℤ)
    (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) (hd : 0 < d)
    {q : MvPolynomial (Fin 2) ℤ} {H : ℝ} (hq : IsBoundedPlaneCurve F q d H)
    (τ : Fin 3 → MvPolynomial (Fin 2) ℤ)
    (z : Fin t → Fin 2 → ℤ) (hz : ∀ i, MvPolynomial.eval (z i) q = 0)
    {B C : ℝ} (himage : IsBoxZeroFamily f B (fun i j => MvPolynomial.eval (z i) (τ j)))
    (hC : 0 ≤ C)
    (T : ℝ) (hT : 0 ≤ T)
    (hheight : 4 * d * Real.log B ≤ Real.log H)
    (hposition : Real.log H ≤ Real.log |((order.leadingCoeff f : ℤ) : ℝ)| + T * (d : ℝ) ^ 2)
    (hcount : PlaneResidueCountBound C d q) :
    ∃ M : ℕ, (M : ℝ) ≤ (34 + 8 * Real.exp (heightDeterminantError C + 6 + T)) * (d : ℝ) ^ 3 ∧
      ∃ g, IsPointAuxiliary f g M (fun i j => MvPolynomial.eval (z i) (τ j)) := by
  let R := 8 * Real.exp (heightDeterminantError C + 6 + T) * (d : ℝ) ^ 3
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  obtain ⟨M, hMlarge, _, hth, hM⟩ := auxiliary_integer_degree_selection (32 * d)
    (show (0 : ℝ) ≤ 0 from le_rfl) hR
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd3 : (d : ℝ) ≤ (d : ℝ) ^ 3 := by nlinarith [sq_nonneg ((d : ℝ) - 1)]
  have hd31 : (1 : ℝ) ≤ (d : ℝ) ^ 3 := le_trans hd1 hd3
  refine ⟨M, ?_, ?_⟩
  · dsimp only [R] at hM
    push_cast at hM
    nlinarith
  · exact polynomial_map_exists_auxiliary_large_height order f hf hf0 hd hMlarge hq τ z hz
      himage hC T hT hheight hposition hth hcount


end
end CCDN
