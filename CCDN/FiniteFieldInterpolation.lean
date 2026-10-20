module

public import CCDN.MonomialDimension
public import Mathlib.FieldTheory.Finite.Basic

/-! Finite-field interpolation with degree bounded by the ambient dimension
times q-1, independently of the number of selected points. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The coordinatewise Fermat indicator of a point. -/
def finiteFieldPointSeparator {K σ : Type*} [Field K] [Fintype K] [Fintype σ]
    (a : σ → K) : MvPolynomial σ K :=
  ∏ j, (1 - (X j - C (a j)) ^ (Fintype.card K - 1))

lemma finiteFieldPointSeparator_eval {K σ : Type*} [Field K] [Fintype K] [Fintype σ]
    [DecidableEq K]
    (a x : σ → K) : eval x (finiteFieldPointSeparator a) = if x = a then 1 else 0 := by
  classical
  have hq : Fintype.card K - 1 ≠ 0 := by have := Fintype.one_lt_card (α := K); omega
  rw [finiteFieldPointSeparator, eval_prod]
  by_cases h : x = a
  · subst x
    simp [hq]
  · rw [ite_eq_right h]
    obtain ⟨j, hj⟩ := Function.ne_iff.mp h
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    simp only [eval_sub, map_one, eval_pow, eval_X, eval_C,
      FiniteField.pow_card_sub_one_eq_one _ (sub_ne_zero.mpr hj), sub_self]

lemma finiteFieldPointSeparator_degree {K σ : Type*} [Field K] [Fintype K] [Fintype σ]
    (a : σ → K) :
    (finiteFieldPointSeparator a).totalDegree ≤ Fintype.card σ * (Fintype.card K - 1) := by
  classical
  unfold finiteFieldPointSeparator
  calc
    _ ≤ ∑ j : σ, (1 - (X j - C (a j)) ^ (Fintype.card K - 1)).totalDegree :=
      totalDegree_finsetProd _ _
    _ ≤ ∑ _j : σ, (Fintype.card K - 1) := by
      apply Finset.sum_le_sum
      intro j _
      apply (totalDegree_sub _ _).trans
      rw [totalDegree_one]
      apply max_le (Nat.zero_le _)
      have hlin : (X j - C (a j)).totalDegree ≤ 1 :=
        (totalDegree_sub _ _).trans (by simp)
      exact (totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left (Fintype.card K - 1) hlin)
    _ = _ := by simp

/-- Any finite set of distinct zeros forces at least its cardinality many
independent classes by the fixed finite-field interpolation degree. -/
theorem finite_field_points_filtered_lower {K σ ι : Type*} [Field K] [Fintype K]
    [Fintype σ] [Fintype ι] [DecidableEq ι]
    (I : Ideal (MvPolynomial σ K)) (z : ι → σ → K) (hz : Function.Injective z)
    (hzI : ∀ i f, f ∈ I → eval (z i) f = 0) {N : ℕ}
    (hN : Fintype.card σ * (Fintype.card K - 1) ≤ N) :
    Fintype.card ι ≤ Module.finrank K (filteredCoordinateSpace I N) := by
  classical
  let q := Ideal.Quotient.mkₐ K I
  let ψ : ι → (MvPolynomial σ K ⧸ I) →ₐ[K] K := fun i =>
    Ideal.Quotient.liftₐ I (aeval (z i)) (by
      intro f hf
      simpa only [aeval_eq_eval] using hzI i f hf)
  have hψ (i : ι) (f : MvPolynomial σ K) : ψ i (q f) = eval (z i) f := rfl
  let v : ι → filteredCoordinateSpace I N := fun j =>
    ⟨q (finiteFieldPointSeparator (z j)), Submodule.mem_map.mpr
      ⟨finiteFieldPointSeparator (z j),
        (mem_restrictTotalDegree _ _ _).mpr ((finiteFieldPointSeparator_degree _).trans hN), rfl⟩⟩
  have hlin : LinearIndependent K v := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have he := congrArg (fun w : filteredCoordinateSpace I N => ψ i w.val) hc
    simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul,
      ZeroMemClass.coe_zero, map_zero] at he
    change (∑ j, c j • ψ i (q (finiteFieldPointSeparator (z j)))) = 0 at he
    simp only [hψ, finiteFieldPointSeparator_eval, hz.eq_iff, smul_eq_mul] at he
    simpa using he
  exact hlin.fintype_card_le_finrank

end
end CCDN
