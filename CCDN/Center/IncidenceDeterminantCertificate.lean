/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Center.HomogeneousIncidenceRelations
public import CCDN.Algebra.HomogeneousMonomials
import CCDN.Algebra.HomogeneousEvaluation
/-! A polynomial determinant separates an empty homogeneous linear incidence
fiber from every tuple with a nonzero common zero. Its construction uses
homogeneous ideal membership certificates and a complete monomial basis. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The coefficient of one fixed monomial in a universal linear combination. -/
def incidenceCoefficientPolynomial {K : Type*} [Field K] {n r : ℕ}
    (q : MvPolynomial (Fin (n + 1)) K)
    (p : Fin r → MvPolynomial (Fin (n + 1)) K) (e : Fin (n + 1) →₀ ℕ) :
    MvPolynomial (Fin r × Fin (n + 1)) K :=
  C (q.coeff e) + ∑ i, ∑ j, X (i,j) * C ((X j * p i).coeff e)

lemma incidenceCoefficientPolynomial_eval {K : Type*} [Field K] {n r : ℕ}
    (q : MvPolynomial (Fin (n + 1)) K)
    (p : Fin r → MvPolynomial (Fin (n + 1)) K) (e : Fin (n + 1) →₀ ℕ)
    (U : Fin r × Fin (n + 1) → K) :
    eval U (incidenceCoefficientPolynomial q p e) =
      (q + ∑ i, incidenceLinearForm U i * p i).coeff e := by
  simp [incidenceCoefficientPolynomial, incidenceLinearForm, Finset.sum_mul, mul_assoc]

lemma homogeneous_coefficient_evaluation {K : Type*} [Field K] {n M : ℕ}
    (f : MvPolynomial (Fin (n + 1)) K) (hf : f.IsHomogeneous M)
    (x : Fin (n + 1) → K) :
    ∑ j, f.coeff (homogeneousMonomials n M j) *
      eval x (monomial (homogeneousMonomials n M j) 1) = eval x f := by
  conv_rhs => rw [homogeneous_eq_sum_coeff f hf]
  simp [eval_monomial]

/-- Homogeneous monomials of any fixed degree do not vanish simultaneously at
a nonzero vector. -/
lemma homogeneous_monomial_values_ne_zero {K : Type*} [Field K] {n M : ℕ}
    (x : Fin (n + 1) → K) (hx : x ≠ 0) :
    (fun j => eval x (monomial (homogeneousMonomials n M j) (1 : K))) ≠ 0 := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra! h
    exact hx (funext h)
  obtain ⟨j, hj⟩ := homogeneousMonomials_surjective n M (Finsupp.single i M) (by simp)
  intro he
  have hz := congrFun he j
  rw [hj] at hz
  simp only [eval_monomial, one_mul, Finsupp.prod_single_index, pow_zero, Pi.zero_apply] at hz
  exact pow_ne_zero M hi hz

/-- Homogeneous membership for every degree-`t+1` monomial constructs a
polynomial which is nonzero at the chosen tuple and zero at every incident tuple. -/
theorem exists_incidence_determinant_certificate {K : Type*} [Field K] {n r t : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hJ : IsHomogeneousIdeal J)
    (U : Fin r × Fin (n + 1) → K)
    (hmem : ∀ e : Fin ((n + (t + 1)).choose (t + 1)),
      monomial (homogeneousMonomials n (t + 1) e) 1 ∈
        J ⊔ Ideal.span (Set.range (incidenceLinearForm U))) :
    ∃ D : MvPolynomial (Fin r × Fin (n + 1)) K,
      eval U D = 1 ∧ ∀ V : Fin r × Fin (n + 1) → K,
        (∃ x : Fin (n + 1) → K, x ≠ 0 ∧ (∀ f ∈ J, eval x f = 0) ∧
          ∀ i, ∑ j, V (i,j) * x j = 0) → eval V D = 0 := by
  classical
  have hrel (e : Fin ((n + (t + 1)).choose (t + 1))) :=
    homogeneous_incidence_relation J hJ U _
      (isHomogeneous_monomial (1 : K) (homogeneousMonomials_degree n (t + 1) e)) (hmem e)
  choose q p hq hqhom hphom heq using hrel
  let A : Matrix (Fin ((n + (t + 1)).choose (t + 1)))
      (Fin ((n + (t + 1)).choose (t + 1))) (MvPolynomial (Fin r × Fin (n + 1)) K) :=
    fun e j => incidenceCoefficientPolynomial (q e) (p e) (homogeneousMonomials n (t + 1) j)
  have heval (V : Fin r × Fin (n + 1) → K) (e j) :
      eval V (A e j) = (q e + ∑ i, incidenceLinearForm V i * p e i).coeff
        (homogeneousMonomials n (t + 1) j) :=
    incidenceCoefficientPolynomial_eval _ _ _ V
  refine ⟨A.det, ?_, ?_⟩
  · rw [RingHom.map_det]
    have hA : (eval U).mapMatrix A = 1 := by
      ext e j
      change eval U (A e j) = (1 : Matrix _ _ K) e j
      rw [heval, heq]
      simp [Matrix.one_apply, coeff_monomial, (homogeneousMonomials_injective n (t + 1)).eq_iff]
    rw [hA, Matrix.det_one]
  · intro V hV
    obtain ⟨x, hx, hxJ, hxV⟩ := hV
    rw [RingHom.map_det]
    apply Matrix.exists_mulVec_eq_zero_iff.mp
    refine ⟨fun j => eval x (monomial (homogeneousMonomials n (t + 1) j) 1),
      homogeneous_monomial_values_ne_zero x hx, ?_⟩
    ext e
    change (∑ j, eval V (A e j) *
      eval x (monomial (homogeneousMonomials n (t + 1) j) 1)) = 0
    simp_rw [heval]
    have hhom : (q e + ∑ i, incidenceLinearForm V i * p e i).IsHomogeneous (t + 1) := by
      apply (hqhom e).add
      apply IsHomogeneous.sum
      intro i _
      simpa only [Nat.add_comm 1 t] using (incidenceLinearForm_homogeneous V i).mul (hphom e i)
    rw [homogeneous_coefficient_evaluation _ hhom x, eval_add, map_sum, hxJ _ (hq e), zero_add]
    apply Finset.sum_eq_zero
    intro i _
    rw [eval_mul, incidenceLinearForm_eval, hxV, zero_mul]

end
end CCDN
