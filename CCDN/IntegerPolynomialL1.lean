module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Tactic

/-! Coefficient-sum bounds for integer multivariate polynomials and their determinants. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial
open scoped BigOperators

variable {σ : Type*}

/-- The sum of the absolute values of all integer coefficients. -/
def coefficientL1 (f : MvPolynomial σ ℤ) : ℕ :=
  f.support.sum fun m => (f.coeff m).natAbs

@[simp] lemma coefficientL1_zero : coefficientL1 (0 : MvPolynomial σ ℤ) = 0 := by
  simp [coefficientL1]

lemma coefficientL1_eq_sum_of_support_subset (f : MvPolynomial σ ℤ)
    (s : Finset (σ →₀ ℕ)) (hs : f.support ⊆ s) :
    coefficientL1 f = ∑ m ∈ s, (f.coeff m).natAbs := by
  classical
  apply Finset.sum_subset hs
  intro m _ hm
  simp [notMem_support_iff.mp hm]

lemma natAbs_coeff_le_coefficientL1 (f : MvPolynomial σ ℤ) (m : σ →₀ ℕ) :
    (f.coeff m).natAbs ≤ coefficientL1 f := by
  classical
  by_cases hm : m ∈ f.support
  · exact Finset.single_le_sum (fun j _ => Nat.zero_le (f.coeff j).natAbs) hm
  · simp [notMem_support_iff.mp hm]

@[simp] lemma coefficientL1_monomial (m : σ →₀ ℕ) (c : ℤ) :
    coefficientL1 (monomial m c) = c.natAbs := by
  classical
  rw [coefficientL1_eq_sum_of_support_subset _ {m} support_monomial_subset]
  simp

@[simp] lemma coefficientL1_C (c : ℤ) :
    coefficientL1 (C c : MvPolynomial σ ℤ) = c.natAbs := by
  exact coefficientL1_monomial 0 c

@[simp] lemma coefficientL1_one : coefficientL1 (1 : MvPolynomial σ ℤ) = 1 := by
  simpa using coefficientL1_C (σ := σ) 1

lemma coefficientL1_add_le (f g : MvPolynomial σ ℤ) :
    coefficientL1 (f + g) ≤ coefficientL1 f + coefficientL1 g := by
  classical
  rw [coefficientL1_eq_sum_of_support_subset (f + g) (f.support ∪ g.support)
    support_add,
    coefficientL1_eq_sum_of_support_subset f (f.support ∪ g.support)
      Finset.subset_union_left,
    coefficientL1_eq_sum_of_support_subset g (f.support ∪ g.support)
      Finset.subset_union_right, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun m _ => by simpa using Int.natAbs_add_le (f.coeff m) (g.coeff m)

lemma coefficientL1_sum_le {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ ℤ) :
    coefficientL1 (∑ i ∈ s, f i) ≤ ∑ i ∈ s, coefficientL1 (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      simpa only [Finset.sum_insert hi] using
        (coefficientL1_add_le (f i) (∑ j ∈ s, f j)).trans (Nat.add_le_add_left ih _)

lemma coefficientL1_mul_le (f g : MvPolynomial σ ℤ) :
    coefficientL1 (f * g) ≤ coefficientL1 f * coefficientL1 g := by
  classical
  calc
    coefficientL1 (f * g) = coefficientL1
        (∑ m ∈ f.support, ∑ n ∈ g.support, monomial m (f.coeff m) *
          monomial n (g.coeff n)) := by
      congr 1
      conv_lhs => rw [f.as_sum, g.as_sum]
      rw [Finset.sum_mul]
      simp only [Finset.mul_sum]
    _ ≤ ∑ m ∈ f.support, ∑ n ∈ g.support,
        coefficientL1 (monomial m (f.coeff m) * monomial n (g.coeff n)) :=
      (coefficientL1_sum_le _ _).trans (Finset.sum_le_sum fun _ _ => coefficientL1_sum_le _ _)
    _ = coefficientL1 f * coefficientL1 g := by
      simp only [monomial_mul_monomial, coefficientL1_monomial, Int.natAbs_mul]
      simp only [← Finset.mul_sum, ← Finset.sum_mul, coefficientL1]

lemma coefficientL1_prod_le {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ ℤ) :
    coefficientL1 (∏ i ∈ s, f i) ≤ ∏ i ∈ s, coefficientL1 (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      simpa only [Finset.prod_insert hi] using
        (coefficientL1_mul_le (f i) (∏ j ∈ s, f j)).trans (Nat.mul_le_mul_left _ ih)

@[simp] lemma coefficientL1_neg (f : MvPolynomial σ ℤ) :
    coefficientL1 (-f) = coefficientL1 f := by
  classical
  simp [coefficientL1]

@[simp] lemma coefficientL1_unit_smul (u : ℤˣ) (f : MvPolynomial σ ℤ) :
    coefficientL1 (u • f) = coefficientL1 f := by
  rcases Int.units_eq_one_or u with h | h <;> simp [h]

lemma coefficientL1_det_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (MvPolynomial σ ℤ)) (L : ℕ)
    (hM : ∀ i j, coefficientL1 (M i j) ≤ L) :
    coefficientL1 M.det ≤ (Fintype.card ι).factorial * L ^ Fintype.card ι := by
  classical
  rw [Matrix.det_apply]
  calc
    coefficientL1 (∑ p : Equiv.Perm ι, p.sign • ∏ i, M (p i) i) ≤
        ∑ p : Equiv.Perm ι, coefficientL1 (p.sign • ∏ i, M (p i) i) :=
      coefficientL1_sum_le _ _
    _ ≤ ∑ _p : Equiv.Perm ι, L ^ Fintype.card ι := by
      apply Finset.sum_le_sum
      intro p _
      rw [coefficientL1_unit_smul]
      exact (coefficientL1_prod_le _ _).trans (by
        simpa using Finset.prod_le_prod (fun i (_ : i ∈ Finset.univ) => hM (p i) i))
    _ = (Fintype.card ι).factorial * L ^ Fintype.card ι := by
      simp [Fintype.card_perm]

end
end CCDN
