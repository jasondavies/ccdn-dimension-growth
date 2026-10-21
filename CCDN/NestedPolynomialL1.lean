module

public import CCDN.IntegerPolynomialL1
public import Mathlib.Algebra.MvPolynomial.Equiv

/-! Flattening polynomial coefficient variables preserves each coefficient
and bounds the coefficient norm of every extracted parameter coefficient.
These estimates introduce no factor depending on parameter degrees. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

lemma coefficientL1_rename_le {σ τ : Type*} (v : σ → τ) (f : MvPolynomial σ ℤ) :
    coefficientL1 (rename v f) ≤ coefficientL1 f := by
  classical
  calc
    coefficientL1 (rename v f) = coefficientL1
        (∑ m ∈ f.support, monomial (m.mapDomain v) (f.coeff m)) := by
      congr 1
      conv_lhs => rw [f.as_sum]
      simp only [map_sum, rename_monomial]
    _ ≤ ∑ m ∈ f.support, coefficientL1 (monomial (m.mapDomain v) (f.coeff m)) :=
      coefficientL1_sum_le _ _
    _ = coefficientL1 f := by
      simp only [coefficientL1_monomial]
      rfl

lemma flattenPolynomial_coeff {σ τ : Type*}
    (f : MvPolynomial σ (MvPolynomial τ ℤ)) (m : σ →₀ ℕ) (n : τ →₀ ℕ) :
    ((sumAlgEquiv ℤ σ τ).symm f).coeff
      (Finsupp.sumFinsuppAddEquivProdFinsupp.symm (m,n)) = (f.coeff m).coeff n := by
  simp [sumAlgEquiv, AddMonoidAlgebra.curryAlgEquiv,
    AddMonoidAlgebra.curryRingEquiv, AddMonoidAlgebra.curryAddEquiv]
  rfl

/-- Extracting one outer coefficient never increases the total coefficient
sum after flattening the two variable families. -/
theorem coefficientL1_coeff_le_flatten {σ τ : Type*}
    (f : MvPolynomial σ (MvPolynomial τ ℤ)) (m : σ →₀ ℕ) :
    coefficientL1 (f.coeff m) ≤ coefficientL1 ((sumAlgEquiv ℤ σ τ).symm f) := by
  classical
  let e : (τ →₀ ℕ) → (σ ⊕ τ →₀ ℕ) :=
    fun n => Finsupp.sumFinsuppAddEquivProdFinsupp.symm (m,n)
  have hinj : Function.Injective e := by
    intro n n' h
    exact congrArg Prod.snd (Finsupp.sumFinsuppAddEquivProdFinsupp.symm.injective h)
  have hs : (f.coeff m).support.image e ⊆ ((sumAlgEquiv ℤ σ τ).symm f).support := by
    intro a ha
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp ha
    rw [mem_support_iff, flattenPolynomial_coeff]
    exact mem_support_iff.mp hn
  calc
    coefficientL1 (f.coeff m) =
        ∑ a ∈ (f.coeff m).support.image e,
          (((sumAlgEquiv ℤ σ τ).symm f).coeff a).natAbs := by
      rw [Finset.sum_image (fun a _ b _ h => hinj h)]
      simp only [e, flattenPolynomial_coeff, coefficientL1]
    _ ≤ coefficientL1 ((sumAlgEquiv ℤ σ τ).symm f) :=
      Finset.sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => Nat.zero_le _)

lemma flattenPolynomial_map_C {σ τ : Type*} (p : MvPolynomial σ ℤ) :
    (sumAlgEquiv ℤ σ τ).symm (map (C : ℤ →+* MvPolynomial τ ℤ) p) =
      rename Sum.inl p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add f g hf hg => simp [hf, hg]
  | mul_X f i hf => simp [hf]

/-- One original coefficient variable multiplying an integer parameter
polynomial has no coefficient-norm cost beyond that parameter polynomial. -/
theorem coefficientL1_flatten_C_X_mul_map_C_le {σ τ : Type*}
    (p : MvPolynomial σ ℤ) (i : τ) :
    coefficientL1 ((sumAlgEquiv ℤ σ τ).symm
      (C (X i) * map (C : ℤ →+* MvPolynomial τ ℤ) p)) ≤ coefficientL1 p := by
  rw [map_mul, sumAlgEquiv_symm_C_X, flattenPolynomial_map_C]
  apply (coefficientL1_mul_le _ _).trans
  simpa only [X, coefficientL1_monomial, Int.natAbs_one, one_mul] using
    coefficientL1_rename_le Sum.inl p

end
end CCDN
