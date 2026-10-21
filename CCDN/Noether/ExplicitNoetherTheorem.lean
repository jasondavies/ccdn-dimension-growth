/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.UniversalHomogeneousForm
public import CCDN.ForMathlib.IntegerPolynomialL1
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import CCDN.Noether.UniversalNoetherForms
/-! CCDN Theorem 3.2.2 with the printed degree, coefficient norm, and both
specialization properties, assembled for a finite family chosen before the field. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial
universe u

/-- Explicit universal Noether polynomials. There are n+1 variables in the
input equation and binomial(n+d,n) coefficient variables in each form.
The all-characteristic vanishing and characteristic-zero detection concern
the same finite family of integer polynomials. -/
theorem exists_explicit_noether_forms (n d : ℕ) (hd : 2 ≤ d) :
    ∃ Φ : Finset (MvPolynomial (Sym (Option (Fin n)) d) ℤ),
      (∀ g ∈ Φ, g.IsHomogeneous (d ^ 2 - 1) ∧
        l1Norm g ≤ d ^ (3 * d ^ 2 - 3) *
          ((n + d).choose n * 3 ^ d) ^ (d ^ 2 - 1)) ∧
      (∀ (K : Type u) [Field K] (f : MvPolynomial (Option (Fin n)) K),
        f.IsHomogeneous d →
        ¬Irreducible (MvPolynomial.map (algebraMap K (AlgebraicClosure K)) f) →
        ∀ g ∈ Φ, homogeneousCoefficientSpecialization d f g = 0) ∧
      (∀ (K : Type u) [Field K] [CharZero K] (f : MvPolynomial (Option (Fin n)) K),
        f.IsHomogeneous d →
        Irreducible (MvPolynomial.map (algebraMap K (AlgebraicClosure K)) f) →
        ∃ g ∈ Φ, homogeneousCoefficientSpecialization d f g ≠ 0) := by
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 2 := ⟨d - 2, by omega⟩
  refine ⟨universalNoetherForms (Option (Fin n)) k, ?_, ?_, ?_⟩
  · intro g hg
    exact ⟨universalNoetherForms_homogeneous k g hg,
      universalNoetherForms_coefficientL1_le n k g hg⟩
  · intro K _ f hf hred g hg
    exact universalNoetherForms_vanish k f hf hred g hg
  · intro K _ _ f hf hir
    exact universalNoetherForms_nonvanishing k f hf hir

end
end CCDN
