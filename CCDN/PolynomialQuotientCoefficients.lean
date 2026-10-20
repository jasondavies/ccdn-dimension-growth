module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Algebra.MvPolynomial.Equiv

/-! Polynomial extension commutes with the coefficient quotient.
The comparison is obtained from its coefficientwise kernel. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

lemma polynomial_quotient_map_kernel {R σ : Type*} [CommRing R]
    (I : Ideal R) :
    RingHom.ker (map (σ := σ) (Ideal.Quotient.mk I)) = I.map C := by
  classical
  apply le_antisymm
  · intro p hp
    have hc (e) : p.coeff e ∈ I := by
      have he := congrArg (fun q : MvPolynomial σ (R ⧸ I) => q.coeff e) hp
      simpa only [coeff_map, AddMonoidAlgebra.coeff_zero,
        Finsupp.zero_apply, Ideal.Quotient.eq_zero_iff_mem] using he
    rw [p.as_sum]
    apply sum_mem
    intro e _
    rw [← mul_one (p.coeff e), ← C_mul_monomial]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem C (hc e))
  · rw [Ideal.map_le_iff_le_comap]
    intro r hr
    change map (Ideal.Quotient.mk I) (C r) = 0
    rw [map_C, Ideal.Quotient.eq_zero_iff_mem.mpr hr, C_0]

/-- Coefficient quotient comparison with its exact evaluation map. -/
def polynomialQuotientCoefficients {R σ : Type*} [CommRing R]
    (I : Ideal R) :
    (MvPolynomial σ R ⧸ I.map C) ≃+* MvPolynomial σ (R ⧸ I) :=
  (Ideal.quotEquivOfEq (polynomial_quotient_map_kernel (σ := σ) I).symm).trans
    (RingHom.quotientKerEquivOfSurjective
      (map_surjective _ Ideal.Quotient.mk_surjective))

@[simp] lemma polynomialQuotientCoefficients_mk {R σ : Type*} [CommRing R]
    (I : Ideal R) (p : MvPolynomial σ R) :
    polynomialQuotientCoefficients I (Ideal.Quotient.mk _ p) =
      map (Ideal.Quotient.mk I) p := rfl

end
end CCDN
