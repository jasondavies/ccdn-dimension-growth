module

public import AffineCurveCounting.GenericLinearPowerBasis
public import AffineCurveCounting.BoundedPrimitiveElement

/-! Generic primitive linear combinations of a separating coordinate tuple.
The primitive specialization is constructed by the bounded primitive-element
theorem; no generic primitivity or minimal-polynomial degree is assumed. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial
attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem generic_linear_primitive
    {K A R F : Type*} [Field K] [CharZero K] [Field A] [Algebra K A]
    [Module.Finite K A] [Field R] [Field F] {n : ℕ}
    [Algebra (MvPolynomial (Fin n) K) R]
    [IsFractionRing (MvPolynomial (Fin n) K) R]
    [Algebra (MvPolynomial (Fin n) A) F]
    [IsFractionRing (MvPolynomial (Fin n) A) F]
    [Algebra (MvPolynomial (Fin n) K) F] [Algebra R F]
    [IsScalarTower (MvPolynomial (Fin n) K) R F]
    [IsScalarTower (MvPolynomial (Fin n) K) (MvPolynomial (Fin n) A) F]
    (x : Fin n → A)
    (hsep : Function.Injective
      (fun φ : A →ₐ[K] AlgebraicClosure K => fun j => φ (x j))) :
    Module.finrank R F = Module.finrank K A ∧
    (minpoly R (algebraMap (MvPolynomial (Fin n) A) F
      (genericLinearForm x))).natDegree = Module.finrank K A ∧
    IntermediateField.adjoin R
      {algebraMap (MvPolynomial (Fin n) A) F (genericLinearForm x)} = ⊤ := by
  classical
  obtain ⟨k,_,hk⟩ := exists_bounded_primitive_element x hsep
  let z := ∑j : Fin n, x j * (k : A) ^ j.val
  let b := PowerBasis.ofAdjoinSimpleEqTop (Algebra.IsIntegral.isIntegral (R := K) z) hk
  have hc : ∑i : Fin n, x i * algebraMap K A ((k : K) ^ i.val) = b.gen := by
    simp only [map_pow,map_natCast,PowerBasis.ofAdjoinSimpleEqTop_gen,b,z]
  let B := genericLinearPowerBasis (R := R) (F := F) b x
    (fun i => (k : K) ^ i.val) hc
  have hgen : B.gen = algebraMap (MvPolynomial (Fin n) A) F (genericLinearForm x) := rfl
  have hdim : B.dim = Module.finrank K A := by
    change b.dim = _
    exact b.finrank.symm
  refine ⟨B.finrank.trans hdim,?_,?_⟩
  · rw [← hgen]
    exact B.natDegree_minpoly.trans hdim
  · have hle : Algebra.adjoin R {B.gen} ≤
        (IntermediateField.adjoin R {B.gen}).toSubalgebra := by
      apply Algebra.adjoin_le
      exact IntermediateField.subset_adjoin R _
    rw [B.adjoin_gen_eq_top] at hle
    rw [← hgen]
    apply top_unique
    intro a _
    exact hle (show a ∈ (⊤ : Subalgebra R F) from trivial)

/-- Original affine coordinates of a finite function field provide the
separating tuple automatically. This is the generic last linear form used
in the Chow incidence degree comparison. -/
theorem generic_coordinate_linear_primitive
    {K E A R F : Type*} [Field K] [Field E] [CharZero E] [Field A]
    [Algebra K E] [Algebra K A] [Algebra E A] [IsScalarTower K E A]
    [Module.Finite E A] [Field R] [Field F] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    [Algebra (MvPolynomial (Fin n) K ⧸ I) A]
    [IsScalarTower K (MvPolynomial (Fin n) K ⧸ I) A]
    [IsFractionRing (MvPolynomial (Fin n) K ⧸ I) A]
    [Algebra (MvPolynomial (Fin n) E) R]
    [IsFractionRing (MvPolynomial (Fin n) E) R]
    [Algebra (MvPolynomial (Fin n) A) F]
    [IsFractionRing (MvPolynomial (Fin n) A) F]
    [Algebra (MvPolynomial (Fin n) E) F] [Algebra R F]
    [IsScalarTower (MvPolynomial (Fin n) E) R F]
    [IsScalarTower (MvPolynomial (Fin n) E) (MvPolynomial (Fin n) A) F] :
    let x := fun j : Fin n => algebraMap (MvPolynomial (Fin n) K ⧸ I) A
      ((Ideal.Quotient.mk I) (X j))
    Module.finrank R F = Module.finrank E A ∧
    (minpoly R (algebraMap (MvPolynomial (Fin n) A) F
      (genericLinearForm x))).natDegree = Module.finrank E A ∧
    IntermediateField.adjoin R
      {algebraMap (MvPolynomial (Fin n) A) F (genericLinearForm x)} = ⊤ := by
  exact generic_linear_primitive _ (curve_coordinate_embeddings_injective I)

end
end AffineCurveCounting
