/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Center.ClosurePolynomialMap
public import CCDN.Projection.ProjectionFractionField
/-! The function field of the cone over an affine variety's projective closure is
the fraction field of a polynomial ring over the affine coordinate ring.
Dividing the homogeneous coordinates by the homogenizing variable recovers
all affine coordinates. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial
attribute [local instance] MvPolynomial.algebraMvPolynomial

def closurePolynomialFieldMap {K F : Type*} [Field K] [Field F] [Algebra K F] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K))
    [Algebra (MvPolynomial Unit (MvPolynomial (Fin n) K ⧸ I)) F]
    [IsScalarTower K (MvPolynomial Unit (MvPolynomial (Fin n) K ⧸ I)) F] :
    (MvPolynomial (Fin (n + 1)) K ⧸ projectiveClosureIdeal I) →ₐ[K] F :=
  (IsScalarTower.toAlgHom K (MvPolynomial Unit (MvPolynomial (Fin n) K ⧸ I)) F).comp
    (closurePolynomialQuotientMap I)

lemma closurePolynomialFieldMap_mk {K F : Type*} [Field K] [Field F] [Algebra K F] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K))
    [Algebra (MvPolynomial Unit (MvPolynomial (Fin n) K ⧸ I)) F]
    [IsScalarTower K (MvPolynomial Unit (MvPolynomial (Fin n) K ⧸ I)) F]
    (f : MvPolynomial (Fin (n + 1)) K) :
    closurePolynomialFieldMap (F := F) I (Ideal.Quotient.mk (projectiveClosureIdeal I) f) =
      algebraMap (MvPolynomial Unit (MvPolynomial (Fin n) K ⧸ I)) F
        (projectiveClosurePolynomialMap I f) := rfl

theorem closure_polynomial_coordinates_generate
    {K F : Type*} [Field K] [Field F] [Algebra K F] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    [Algebra (MvPolynomial Unit (MvPolynomial (Fin n) K ⧸ I)) F]
    [IsScalarTower K (MvPolynomial Unit (MvPolynomial (Fin n) K ⧸ I)) F]
    [IsFractionRing (MvPolynomial Unit (MvPolynomial (Fin n) K ⧸ I)) F] :
    IntermediateField.adjoin K (Set.range (fun i : Fin (n + 1) =>
      closurePolynomialFieldMap (F := F) I
        (Ideal.Quotient.mk (projectiveClosureIdeal I) (X i)))) = ⊤ := by
  let A := MvPolynomial (Fin n) K ⧸ I
  let P := MvPolynomial Unit A
  let η : P →ₐ[K] F := IsScalarTower.toAlgHom K P F
  let θ := closurePolynomialFieldMap (F := F) I
  let E := IntermediateField.adjoin K (Set.range (fun i : Fin (n + 1) =>
    θ (Ideal.Quotient.mk (projectiveClosureIdeal I) (X i))))
  have hT : η (X ()) ∈ E := by
    have h := IntermediateField.subset_adjoin K _
      (show θ (Ideal.Quotient.mk (projectiveClosureIdeal I) (X 0)) ∈
        Set.range (fun i : Fin (n + 1) =>
          θ (Ideal.Quotient.mk (projectiveClosureIdeal I) (X i))) from ⟨0,rfl⟩)
    change η (projectiveClosurePolynomialMap I (X 0)) ∈ E at h
    rwa [projectiveClosurePolynomialMap_X_zero] at h
  have hTne : η (X ()) ≠ 0 :=
    fun h => X_ne_zero () ((IsFractionRing.injective P F) (h.trans (map_zero η).symm))
  have hx (j : Fin n) : η (C (Ideal.Quotient.mk I (X j))) ∈ E := by
    have h := IntermediateField.subset_adjoin K _
      (show θ (Ideal.Quotient.mk (projectiveClosureIdeal I) (X j.succ)) ∈
        Set.range (fun i : Fin (n + 1) =>
          θ (Ideal.Quotient.mk (projectiveClosureIdeal I) (X i))) from ⟨j.succ,rfl⟩)
    change η (projectiveClosurePolynomialMap I (X j.succ)) ∈ E at h
    rw [projectiveClosurePolynomialMap_X_succ, map_mul] at h
    have hh := E.div_mem h hT
    simpa only [mul_div_cancel_right₀ _ hTne] using hh
  let γ : MvPolynomial (Fin n) K →ₐ[K] F := η.comp
    ((IsScalarTower.toAlgHom K A P).comp (Ideal.Quotient.mkₐ K I))
  have hcoeffpoly (f : MvPolynomial (Fin n) K) : η (C (Ideal.Quotient.mk I f)) ∈ E := by
    change γ f ∈ E
    induction f using MvPolynomial.induction_on with
    | C c =>
      change γ (algebraMap K (MvPolynomial (Fin n) K) c) ∈ E
      rw [γ.commutes]
      exact E.algebraMap_mem c
    | add p q hp hq => rw [map_add]; exact E.add_mem hp hq
    | mul_X p j hp => rw [map_mul]; exact E.mul_mem hp (hx j)
  have hcoeff (a : A) : η (C a) ∈ E := by
    obtain ⟨f,rfl⟩ := Ideal.Quotient.mk_surjective a
    exact hcoeffpoly f
  have hpoly (f : P) : η f ∈ E := by
    induction f using MvPolynomial.induction_on with
    | C c => exact hcoeff c
    | add p q hp hq => rw [map_add]; exact E.add_mem hp hq
    | mul_X p j hp =>
      cases j
      rw [map_mul]
      exact E.mul_mem hp hT
  change E = ⊤
  apply top_unique
  intro x _
  obtain ⟨p,q,_,rfl⟩ := IsFractionRing.div_surjective P x
  exact E.div_mem (hpoly p) (hpoly q)

/-- The cone embedding realizes any fraction field of A[t] as a
fraction field of the closure's homogeneous coordinate ring. -/
theorem closure_polynomial_field_isFractionRing
    {K F : Type*} [Field K] [Field F] [Algebra K F] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    [Algebra (MvPolynomial Unit (MvPolynomial (Fin n) K ⧸ I)) F]
    [IsScalarTower K (MvPolynomial Unit (MvPolynomial (Fin n) K ⧸ I)) F]
    [IsFractionRing (MvPolynomial Unit (MvPolynomial (Fin n) K ⧸ I)) F] :
    let : Algebra (MvPolynomial (Fin (n + 1)) K ⧸ projectiveClosureIdeal I) F :=
      (closurePolynomialFieldMap (F := F) I).toRingHom.toAlgebra
    IsFractionRing (MvPolynomial (Fin (n + 1)) K ⧸ projectiveClosureIdeal I) F := by
  exact isFractionRing_of_generating_tuple (closurePolynomialFieldMap (F := F) I)
    ((IsFractionRing.injective (MvPolynomial Unit (MvPolynomial (Fin n) K ⧸ I)) F).comp
      (closurePolynomialQuotientMap_injective I))
    (fun i : Fin (n + 1) => Ideal.Quotient.mk (projectiveClosureIdeal I) (X i))
    (closure_polynomial_coordinates_generate I)

end
end CCDN
