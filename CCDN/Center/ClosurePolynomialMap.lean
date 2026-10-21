/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.ProjectiveClosureIdeal
public import CCDN.Projection.ProjectiveClosureProjection
public import Mathlib.Algebra.MvPolynomial.Equiv

/-! The homogeneous coordinate ring of an affine variety's projective
closure embeds into the polynomial ring over its affine coordinate ring.
The homogenizing coordinate is the polynomial variable. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial
attribute [local instance] MvPolynomial.algebraMvPolynomial

def projectiveClosurePolynomialMap {K : Type*} [Field K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) :
    MvPolynomial (Fin (n + 1)) K →ₐ[K]
      MvPolynomial Unit (MvPolynomial (Fin n) K ⧸ I) :=
  ((uniqueAlgEquiv (MvPolynomial (Fin n) K ⧸ I) Unit).symm.restrictScalars K).toAlgHom.comp
    (projectiveClosureMap I)

lemma projectiveClosureMap_homogeneous {K : Type*} [Field K] {n d : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) (f : MvPolynomial (Fin (n + 1)) K)
    (hf : f.IsHomogeneous d) :
    projectiveClosureMap I f =
      Polynomial.C (Ideal.Quotient.mk I (affineChart n f)) * Polynomial.X ^ d := by
  ext k
  rw [projectiveClosureMap_coeff, homogeneousComponent_of_mem hf,
    Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  split_ifs <;> simp_all

lemma projectiveClosurePolynomialMap_homogeneous {K : Type*} [Field K] {n d : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) (f : MvPolynomial (Fin (n + 1)) K)
    (hf : f.IsHomogeneous d) :
    projectiveClosurePolynomialMap I f =
      C (Ideal.Quotient.mk I (affineChart n f)) * X () ^ d := by
  change (uniqueAlgEquiv (MvPolynomial (Fin n) K ⧸ I) Unit).symm
    (projectiveClosureMap I f) = _
  rw [projectiveClosureMap_homogeneous I f hf]
  simp [uniqueAlgEquiv_symm_apply]

lemma projectiveClosurePolynomialMap_X_zero {K : Type*} [Field K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) :
    projectiveClosurePolynomialMap I (X 0) = X () := by
  rw [projectiveClosurePolynomialMap_homogeneous I _ (isHomogeneous_X K 0)]
  simp [affineChart]

lemma projectiveClosurePolynomialMap_rename_homogeneous {K : Type*} [Field K] {n d : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) (f : MvPolynomial (Fin n) K)
    (hf : f.IsHomogeneous d) :
    projectiveClosurePolynomialMap I (rename Fin.succ f) =
      C (Ideal.Quotient.mk I f) * X () ^ d := by
  rw [projectiveClosurePolynomialMap_homogeneous I _ hf.rename_isHomogeneous,
    affineChart_rename_succ]

lemma projectiveClosurePolynomialMap_X_succ {K : Type*} [Field K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) (j : Fin n) :
    projectiveClosurePolynomialMap I (X j.succ) =
      C (Ideal.Quotient.mk I (X j)) * X () := by
  rw [← rename_X Fin.succ j,
    projectiveClosurePolynomialMap_rename_homogeneous I _ (isHomogeneous_X K j), pow_one]

lemma projectiveClosurePolynomialMap_ker {K : Type*} [Field K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) :
    RingHom.ker (projectiveClosurePolynomialMap I) = projectiveClosureIdeal I := by
  ext f
  change (uniqueAlgEquiv (MvPolynomial (Fin n) K ⧸ I) Unit).symm
    (projectiveClosureMap I f) = 0 ↔ projectiveClosureMap I f = 0
  exact (uniqueAlgEquiv (MvPolynomial (Fin n) K ⧸ I) Unit).symm.injective.eq_iff'
    (map_zero _)

def closurePolynomialQuotientMap {K : Type*} [Field K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) :
    (MvPolynomial (Fin (n + 1)) K ⧸ projectiveClosureIdeal I) →ₐ[K]
      MvPolynomial Unit (MvPolynomial (Fin n) K ⧸ I) :=
  Ideal.Quotient.liftₐ (projectiveClosureIdeal I) (projectiveClosurePolynomialMap I)
    (fun f hf => by
      have h : f ∈ RingHom.ker (projectiveClosurePolynomialMap I) := by
        rwa [projectiveClosurePolynomialMap_ker]
      exact h)

theorem closurePolynomialQuotientMap_injective {K : Type*} [Field K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) :
    Function.Injective (closurePolynomialQuotientMap I) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  obtain ⟨f,rfl⟩ := Ideal.Quotient.mk_surjective x
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  rw [← projectiveClosurePolynomialMap_ker]
  exact hx

end
end CCDN
