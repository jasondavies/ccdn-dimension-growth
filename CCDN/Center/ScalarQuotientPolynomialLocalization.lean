/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.MvPolynomial.Localization

/-! The scalar-extended coordinate quotient is the localization of the
polynomial extension of the original coordinate quotient. All maps are
the coefficient and coordinate maps. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial
attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- Interchange parameters and coordinates, then impose the source ideal. -/
def quotientPolynomialSwap {K σ τ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) :
    MvPolynomial σ (MvPolynomial τ K) →+* MvPolynomial τ (MvPolynomial σ K ⧸ I) :=
  (map (Ideal.Quotient.mk I)).comp (commAlgEquiv K σ τ).toRingHom

private lemma quotientPolynomialSwap_surjective {K σ τ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) :
    Function.Surjective (quotientPolynomialSwap (τ := τ) I) :=
  (map_surjective _ Ideal.Quotient.mk_surjective).comp (commAlgEquiv K σ τ).surjective

private lemma quotientPolynomialSwap_kernel {K σ τ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) :
    RingHom.ker (quotientPolynomialSwap (τ := τ) I) = I.map (map C) := by
  rw [quotientPolynomialSwap, ← RingHom.comap_ker, MvPolynomial.ker_map, Ideal.mk_ker]
  change (I.map C).comap (commAlgEquiv K σ τ).toRingEquiv = _
  rw [← Ideal.map_symm (commAlgEquiv K σ τ).toRingEquiv]
  change (I.map C).map (commAlgEquiv K σ τ).symm.toRingHom = _
  rw [Ideal.map_map]
  congr 1
  apply RingHom.ext
  intro p
  change (commAlgEquiv K τ σ) (C p) = map C p
  exact commAlgEquiv_C p

/-- The source coordinate quotient embeds into the scalar-extended one. -/
def scalarCoordinateQuotientMap {K L σ : Type*} [Field K] [Field L] [Algebra K L]
    (I : Ideal (MvPolynomial σ K)) :
    (MvPolynomial σ K ⧸ I) →+* (MvPolynomial σ L ⧸ I.map (map (algebraMap K L))) :=
  Ideal.quotientMap _ (map (algebraMap K L)) (Ideal.le_comap_map)

/-- Polynomial parameters become scalar coefficients in the extended quotient. -/
def scalarQuotientPolynomialMap {K L σ τ : Type*} [Field K] [Field L]
    [Algebra K L] [Algebra (MvPolynomial τ K) L]
    [IsScalarTower K (MvPolynomial τ K) L]
    (I : Ideal (MvPolynomial σ K)) :
    MvPolynomial τ (MvPolynomial σ K ⧸ I) →+*
      (MvPolynomial σ L ⧸ I.map (map (algebraMap K L))) :=
  eval₂Hom (scalarCoordinateQuotientMap I) (fun j =>
    Ideal.Quotient.mk _ (C (algebraMap (MvPolynomial τ K) L (X j))))

private lemma scalarQuotientPolynomialMap_comp {K L σ τ : Type*} [Field K] [Field L]
    [Algebra K L] [Algebra (MvPolynomial τ K) L]
    [IsScalarTower K (MvPolynomial τ K) L]
    (I : Ideal (MvPolynomial σ K)) :
    (scalarQuotientPolynomialMap (τ := τ) (L := L) I).comp
      (quotientPolynomialSwap I) =
      (Ideal.Quotient.mk (I.map (map (algebraMap K L)))).comp
        (map (algebraMap (MvPolynomial τ K) L)) := by
  apply MvPolynomial.ringHom_ext
  · intro p
    induction p using MvPolynomial.induction_on with
    | C c =>
        simp [scalarQuotientPolynomialMap,quotientPolynomialSwap,scalarCoordinateQuotientMap]
        congr 2
        exact IsScalarTower.algebraMap_apply K (MvPolynomial τ K) L c
    | add p q hp hq => simpa only [map_add] using congrArg₂ (· + ·) hp hq
    | mul_X p j hp =>
        simp only [map_mul]
        rw [hp]
        simp [scalarQuotientPolynomialMap,quotientPolynomialSwap]
  · intro i
    simp [scalarQuotientPolynomialMap,quotientPolynomialSwap,scalarCoordinateQuotientMap]

/-- The precise localization structure on the scalar-extended quotient. -/
theorem scalar_quotient_polynomial_localization {K L σ τ : Type*}
    [Field K] [Field L] [Algebra K L] [Algebra (MvPolynomial τ K) L]
    [IsScalarTower K (MvPolynomial τ K) L]
    [IsFractionRing (MvPolynomial τ K) L]
    (I : Ideal (MvPolynomial σ K)) :
    let φ := scalarQuotientPolynomialMap (τ := τ) (L := L) I
    let : Algebra (MvPolynomial τ (MvPolynomial σ K ⧸ I))
      (MvPolynomial σ L ⧸ I.map (map (algebraMap K L))) := φ.toAlgebra
    IsLocalization
      (((nonZeroDivisors (MvPolynomial τ K)).map (C (σ := σ))).map
        (quotientPolynomialSwap I))
      (MvPolynomial σ L ⧸ I.map (map (algebraMap K L))) := by
  let φ := scalarQuotientPolynomialMap (τ := τ) (L := L) I
  let : Algebra (MvPolynomial τ (MvPolynomial σ K ⧸ I))
      (MvPolynomial σ L ⧸ I.map (map (algebraMap K L))) := φ.toAlgebra
  change IsLocalization _ _
  apply IsLocalization.of_surjective (R' := MvPolynomial τ (MvPolynomial σ K ⧸ I))
    ((nonZeroDivisors (MvPolynomial τ K)).map (C (σ := σ))) (MvPolynomial σ L)
    (quotientPolynomialSwap (τ := τ) I) (quotientPolynomialSwap_surjective I)
    (Ideal.Quotient.mk (I.map (map (algebraMap K L)))) Ideal.Quotient.mk_surjective
    (by
      change (Ideal.Quotient.mk _).comp (map (algebraMap (MvPolynomial τ K) L)) =
        φ.comp (quotientPolynomialSwap I)
      exact (scalarQuotientPolynomialMap_comp I).symm)
  rw [Ideal.mk_ker,quotientPolynomialSwap_kernel,Ideal.map_map]
  apply le_of_eq
  congr 1
  apply MvPolynomial.ringHom_ext
  · intro c
    simp only [RingHom.comp_apply,MvPolynomial.algebraMap_def,map_C]
    change C (algebraMap K L c) = C (algebraMap (MvPolynomial τ K) L (C c))
    exact congrArg C (IsScalarTower.algebraMap_apply K (MvPolynomial τ K) L c)
  · intro i
    simp

end
end CCDN
