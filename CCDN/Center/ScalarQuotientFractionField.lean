/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Center.ScalarQuotientPolynomialLocalization
public import CCDN.ForMathlib.FractionRing

/-! A fraction field of the parameter polynomial extension is also
the fraction field of the scalar-extended source coordinate quotient. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

local instance scalarFractionPolynomialRing {K σ τ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) :
    CommRing (MvPolynomial τ (MvPolynomial σ K ⧸ I)) := by
  letI : CommRing (MvPolynomial σ K ⧸ I) := inferInstance
  infer_instance
attribute [local instance] MvPolynomial.algebraMvPolynomial

section
variable {K L F σ τ : Type*} [Field K] [Field L] [Field F]
  [Algebra K L] [Algebra (MvPolynomial τ K) L]
  [IsScalarTower K (MvPolynomial τ K) L] [IsFractionRing (MvPolynomial τ K) L]
  (I : Ideal (MvPolynomial σ K)) [I.IsPrime]
  [(I.map (map (algebraMap K L))).IsPrime]
  [Algebra (MvPolynomial τ (MvPolynomial σ K ⧸ I)) F]
  [IsFractionRing (MvPolynomial τ (MvPolynomial σ K ⧸ I)) F]

/-- The canonical compatible embedding into the original fraction field. -/
def scalarQuotientFractionMap :
    (MvPolynomial σ L ⧸ I.map (map (algebraMap K L))) →+* F :=
  let : Algebra (MvPolynomial τ (MvPolynomial σ K ⧸ I))
      (MvPolynomial σ L ⧸ I.map (map (algebraMap K L))) :=
    (scalarQuotientPolynomialMap (τ := τ) (L := L) I).toAlgebra
  let : IsLocalization
      (((nonZeroDivisors (MvPolynomial τ K)).map (C (σ := σ))).map
        (quotientPolynomialSwap I).toMonoidHom)
      (MvPolynomial σ L ⧸ I.map (map (algebraMap K L))) :=
    scalar_quotient_polynomial_localization I
  IsFractionRing.liftOfLocalization
    (S := MvPolynomial σ L ⧸ I.map (map (algebraMap K L))) (F := F)
    (((nonZeroDivisors (MvPolynomial τ K)).map (C (σ := σ))).map
      (quotientPolynomialSwap I).toMonoidHom)

lemma scalarQuotientFractionMap_comp :
    (scalarQuotientFractionMap (F := F) (τ := τ) (L := L) I).comp
      (scalarQuotientPolynomialMap (τ := τ) (L := L) I) =
        algebraMap (MvPolynomial τ (MvPolynomial σ K ⧸ I)) F := by
  let : Algebra (MvPolynomial τ (MvPolynomial σ K ⧸ I))
      (MvPolynomial σ L ⧸ I.map (map (algebraMap K L))) :=
    (scalarQuotientPolynomialMap (τ := τ) (L := L) I).toAlgebra
  let : IsLocalization
      (((nonZeroDivisors (MvPolynomial τ K)).map (C (σ := σ))).map
        (quotientPolynomialSwap I).toMonoidHom)
      (MvPolynomial σ L ⧸ I.map (map (algebraMap K L))) :=
    scalar_quotient_polynomial_localization I
  exact IsFractionRing.liftOfLocalization_comp
    (S := MvPolynomial σ L ⧸ I.map (map (algebraMap K L))) (F := F)
    (((nonZeroDivisors (MvPolynomial τ K)).map (C (σ := σ))).map
      (quotientPolynomialSwap I).toMonoidHom)

theorem scalarQuotientFractionMap_isFractionRing :
    let : Algebra (MvPolynomial σ L ⧸ I.map (map (algebraMap K L))) F :=
      (scalarQuotientFractionMap (F := F) (τ := τ) (L := L) I).toAlgebra
    IsFractionRing (MvPolynomial σ L ⧸ I.map (map (algebraMap K L))) F := by
  let : Algebra (MvPolynomial τ (MvPolynomial σ K ⧸ I))
      (MvPolynomial σ L ⧸ I.map (map (algebraMap K L))) :=
    (scalarQuotientPolynomialMap (τ := τ) (L := L) I).toAlgebra
  let : IsLocalization
      (((nonZeroDivisors (MvPolynomial τ K)).map (C (σ := σ))).map
        (quotientPolynomialSwap I).toMonoidHom)
      (MvPolynomial σ L ⧸ I.map (map (algebraMap K L))) :=
    scalar_quotient_polynomial_localization I
  exact IsFractionRing.isFractionRing_liftOfLocalization
    (S := MvPolynomial σ L ⧸ I.map (map (algebraMap K L))) (F := F)
    (((nonZeroDivisors (MvPolynomial τ K)).map (C (σ := σ))).map
      (quotientPolynomialSwap I).toMonoidHom)

@[simp] lemma scalarQuotientFractionMap_coordinate (i : σ) :
    scalarQuotientFractionMap (F := F) (τ := τ) (L := L) I
      (Ideal.Quotient.mk _ (X i)) =
      algebraMap (MvPolynomial τ (MvPolynomial σ K ⧸ I)) F
        (C (Ideal.Quotient.mk I (X i))) := by
  have h := RingHom.congr_fun (scalarQuotientFractionMap_comp (F := F) (τ := τ) (L := L) I)
    (C (Ideal.Quotient.mk I (X i)))
  simpa [scalarQuotientPolynomialMap,scalarCoordinateQuotientMap] using h

@[simp] lemma scalarQuotientFractionMap_parameter (j : τ) :
    scalarQuotientFractionMap (F := F) (τ := τ) (L := L) I
      (Ideal.Quotient.mk _ (C (algebraMap (MvPolynomial τ K) L (X j)))) =
      algebraMap (MvPolynomial τ (MvPolynomial σ K ⧸ I)) F (X j) := by
  have h := RingHom.congr_fun (scalarQuotientFractionMap_comp (F := F) (τ := τ) (L := L) I)
    (X j)
  simpa [scalarQuotientPolynomialMap] using h

end
end
end CCDN
