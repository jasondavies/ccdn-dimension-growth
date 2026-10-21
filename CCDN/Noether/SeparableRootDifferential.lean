/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Derivation.MapCoeffs
import Mathlib.Data.Nat.Totient
/-! Extend a differential structure to an explicitly separable monic root
extension in any characteristic. The construction is the implicit-derivative
quotient construction from Mathlib's characteristic-zero instance, with the
nonvanishing derivative supplied by separability. -/

@[expose] public section
namespace CCDN
noncomputable section
open Polynomial Differential
open scoped Differential

@[reducible]
def separableAdjoinRootDifferential {K : Type*} [Field K] [Differential K]
    (f : K[X]) [Fact (Irreducible f)] [Fact f.Monic] (hsep : f.Separable) :
    Differential (AdjoinRoot f) where
  deriv := Derivation.liftOfSurjective (f := (AdjoinRoot.mk f).toIntAlgHom) AdjoinRoot.mk_surjective
    (d := implicitDeriv <| AdjoinRoot.modByMonicHom Fact.out <|
      - (aeval (AdjoinRoot.root f) (Differential.mapCoeffs f)) /
        (aeval (AdjoinRoot.root f) f.derivative)) (by
      rintro x hx
      simp_all only [RingHom.toIntAlgHom_apply, AdjoinRoot.mk_eq_zero]
      obtain ⟨q, rfl⟩ := hx
      simp only [Derivation.leibniz, smul_eq_mul]
      apply dvd_add (dvd_mul_right ..)
      apply dvd_mul_of_dvd_right
      rw [← AdjoinRoot.mk_eq_zero]
      unfold implicitDeriv
      simp only [AdjoinRoot.aeval_eq, Derivation.coe_add, Derivation.coe_smul, Pi.add_apply,
        Pi.smul_apply, Derivation.restrictScalars_apply, derivative'_apply, smul_eq_mul, map_add,
        map_mul, AdjoinRoot.mk_leftInverse Fact.out _]
      rw [div_mul_cancel₀, add_neg_cancel]
      have hc : aeval (AdjoinRoot.root f) f = 0 := by
        rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
      simpa only [AdjoinRoot.aeval_eq] using hsep.aeval_derivative_ne_zero hc)

set_option backward.isDefEq.respectTransparency false in
theorem separableAdjoinRootDifferential_algebra {K : Type*} [Field K] [Differential K]
    (f : K[X]) [Fact (Irreducible f)] [Fact f.Monic] (hsep : f.Separable) :
    let := separableAdjoinRootDifferential f hsep
    DifferentialAlgebra K (AdjoinRoot f) := by
  dsimp only
  let := separableAdjoinRootDifferential f hsep
  refine { deriv_algebraMap := ?_ }
  intro a
  change (Derivation.liftOfSurjective _ _) ((AdjoinRoot.mk f).toIntAlgHom (C a)) = _
  rw [Derivation.liftOfSurjective_apply, implicitDeriv_C]
  rfl

end
end CCDN
