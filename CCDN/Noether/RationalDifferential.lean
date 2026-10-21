/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.RingTheory.Derivation.DifferentialRing
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-! The formal derivative on a rational function field and its constant field. -/

@[expose] public section
namespace CCDN
noncomputable section
open Polynomial

variable {K : Type*} [Field K]

/-- Quotient-rule numerator and denominator for formal rational differentiation. -/
def rationalDerivativeFraction (p q : K[X]) : RatFunc K :=
  (algebraMap K[X] (RatFunc K) p.derivative * algebraMap K[X] (RatFunc K) q -
    algebraMap K[X] (RatFunc K) p * algebraMap K[X] (RatFunc K) q.derivative) /
      (algebraMap K[X] (RatFunc K) q) ^ 2

lemma rationalDerivativeFraction_mul {p q a : K[X]} (hq : q ≠ 0) (ha : a ≠ 0) :
    rationalDerivativeFraction (a * p) (a * q) = rationalDerivativeFraction p q := by
  simp only [rationalDerivativeFraction, derivative_mul, map_add, map_mul]
  field_simp [RatFunc.algebraMap_ne_zero hq, RatFunc.algebraMap_ne_zero ha]
  ring

/-- Formal rational differentiation, well-defined under changing fractions. -/
def rationalDerivative (x : RatFunc K) : RatFunc K :=
  x.liftOn' rationalDerivativeFraction (fun _hq _ha => rationalDerivativeFraction_mul _hq _ha)

private lemma rationalDerivative_div (p q : K[X]) :
    rationalDerivative (algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) q) =
      rationalDerivativeFraction p q := by
  rw [rationalDerivative, RatFunc.liftOn'_div]
  intro p
  simp [rationalDerivativeFraction]

lemma rationalDerivative_polynomial (p : K[X]) :
    rationalDerivative (algebraMap K[X] (RatFunc K) p) =
      algebraMap K[X] (RatFunc K) p.derivative := by
  simpa [rationalDerivativeFraction] using rationalDerivative_div p 1

lemma rationalDerivative_add (x y : RatFunc K) :
    rationalDerivative (x + y) = rationalDerivative x + rationalDerivative y := by
  induction x using RatFunc.induction_on with | _ p q hq
  induction y using RatFunc.induction_on with | _ r s hs
  have hq' := RatFunc.algebraMap_ne_zero hq
  have hs' := RatFunc.algebraMap_ne_zero hs
  rw [div_add_div _ _ hq' hs', ← map_mul, ← map_mul, ← map_add, ← map_mul,
    rationalDerivative_div, rationalDerivative_div, rationalDerivative_div]
  simp only [rationalDerivativeFraction, derivative_mul, map_add, map_mul]
  field_simp
  ring

lemma rationalDerivative_mul (x y : RatFunc K) :
    rationalDerivative (x * y) = x * rationalDerivative y + y * rationalDerivative x := by
  induction x using RatFunc.induction_on with | _ p q hq
  induction y using RatFunc.induction_on with | _ r s hs
  rw [div_mul_div_comm, ← map_mul, ← map_mul,
    rationalDerivative_div, rationalDerivative_div, rationalDerivative_div]
  simp only [rationalDerivativeFraction, derivative_mul, map_add, map_mul]
  field_simp
  ring

/-- Rational formal differentiation as a derivation over the coefficient field. -/
def rationalDerivation (K : Type*) [Field K] : Derivation K (RatFunc K) (RatFunc K) where
  toFun := rationalDerivative
  map_add' := rationalDerivative_add
  map_smul' c x := by
    rw [Algebra.smul_def, rationalDerivative_mul, Algebra.smul_def]
    have hc : rationalDerivative (algebraMap K (RatFunc K) c) = 0 := by
      rw [IsScalarTower.algebraMap_apply K K[X] (RatFunc K), rationalDerivative_polynomial]
      simp
    simp only [hc, mul_zero, add_zero, RingHom.id_apply]
  map_one_eq_zero' := by
    simpa using rationalDerivative_polynomial (1 : K[X])
  leibniz' x y := rationalDerivative_mul x y

/-- The corresponding differential field structure; it is kept explicit to
avoid introducing a competing global instance on rational functions. -/
@[reducible]
def rationalDifferential (K : Type*) [Field K] : Differential (RatFunc K) := by
  let : Algebra ℤ (RatFunc K) := Ring.toIntAlgebra _
  exact ⟨(rationalDerivation K).restrictScalars ℤ⟩

end
end CCDN
