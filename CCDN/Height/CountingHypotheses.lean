/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Height.Box
public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Recurring hypotheses of the counting theorems

The determinant-method counting theorems are stated for a finite family of integral points and
an equation with bounded coefficients. These bundles name the recurring groups of hypotheses.

* `CCDN.IsBoxZeroFamily f B z`: the points `z i` are integral zeros of `f` in the box of
  radius `B ≥ 1`.
* `CCDN.IsPrimitiveBoxZeroFamily f B z`: moreover every `z i` is a primitive integer vector,
  that is, the reduced representative of a rational projective point.
* `CCDN.IsBoundedPlaneCurve F q d H`: the integral affine plane equation `q` has degree `d`, is
  irreducible over the field `F`, and has coefficients bounded by `H ≥ 1`.
* `CCDN.IsIndependentEvaluation f M F z`: the evaluation matrix `(F j (z i))` of forms of
  degree `M` at primitive integral zeros of `f` has linearly independent rows; this is the input
  of the determinant lower bounds.
* `CCDN.IsSmoothResidueFamily f P a x`: the points `x i` lie in prescribed nonsingular residue
  classes `a p` of `f` modulo the primes `p ∈ P`; this is the input of the congruence
  improvement of the determinant lower bound.
-/

@[expose] public section

namespace CCDN

open MvPolynomial

/-- The points `z i` are integral zeros of `f` lying in the box of radius `B ≥ 1`. -/
structure IsBoxZeroFamily {n : ℕ} {ι : Type*} (f : MvPolynomial (Fin n) ℤ) (B : ℝ)
    (z : ι → IntPoint n) : Prop where
  one_le_radius : 1 ≤ B
  eval_eq_zero : ∀ i, eval (z i) f = 0
  abs_le : ∀ i j, |(z i j : ℝ)| ≤ B

/-- The points `z i` are primitive integral zeros of `f` lying in the box of radius `B ≥ 1`;
for a form `f` these are the reduced representatives of rational projective zeros of `f`. -/
structure IsPrimitiveBoxZeroFamily {n : ℕ} {ι : Type*} (f : MvPolynomial (Fin n) ℤ) (B : ℝ)
    (z : ι → IntPoint n) : Prop extends IsBoxZeroFamily f B z where
  primitive : ∀ i, Finset.univ.gcd (z i) = 1

/-- The integral affine plane equation `q` has total degree `d`, is irreducible over the
field `F`, and all its coefficients are bounded in absolute value by `H ≥ 1`. -/
structure IsBoundedPlaneCurve (F : Type*) [Field F] (q : MvPolynomial (Fin 2) ℤ) (d : ℕ)
    (H : ℝ) : Prop where
  totalDegree_eq : q.totalDegree = d
  irreducible : Irreducible (map (Int.castRingHom F) q)
  one_le_height : 1 ≤ H
  coeff_le : ∀ m, |(q.coeff m : ℝ)| ≤ H

/-- The input of the determinant method: forms `F j` of degree `M`, primitive integral zeros
`z i` of `f`, and an evaluation matrix `(F j (z i))` whose rows are linearly independent over
`ℚ`, so that it has a nonzero maximal minor. -/
structure IsIndependentEvaluation {n s N : ℕ} (f : MvPolynomial (Fin n) ℤ) (M : ℕ)
    (F : Fin N → MvPolynomial (Fin n) ℤ) (z : Fin s → IntPoint n) : Prop where
  isHomogeneous : ∀ j, (F j).IsHomogeneous M
  primitive : ∀ i, Finset.univ.gcd (z i) = 1
  eval_eq_zero : ∀ i, eval (z i) f = 0
  rows_linearIndependent :
    LinearIndependent ℚ ((Matrix.of fun i j => eval (z i) (F j)).map ((↑) : ℤ → ℚ)).row

/-- The points `x i` lie in prescribed nonsingular residue classes of `f`: every `p ∈ P` is
prime, `a p` is a zero of `f` modulo `p` at which some partial derivative of `f` does not vanish
modulo `p`, and every `x i` is congruent to `a p` modulo `p`. -/
structure IsSmoothResidueFamily {n : ℕ} {ι : Type*} (f : MvPolynomial (Fin n) ℤ) (P : Finset ℕ)
    (a : ℕ → IntPoint n) (x : ι → IntPoint n) : Prop where
  prime : ∀ p ∈ P, p.Prime
  eval_eq_zero : ∀ p ∈ P, eval₂ (Int.castRingHom (ZMod p)) (fun j => (a p j : ZMod p)) f = 0
  smooth : ∀ p ∈ P, ∃ j, eval (fun i => (a p i : ZMod p))
    (pderiv j (map (Int.castRingHom (ZMod p)) f)) ≠ 0
  dvd_sub : ∀ p ∈ P, ∀ i j, (p : ℤ) ∣ x i j - a p j

end CCDN
