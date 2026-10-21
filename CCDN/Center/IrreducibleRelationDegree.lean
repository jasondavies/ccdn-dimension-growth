/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Polynomial.GaussLemma
/-! An irreducible polynomial relation over a polynomial coefficient ring
becomes the minimal polynomial, up to a nonzero scalar, over its
fraction field. -/

@[expose] public section
namespace CCDN
noncomputable section

theorem irreducible_relation_minpoly_degree
    {K R F σ : Type*} [Field K] [Field R] [Field F]
    [Algebra (MvPolynomial σ K) R] [IsFractionRing (MvPolynomial σ K) R]
    [Algebra R F] [Algebra (MvPolynomial σ K) F]
    [IsScalarTower (MvPolynomial σ K) R F]
    (p : Polynomial (MvPolynomial σ K)) (hp : Irreducible p)
    (hpos : 0 < p.natDegree) (z : F)
    (hz : p.eval₂ (algebraMap (MvPolynomial σ K) F) z = 0) :
    (minpoly R z).natDegree = p.natDegree := by
  have hprim : p.IsPrimitive := hp.isPrimitive (Nat.ne_zero_of_lt hpos)
  let q := p.map (algebraMap (MvPolynomial σ K) R)
  have hq : Irreducible q := hprim.irreducible_iff_irreducible_map_fraction_map.mp hp
  have hroot : Polynomial.aeval z q = 0 := by
    change (p.map (algebraMap (MvPolynomial σ K) R)).eval₂ (algebraMap R F) z = 0
    rw [Polynomial.eval₂_map,← IsScalarTower.algebraMap_eq]
    exact hz
  rw [← minpoly.eq_of_irreducible hq hroot,
    Polynomial.natDegree_mul_C_of_isUnit (isUnit_iff_ne_zero.mpr
      (inv_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hq.ne_zero)))]
  exact Polynomial.natDegree_map_eq_of_injective
    (IsFractionRing.injective (MvPolynomial σ K) R) p

end
end CCDN
