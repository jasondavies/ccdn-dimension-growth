/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Hypersurface.GoodHyperplaneBounds
public import CCDN.Hypersurface.IntegerHyperplaneSlices
public import CCDN.Plane.Plane
public import CCDN.Algebra.PolynomialPredicates
/-! Coordinate transport between the graph-hyperplane construction and
the finite integral-point count. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

lemma integer_top_irreducible_rename {σ τ : Type*} (e : σ ≃ τ)
    (f : MvPolynomial σ ℤ)
    (hir : HasAbsIrreducibleTopForm f) :
    Irreducible (map (Int.castRingHom (AlgebraicClosure ℚ))
      (homogeneousComponent (rename e f).totalDegree (rename e f))) := by
  rw [show (rename e f).totalDegree = f.totalDegree from totalDegree_renameEquiv e f,
    ← rename_homogeneousComponent, map_rename]
  exact (MulEquiv.irreducible_iff (f := renameEquiv _ e)).mpr hir

def graphIntegerNormal {n : ℕ} (D : ℤ) (a : Fin n → ℤ) : IntPoint (n + 1) :=
  Fin.cons D (fun i => -a i)

lemma graphIntegerNormal_height {n : ℕ} (D : ℤ) (a : Fin n → ℤ) {H : ℕ}
    (hD : |D| ≤ (H : ℤ)) (ha : ∀ i, |a i| ≤ (H : ℤ)) :
    ∀ i, |(graphIntegerNormal D a i : ℝ)| ≤ (H : ℝ) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact_mod_cast hD
  · simpa only [graphIntegerNormal, Fin.cons_succ, Int.cast_neg, abs_neg] using
      (show |(a j : ℝ)| ≤ (H : ℝ) by exact_mod_cast ha j)

/-- Integral equations suffice for the rational zero-locus map used by
the count: the only coordinate change is deleting coordinate zero. -/
theorem integer_slice_map_of_option_equations {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) ℤ) (D : ℤ) (a : Fin n → ℤ)
    (g : ℤ → MvPolynomial (Fin n) ℤ)
    (hslice : ∀ k (x : Option (Fin n) → ℤ),
      D * x none - ∑ i, a i * x (some i) = k →
      eval x (rename (finSuccEquiv' 0) f) = 0 →
      eval (fun i => x (some i)) (g k) = 0)
    (B : ℝ) (k : ℤ) (x : IntPoint (n + 1))
    (hx : x ∈ integerSlicePoints (zeroLocus (map (Int.castRingHom ℚ) f))
      B (graphIntegerNormal D a) k) :
    rationalPoint (deleteIntegerCoordinate 0 x) ∈
      zeroLocus (map (Int.castRingHom ℚ) (g k)) := by
  classical
  let e : Fin (n + 1) ≃ Option (Fin n) := finSuccEquiv' 0
  let z : Option (Fin n) → ℤ := x ∘ e.symm
  have hznone : z none = x 0 := by simp [z, e]
  have hzsome (i : Fin n) : z (some i) = deleteIntegerCoordinate 0 x i := by
    simp [z, e, deleteIntegerCoordinate]
  have hlevel := (Finset.mem_filter.mp hx).2
  have hzlevel : D * z none - ∑ i, a i * z (some i) = k := by
    change (∑ i, graphIntegerNormal D a i * x i) = k at hlevel
    rw [Fin.sum_univ_succ] at hlevel
    simp only [graphIntegerNormal, Fin.cons_zero, Fin.cons_succ, neg_mul,
      Finset.sum_neg_distrib] at hlevel
    simpa [hznone, hzsome, deleteIntegerCoordinate, sub_eq_add_neg] using hlevel
  have hfxQ : eval (rationalPoint x) (map (Int.castRingHom ℚ) f) = 0 :=
    (mem_integralPoints.mp (Finset.mem_filter.mp hx).1).2
  have hfxZ : eval x f = 0 := by
    have he : ((eval x f : ℤ) : ℚ) =
        eval (rationalPoint x) (map (Int.castRingHom ℚ) f) := by
      exact map_eval (Int.castRingHom ℚ) x f
    exact Int.cast_injective (he.trans hfxQ)
  have hz : eval z (rename e f) = 0 := by
    rw [eval_rename]
    simpa only [z, Function.comp_def, Equiv.symm_apply_apply] using hfxZ
  have hgZ := hslice k z hzlevel hz
  change eval (rationalPoint (deleteIntegerCoordinate 0 x))
    (map (Int.castRingHom ℚ) (g k)) = 0
  have he : eval (rationalPoint (deleteIntegerCoordinate 0 x))
      (map (Int.castRingHom ℚ) (g k)) =
      ((eval (fun i => z (some i)) (g k) : ℤ) : ℚ) := by
    change eval (fun i => (deleteIntegerCoordinate 0 x i : ℚ))
      (map (Int.castRingHom ℚ) (g k)) = _
    simpa only [Function.comp_def, Int.coe_castRingHom, hzsome] using
      (map_eval (Int.castRingHom ℚ) (fun i => z (some i)) (g k)).symm
  rw [he, hgZ, Int.cast_zero]

end
end CCDN
