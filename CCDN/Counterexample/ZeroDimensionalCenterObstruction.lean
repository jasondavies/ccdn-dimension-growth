/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.PolynomialPredicates
public import CCDN.Algebra.ProjectiveSection
public import CCDN.Curve.Curve
public import CCDN.Height.ProjectiveBox
public import CCDN.Hilbert.FilteredHilbertPolynomial
import CCDN.Counterexample.OriginProjectivePoint
/-! The strict degree bound in the literal CCDN Lemma 5.2 fails at
dimension zero and degree one. A point in P² is a geometrically integral
degree-one variety; its point centers cannot include that point. Any
nonempty set of good centers therefore has a nonempty proper complement,
which cannot be cut out by polynomials of degree strictly below one. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Maximal minors for the one-row matrix representing a point center. -/
def pointCenterPluckerCoordinates {K : Type*} [Field K] {n : ℕ}
    (p : Projectivization K (Fin (n + 1) → K)) : (Fin 1 ↪ Fin (n + 1)) → K :=
  fun c => Matrix.det (Matrix.submatrix (fun (_ : Fin 1) j => p.rep j) id c)

lemma totalDegree_zero_eval_constant {K σ : Type*} [Field K]
    (f : MvPolynomial σ K) (hf : f.totalDegree = 0) (a b : σ → K) :
    eval a f = eval b f := by
  rw [(totalDegree_eq_zero_iff_eq_C).mp hf]
  simp only [eval_C]

/-- Lemma 5.2's strict degree bound fails for `m = 0`: there is a geometrically integral
rational point `X ⊂ ℙ²` such that, for every nonempty set `G` of points off `X`, the
complement of `G` is not the common zero set of polynomials of degree `< (0+1)²·1² = 1` in the
Plücker (maximal-minor) coordinates. -/
theorem zero_dimensional_plucker_degree_bound_obstruction :
    ∃ I : Ideal (CoordinatePolynomial 3), I.IsPrime ∧
      IsHomogeneousIdeal I ∧
      (I.map (map (algebraMap ℚ (AlgebraicClosure ℚ)))).IsPrime ∧
      (filteredHilbertPolynomial I).natDegree = 1 ∧
      (filteredHilbertPolynomial I).leadingCoeff = 1 ∧
      ∀ G : Set (ProjectivePoint 2), G.Nonempty →
        (∀ p ∈ G, p ∉ projectiveIdealZeroLocus I) →
        ¬ ∃ S : Set (MvPolynomial (Fin 1 ↪ Fin 3) ℚ),
          (∀ f ∈ S, f.totalDegree < (0 + 1) ^ 2 * 1 ^ 2) ∧
          ∀ p, p ∉ G ↔ ∀ f ∈ S, eval (pointCenterPluckerCoordinates p) f = 0 := by
  refine ⟨originProjectiveIdeal ℚ 2, inferInstance,
    projectiveClosureIdeal_homogeneous _,
    originProjectiveIdeal_geometrically_prime 2,
    (originProjectiveIdeal_hilbert_parameters 2).1,
    (originProjectiveIdeal_hilbert_parameters 2).2, ?_⟩
  intro G hG hdisjoint S
  obtain ⟨p,hp⟩ := hG
  let q : ProjectivePoint 2 := affineProjectivePoint (0 : Fin 2 → ℚ)
  have hq : q ∉ G := by
    intro h
    exact hdisjoint q h ((originProjectiveIdeal_chart_point 0).mpr rfl)
  obtain ⟨S,hdeg,hcut⟩ := S
  apply ((hcut p).mpr ?_) hp
  intro f hf
  rw [totalDegree_zero_eval_constant f (by have := hdeg f hf; norm_num at this; omega)
    (pointCenterPluckerCoordinates p) (pointCenterPluckerCoordinates q)]
  exact (hcut q).mp hq f hf

end
end CCDN
