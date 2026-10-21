/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.ProjectiveClosureIdeal
public import CCDN.Hilbert.FilteredHilbertPolynomial
public import CCDN.Projection.ProjectivePlaneProjection
public import Mathlib.RingTheory.MvPolynomial.Ideal
import CCDN.Algebra.ProjectiveClosureDegree
import CCDN.Determinant.HypersurfaceOriginStalk
import CCDN.Hilbert.ProjectiveClosureHilbertPolynomial

/-! The projective closure of the affine origin is geometrically
prime and has projective dimension zero and degree one. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Extending scalars along a field extension `K → L` maps the ideal of the origin over `K` to the
ideal of the origin over `L`. -/
lemma idealOfVars_scalar_extension {K L σ : Type*}
    [Field K] [Field L] [Algebra K L] :
    (idealOfVars σ K).map (map (algebraMap K L)) = idealOfVars σ L := by
  rw [idealOfVars, Ideal.map_span]
  congr 1
  ext f
  simp only [Set.mem_image, Set.mem_range]
  constructor
  · rintro ⟨_, ⟨i,rfl⟩,rfl⟩
    exact ⟨i,(map_X _ _).symm⟩
  · rintro ⟨i,rfl⟩
    exact ⟨X i,⟨i,rfl⟩,map_X _ _⟩

/-- For every `N`, the image of the polynomials of total degree at most `N` in the coordinate ring
`K[X] ⧸ (X_i)` of the origin has `K`-dimension `1`. -/
theorem idealOfVars_filtered_finrank {K σ : Type*}
    [Field K] [Fintype σ] (N : ℕ) :
    Module.finrank K (filteredCoordinateSpace (idealOfVars σ K) N) = 1 := by
  let I := idealOfVars σ K
  have heval : RingHom.ker (aeval (0 : σ → K)) = I := by
    change RingHom.ker (aeval (0 : σ → K)) = idealOfVars σ K
    rw [idealOfVars_eq_ker_constantCoeff]
    ext f
    simp only [RingHom.mem_ker, aeval_zero,
      Algebra.algebraMap_self, RingHom.id_apply]
  let e := Ideal.quotientKerAlgEquivOfSurjective
    (f := aeval (0 : σ → K)) (fun c => ⟨C c, by simp⟩)
  have htop : filteredCoordinateSpace I N = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨f,rfl⟩ := Ideal.Quotient.mk_surjective x
    refine Submodule.mem_map.mpr ⟨C (constantCoeff f), ?_, ?_⟩
    · exact (mem_restrictTotalDegree _ _ _).mpr (by simp)
    · apply Ideal.Quotient.eq.mpr
      rw [show I = RingHom.ker constantCoeff from idealOfVars_eq_ker_constantCoeff]
      change constantCoeff (C (constantCoeff f) - f) = 0
      simp
  rw [htop, finrank_top]
  let e' := (Ideal.quotientEquivAlgOfEq K heval.symm).trans e
  simpa using e'.toLinearEquiv.finrank_eq

/-- The filtered Hilbert polynomial of the ideal of the origin is the constant `1`. -/
theorem idealOfVars_filteredHilbertPolynomial {K σ : Type*}
    [Field K] [Fintype σ] [LinearOrder σ] :
    filteredHilbertPolynomial (idealOfVars σ K) = 1 := by
  apply filteredHilbertPolynomial_eq_of_eventual
  exact ⟨0, fun N _ => by rw [idealOfVars_filtered_finrank]; simp⟩

/-- The homogeneous ideal in `K[X₀, …, Xₙ]` of the projective closure of the affine origin, that is,
of the point `[1 : 0 : ⋯ : 0]`; used in the counterexample to the degree bound of CCDN Lemma 5.2 in
dimension zero. -/
def originProjectiveIdeal (K : Type*) [Field K] (n : ℕ) :
    Ideal (MvPolynomial (Fin (n + 1)) K) :=
  projectiveClosureIdeal (idealOfVars (Fin n) K)

instance originProjectiveIdeal_isPrime {K : Type*} [Field K] {n : ℕ} :
    (originProjectiveIdeal K n).IsPrime := by
  have : (idealOfVars (Fin n) K).IsPrime := idealOfVars_isMaximal.isPrime
  exact projectiveClosureIdeal_isPrime _

/-- The ideal of the projective closure of the origin stays prime after extending scalars to any
field extension `L` of `K`, so the point is geometrically integral. -/
theorem originProjectiveIdeal_geometrically_prime {K L : Type*}
    [Field K] [Field L] [Algebra K L] (n : ℕ) :
    ((originProjectiveIdeal K n).map (map (algebraMap K L))).IsPrime := by
  unfold originProjectiveIdeal
  rw [projectiveClosureIdeal_scalar_extension, idealOfVars_scalar_extension]
  exact originProjectiveIdeal_isPrime

/-- The filtered Hilbert polynomial of the projective closure of the origin has degree `1` and
leading coefficient `1`: the point has projective dimension zero and degree one. -/
theorem originProjectiveIdeal_hilbert_parameters {K : Type*} [Field K] (n : ℕ) :
    (filteredHilbertPolynomial (originProjectiveIdeal K n)).natDegree = 1 ∧
      (filteredHilbertPolynomial (originProjectiveIdeal K n)).leadingCoeff = 1 := by
  have : (idealOfVars (Fin n) K).IsPrime := idealOfVars_isMaximal.isPrime
  have h := projectiveClosureIdeal_hilbertPolynomial_parameters (idealOfVars (Fin n) K) 0 1
    ⟨by rw [idealOfVars_filteredHilbertPolynomial]; simp,
      by rw [idealOfVars_filteredHilbertPolynomial]; simp⟩
  simpa [originProjectiveIdeal] using And.intro h.natDegree_eq h.leadingCoeff_eq

/-- A point of the standard affine chart lies on the projective closure of the origin if and only if
it is the origin. -/
theorem originProjectiveIdeal_chart_point {K : Type*} [Field K] {n : ℕ}
    (a : Fin n → K) :
    affineProjectivePoint a ∈ projectiveIdealZeroLocus (originProjectiveIdeal K n) ↔ a = 0 := by
  rw [originProjectiveIdeal, projectiveClosureIdeal_chart_point]
  constructor
  · intro h
    funext i
    simpa only [eval_X, Pi.zero_apply] using
      h (X i) (Ideal.subset_span ⟨i,rfl⟩)
  · rintro rfl f hf
    rw [idealOfVars_eq_ker_constantCoeff] at hf
    simpa only [eval_zero, RingHom.mem_ker] using hf

end
end CCDN
