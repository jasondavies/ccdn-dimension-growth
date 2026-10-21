/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib

/-!
# Challenge: dimension growth, polynomial in the degree (CCDN)

This file is the human-auditable statement surface. It imports only Mathlib. Each
compared theorem below is stated with `sorry`; `Solution.lean` restates the same
definitions verbatim and proves the same statements from the `CCDN`
library.

Source: W. Castryck, R. Cluckers, P. Dittmann and K. H. Nguyen, *The dimension growth
conjecture, polynomial in the degree and without logarithmic factors*, Algebra & Number
Theory 14 (2020) 2261–2294, arXiv:1904.13109, with the authors' list of addenda dated
2026-04-20. "Theorem k" and "Proposition 5" refer to the numbering of that paper.

## Conventions

* Varieties are given by their ideals over `ℚ`. An integral variety is a prime ideal; the
  ideal is not assumed to be geometrically prime, so varieties that split over `ℚ̄` are
  included.
* Degree and dimension are read off the coordinate ring's Hilbert function. Varieties are
  not identified with Mathlib `Scheme`s.
* `affineCount X B` counts integer points `x ∈ ℤⁿ` with `max |xᵢ| ≤ B` and `x ∈ X`.
  `projectiveCount X B` counts points of `X ⊆ ℙⁿ(ℚ)` with multiplicative height at most `B`.
  On a point with coprime integer coordinates, Mathlib's height is `max |xᵢ|`
  (`Rat.mulHeight_eq_max_abs_of_gcd_eq_one`), which is CCDN's height `H`.
* Both counts are `Set.ncard`s. The sets are finite (`affineCount_set_finite`,
  `projectiveCount_set_finite`), so `ncard` is the true cardinality, not a junk value `0`.
* Every constant `C` depends only on the ambient dimension `n`. It is chosen before the
  variety, its degree and the radius `B`.
-/

@[expose] public section

namespace CCDN.Submission

open MvPolynomial
open scoped NumberField

universe u

/-! ## Counting functions -/

/-- `N_aff(X, B)`: the number of integer points `x ∈ ℤⁿ` with `|xᵢ| ≤ B` for every `i`
whose image in `ℚⁿ` lies in `X`. -/
noncomputable def affineCount {n : ℕ} (X : Set (Fin n → ℚ)) (B : ℝ) : ℕ :=
  {x : Fin n → ℤ | (∀ i, |(x i : ℝ)| ≤ B) ∧ (fun i => (x i : ℚ)) ∈ X}.ncard

/-- `N(X, B)`: the number of rational points of `X ⊆ ℙⁿ(ℚ)` whose multiplicative height is
at most `B`, each projective point counted once. -/
noncomputable def projectiveCount {n : ℕ} (X : Set (Projectivization ℚ (Fin (n + 1) → ℚ)))
    (B : ℝ) : ℕ :=
  {x : Projectivization ℚ (Fin (n + 1) → ℚ) | x.mulHeight ≤ B ∧ x ∈ X}.ncard

/-- The affine zero set `V(I) ⊆ 𝔸ⁿ(ℚ)` of an ideal `I ⊆ ℚ[x₁,…,xₙ]`. -/
def affineZeroSet {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℚ)) : Set (Fin n → ℚ) :=
  {x | ∀ f ∈ I, eval x f = 0}

/-- The projective zero set `V(I) ⊆ ℙⁿ(ℚ)` of an ideal `I ⊆ ℚ[x₀,…,xₙ]`. A point lies in it
when every representative vector annihilates `I`. For a homogeneous ideal this is the usual
projective zero set. -/
def projectiveZeroSet {n : ℕ} (I : Ideal (MvPolynomial (Fin (n + 1)) ℚ)) :
    Set (Projectivization ℚ (Fin (n + 1) → ℚ)) :=
  {x | ∀ (v : Fin (n + 1) → ℚ) (hv : v ≠ 0), Projectivization.mk ℚ v hv = x →
    ∀ f ∈ I, eval v f = 0}

/-! ## Hilbert functions, degree and dimension -/

/-- The affine Hilbert function `M ↦ dim_ℚ` of the image in `ℚ[x₁,…,xₙ]/I` of the
polynomials of total degree at most `M`. -/
noncomputable def affineHilbertFunction {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℚ))
    (M : ℕ) : ℕ :=
  Module.finrank ℚ ((restrictTotalDegree (Fin n) ℚ M).map (Ideal.Quotient.mkₐ ℚ I).toLinearMap)

/-- The homogeneous Hilbert function `M ↦ dim_ℚ` of the image in `ℚ[x₀,…,xₙ]/I` of the
homogeneous polynomials of degree `M`. -/
noncomputable def projectiveHilbertFunction {n : ℕ} (I : Ideal (MvPolynomial (Fin (n + 1)) ℚ))
    (M : ℕ) : ℕ :=
  Module.finrank ℚ
    ((homogeneousSubmodule (Fin (n + 1)) ℚ M).map (Ideal.Quotient.mkₐ ℚ I).toLinearMap)

/-- `I` defines an affine curve of degree `d`: its affine Hilbert function is eventually
`d * M + c`. -/
def IsAffineCurveOfDegree {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℚ)) (d : ℕ) : Prop :=
  ∃ N : ℕ, ∃ c : ℤ, ∀ M : ℕ, N ≤ M → (affineHilbertFunction I M : ℤ) = (d : ℤ) * M + c

/-- `I` defines a projective curve of degree `d`: its homogeneous Hilbert function is
eventually `d * M + c`. -/
def IsProjectiveCurveOfDegree {n : ℕ} (I : Ideal (MvPolynomial (Fin (n + 1)) ℚ)) (d : ℕ) :
    Prop :=
  ∃ N : ℕ, ∃ c : ℤ, ∀ M : ℕ, N ≤ M → (projectiveHilbertFunction I M : ℤ) = (d : ℤ) * M + c

/-- `P` is the affine Hilbert polynomial of `I`: it agrees with `affineHilbertFunction I`
at all sufficiently large integers. -/
def IsAffineHilbertPolynomial {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℚ))
    (P : Polynomial ℚ) : Prop :=
  ∃ N : ℕ, ∀ M : ℕ, N ≤ M → P.eval (M : ℚ) = affineHilbertFunction I M

/-! ## The counted sets are finite -/

/-- The set counted by `affineCount` is finite. -/
theorem affineCount_set_finite {n : ℕ} (X : Set (Fin n → ℚ)) (B : ℝ) :
    {x : Fin n → ℤ | (∀ i, |(x i : ℝ)| ≤ B) ∧ (fun i => (x i : ℚ)) ∈ X}.Finite := by
  sorry

/-- The set counted by `projectiveCount` is finite (Northcott). -/
theorem projectiveCount_set_finite {n : ℕ} (X : Set (Projectivization ℚ (Fin (n + 1) → ℚ)))
    (B : ℝ) :
    {x : Projectivization ℚ (Fin (n + 1) → ℚ) | x.mulHeight ≤ B ∧ x ∈ X}.Finite := by
  sorry

/-! ## Main results -/

/-- **Theorem 1** (projective dimension growth, polynomial in the degree). Let
`X ⊆ ℙⁿ` be an integral projective variety over `ℚ` with homogeneous prime ideal `I`, degree
`d ≥ 5` and dimension `m`. Then `N(X, B) ≤ C(n) d^(2n² + 5n − 5) B^m` for all `B ≥ 1`.

The affine Hilbert polynomial `P` of the cone `ℚ[x₀,…,xₙ]/I` has degree `m + 1` and leading
coefficient `d / (m + 1)!`. The two hypotheses on `P` therefore say that `X` has degree `d`,
and `P.natDegree - 1 = m`. The paper's degree exponent `e(n)` is made explicit as
`2n² + 5n − 5`, with natural-number subtraction (the exponent is `0` for `n = 0`).
The statement also covers `n ≤ 1` and the empty and zero-dimensional cases. -/
theorem projective_dimension_growth (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ I : Ideal (MvPolynomial (Fin (n + 1)) ℚ), I.IsPrime →
      (∀ f ∈ I, ∀ N, homogeneousComponent N f ∈ I) →
      ∀ d : ℕ, 5 ≤ d →
      ∀ P : Polynomial ℚ, IsAffineHilbertPolynomial I P →
      P.leadingCoeff = (d : ℚ) / P.natDegree.factorial →
      ∀ B : ℝ, 1 ≤ B →
      (projectiveCount (projectiveZeroSet I) B : ℝ) ≤
        C * (d : ℝ) ^ (2 * n ^ 2 + 5 * n - 5) * B ^ (P.natDegree - 1) := by
  sorry

/-- **Theorem 2** (projective curves). For `n ≥ 2`, every integral projective curve
`X ⊆ ℙⁿ` over `ℚ` of degree `d ≥ 1` satisfies `N(X, B) ≤ C(n) d⁴ B^(2/d)` for all
`B ≥ 1`. The ideal is not required to be homogeneous. -/
theorem projective_curve_bound (n : ℕ) (hn : 2 ≤ n) :
    ∃ C : ℝ, 0 < C ∧
      ∀ I : Ideal (MvPolynomial (Fin (n + 1)) ℚ), I.IsPrime →
      ∀ d : ℕ, 0 < d → IsProjectiveCurveOfDegree I d →
      ∀ B : ℝ, 1 ≤ B →
      (projectiveCount (projectiveZeroSet I) B : ℝ) ≤
        C * ((d : ℝ) ^ 4 * B ^ (2 / (d : ℝ))) := by
  sorry

/-- **Theorem 3** (affine curves). For `n ≥ 2`, every integral affine curve `X ⊆ 𝔸ⁿ` over
`ℚ` of degree `d ≥ 1` satisfies `N_aff(X, B) ≤ C(n) d³ B^(1/d) (log B + d)` for every real
`B ≥ 1`. -/
theorem affine_curve_bound (n : ℕ) (hn : 2 ≤ n) :
    ∃ C : ℝ, 0 < C ∧
      ∀ I : Ideal (MvPolynomial (Fin n) ℚ), I.IsPrime →
      ∀ d : ℕ, 0 < d → IsAffineCurveOfDegree I d →
      ∀ B : ℝ, 1 ≤ B →
      (affineCount (affineZeroSet I) B : ℝ) ≤
        C * ((d : ℝ) ^ 3 * B ^ (1 / (d : ℝ)) * (Real.log B + d)) := by
  sorry

/-- **Theorem 4** (affine hypersurfaces), for integer equations in `N = n + 3 ≥ 3`
variables. Let `f ∈ ℤ[x₁,…,x_N]` have degree `d ≥ 5`, and let its top-degree homogeneous
part be irreducible over `ℚ̄`. Then `N_aff(V(f), B) ≤ C(N) d^(18+3n) B^(N-2)`.

The paper leaves the exponent `e(N)` unspecified after the addenda's corrections. It is made
explicit here as `18 + 3n = 3N + 9`. -/
theorem affine_hypersurface_bound (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ f : MvPolynomial (Fin (n + 3)) ℤ,
      Irreducible (map (Int.castRingHom (AlgebraicClosure ℚ))
        (homogeneousComponent f.totalDegree f)) →
      5 ≤ f.totalDegree → ∀ B : ℝ, 1 ≤ B →
      (affineCount {x | eval x (map (Int.castRingHom ℚ) f) = 0} B : ℝ) ≤
        C * (f.totalDegree : ℝ) ^ (18 + 3 * n) * B ^ (n + 1) := by
  sorry

/-- **Theorem 4**, for rational equations, with the same constant shape as
`affine_hypersurface_bound`. -/
theorem affine_hypersurface_bound_rat (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ f : MvPolynomial (Fin (n + 3)) ℚ,
      Irreducible (map (algebraMap ℚ (AlgebraicClosure ℚ))
        (homogeneousComponent f.totalDegree f)) →
      5 ≤ f.totalDegree → ∀ B : ℝ, 1 ≤ B →
      (affineCount {x | eval x f = 0} B : ℝ) ≤
        C * (f.totalDegree : ℝ) ^ (18 + 3 * n) * B ^ (n + 1) := by
  sorry

/-- **Proposition 5** (lower bound for Theorem 2). For every `d ≥ 1` there is an
integral projective plane curve `X = V(F) ⊆ ℙ²` over `ℚ` of degree `d`, with `F` irreducible
over `ℚ̄`, and an integer `B ≥ 1` with `N(X, B) ≥ d² B^(2/d) / 5`. Hence the factor `d⁴` in
Theorem 2 cannot be replaced by anything in `o(d²)`. Its degree is checked both as the total
degree of `F` and by the homogeneous Hilbert function. -/
theorem projective_plane_curve_lower_bound (d : ℕ) (hd : 0 < d) :
    ∃ F : MvPolynomial (Fin 3) ℚ, ∃ B : ℕ, 1 ≤ B ∧
      F.IsHomogeneous d ∧ F.totalDegree = d ∧
      Irreducible (map (algebraMap ℚ (AlgebraicClosure ℚ)) F) ∧
      (Ideal.span {F}).IsPrime ∧ IsProjectiveCurveOfDegree (Ideal.span {F}) d ∧
      ((d : ℝ) ^ 2 / 5) * (B : ℝ) ^ (2 / (d : ℝ)) ≤
        (projectiveCount (projectiveZeroSet (Ideal.span {F})) B : ℝ) := by
  sorry

/-- **Theorem 6** (2-torsion in class groups). For every `n ≥ 3` there is `C(n) > 0` such
that every number field `K` of degree `n` satisfies
`h₂(K) ≤ C(n) |disc K|^(1/2 - 1/(2n)) (log |disc K|)^(1 - n % 2)`. Here `h₂(K)` is the
order of the `2`-torsion subgroup of the class group of `𝓞 K`. The logarithm appears only
for even `n`. -/
theorem classGroup_two_torsion_bound (n : ℕ) (hn : 3 ≤ n) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (K : Type u) [Field K] [NumberField K], Module.finrank ℚ K = n →
        (Nat.card (powMonoidHom 2 : ClassGroup (𝓞 K) →* ClassGroup (𝓞 K)).ker : ℝ) ≤
          C * |(NumberField.discr K : ℝ)| ^ (1 / 2 - 1 / (2 * (n : ℝ))) *
            (Real.log |(NumberField.discr K : ℝ)|) ^ (1 - n % 2) := by
  sorry

end CCDN.Submission
