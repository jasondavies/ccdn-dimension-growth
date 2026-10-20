module

public import Mathlib
public import AffineCurveCounting

/-!
# Solution

The definitions are copied verbatim from `Challenge.lean`. Each compared theorem is
derived from the corresponding theorem of the `AffineCurveCounting` library. The bridging
lemmas identify the `Set.ncard` counts of the Challenge with the library's `Finset` counts;
every other definition agrees with its library counterpart definitionally.

| Challenge theorem | Library theorem |
| --- | --- |
| `projective_dimension_growth` | `AffineCurveCounting.projective_dimension_growth_cubic` |
| `projective_curve_bound` | `AffineCurveCounting.projectiveCurveBound` |
| `affine_curve_bound` | `AffineCurveCounting.affineCurveBound` |
| `affine_hypersurface_bound` | `AffineCurveCounting.top_form_hypersurface_dimension_growth_cubic` |
| `affine_hypersurface_bound_rat` | `AffineCurveCounting.rational_top_form_hypersurface_dimension_growth_cubic` |
| `projective_plane_curve_lower_bound` | `AffineCurveCounting.projective_integral_curve_lower_bound` |
| `classGroup_two_torsion_bound` | `AffineCurveCounting.classGroup_two_torsion_bound` |
-/

@[expose] public section

namespace CCDN

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

/-! ## Bridges to the library -/

theorem affineCount_eq {n : ℕ} (X : Set (Fin n → ℚ)) (B : ℝ) :
    affineCount X B = AffineCurveCounting.count X B := by
  classical
  unfold affineCount AffineCurveCounting.count
  rw [← Set.ncard_coe_finset]
  congr 1
  ext x
  exact AffineCurveCounting.mem_integralPoints.symm

theorem projectiveCount_eq {n : ℕ} (X : Set (Projectivization ℚ (Fin (n + 1) → ℚ))) (B : ℝ) :
    projectiveCount X B = AffineCurveCounting.projectiveCount X B := by
  classical
  unfold projectiveCount AffineCurveCounting.projectiveCount
  rw [← Set.ncard_coe_finset]
  congr 1
  ext x
  exact AffineCurveCounting.mem_projectivePoints.symm

/-! ## The counted sets are finite -/

theorem affineCount_set_finite {n : ℕ} (X : Set (Fin n → ℚ)) (B : ℝ) :
    {x : Fin n → ℤ | (∀ i, |(x i : ℝ)| ≤ B) ∧ (fun i => (x i : ℚ)) ∈ X}.Finite :=
  (AffineCurveCounting.integralPoints X B).finite_toSet.subset fun _ hx =>
    AffineCurveCounting.mem_integralPoints.mpr hx

theorem projectiveCount_set_finite {n : ℕ} (X : Set (Projectivization ℚ (Fin (n + 1) → ℚ)))
    (B : ℝ) :
    {x : Projectivization ℚ (Fin (n + 1) → ℚ) | x.mulHeight ≤ B ∧ x ∈ X}.Finite :=
  (AffineCurveCounting.projective_height_finite n B).subset fun _ hx => hx.1

/-! ## Main results -/

theorem projective_dimension_growth (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ I : Ideal (MvPolynomial (Fin (n + 1)) ℚ), I.IsPrime →
      (∀ f ∈ I, ∀ N, homogeneousComponent N f ∈ I) →
      ∀ d : ℕ, 5 ≤ d →
      ∀ P : Polynomial ℚ, IsAffineHilbertPolynomial I P →
      P.leadingCoeff = (d : ℚ) / P.natDegree.factorial →
      ∀ B : ℝ, 1 ≤ B →
      (projectiveCount (projectiveZeroSet I) B : ℝ) ≤
        C * (d : ℝ) ^ (2 * n ^ 3) * B ^ (P.natDegree - 1) := by
  obtain ⟨C, hC, h⟩ := AffineCurveCounting.projective_dimension_growth_cubic n
  refine ⟨C, hC, fun I hI hhom d hd P hP hlead B hB => ?_⟩
  have hPI : AffineCurveCounting.filteredHilbertPolynomial I = P := by
    obtain ⟨N, hN⟩ := hP
    exact AffineCurveCounting.filteredHilbertPolynomial_eq_of_eventual I P
      ⟨N, fun M hM => hN M hM⟩
  rw [projectiveCount_eq]
  have := h I hI hhom d hd (by rw [hPI]; exact hlead) B hB
  rwa [hPI] at this

theorem projective_curve_bound (n : ℕ) (hn : 2 ≤ n) :
    ∃ C : ℝ, 0 < C ∧
      ∀ I : Ideal (MvPolynomial (Fin (n + 1)) ℚ), I.IsPrime →
      ∀ d : ℕ, 0 < d → IsProjectiveCurveOfDegree I d →
      ∀ B : ℝ, 1 ≤ B →
      (projectiveCount (projectiveZeroSet I) B : ℝ) ≤
        C * ((d : ℝ) ^ 4 * B ^ (2 / (d : ℝ))) := by
  obtain ⟨C, hC, h⟩ := AffineCurveCounting.projectiveCurveBound n hn
  refine ⟨C, hC, fun I hI d hd hdeg B hB => ?_⟩
  rw [projectiveCount_eq]
  exact h I hI d hd hdeg B hB

theorem affine_curve_bound (n : ℕ) (hn : 2 ≤ n) :
    ∃ C : ℝ, 0 < C ∧
      ∀ I : Ideal (MvPolynomial (Fin n) ℚ), I.IsPrime →
      ∀ d : ℕ, 0 < d → IsAffineCurveOfDegree I d →
      ∀ B : ℝ, 1 ≤ B →
      (affineCount (affineZeroSet I) B : ℝ) ≤
        C * ((d : ℝ) ^ 3 * B ^ (1 / (d : ℝ)) * (Real.log B + d)) := by
  obtain ⟨C, hC, h⟩ := AffineCurveCounting.affineCurveBound n hn
  refine ⟨C, hC, fun I hI d hd hdeg B hB => ?_⟩
  rw [affineCount_eq]
  exact h I hI d hd hdeg B hB

theorem affine_hypersurface_bound (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ f : MvPolynomial (Fin (n + 3)) ℤ,
      Irreducible (map (Int.castRingHom (AlgebraicClosure ℚ))
        (homogeneousComponent f.totalDegree f)) →
      5 ≤ f.totalDegree → ∀ B : ℝ, 1 ≤ B →
      (affineCount {x | eval x (map (Int.castRingHom ℚ) f) = 0} B : ℝ) ≤
        C * (f.totalDegree : ℝ) ^ (18 + 3 * n) * B ^ (n + 1) := by
  obtain ⟨C, hC, h⟩ := AffineCurveCounting.top_form_hypersurface_dimension_growth_cubic n
  refine ⟨C, hC, fun f hf hd B hB => ?_⟩
  rw [affineCount_eq]
  exact h f hf hd B hB

theorem affine_hypersurface_bound_rat (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ f : MvPolynomial (Fin (n + 3)) ℚ,
      Irreducible (map (algebraMap ℚ (AlgebraicClosure ℚ))
        (homogeneousComponent f.totalDegree f)) →
      5 ≤ f.totalDegree → ∀ B : ℝ, 1 ≤ B →
      (affineCount {x | eval x f = 0} B : ℝ) ≤
        C * (f.totalDegree : ℝ) ^ (18 + 3 * n) * B ^ (n + 1) := by
  obtain ⟨C, hC, h⟩ := AffineCurveCounting.rational_top_form_hypersurface_dimension_growth_cubic n
  refine ⟨C, hC, fun f hf hd B hB => ?_⟩
  rw [affineCount_eq]
  exact h f hf hd B hB

theorem projective_plane_curve_lower_bound (d : ℕ) (hd : 0 < d) :
    ∃ F : MvPolynomial (Fin 3) ℚ, ∃ B : ℕ, 1 ≤ B ∧
      F.IsHomogeneous d ∧ F.totalDegree = d ∧
      Irreducible (map (algebraMap ℚ (AlgebraicClosure ℚ)) F) ∧
      (Ideal.span {F}).IsPrime ∧ IsProjectiveCurveOfDegree (Ideal.span {F}) d ∧
      ((d : ℝ) ^ 2 / 5) * (B : ℝ) ^ (2 / (d : ℝ)) ≤
        (projectiveCount (projectiveZeroSet (Ideal.span {F})) B : ℝ) := by
  obtain ⟨F, B, hB, hhom, hdeg, hir, hprime, hcurve, hcount⟩ :=
    AffineCurveCounting.projective_integral_curve_lower_bound d hd
  refine ⟨F, B, hB, hhom, hdeg, hir, hprime, hcurve, ?_⟩
  rw [projectiveCount_eq]
  exact hcount

theorem classGroup_two_torsion_bound (n : ℕ) (hn : 3 ≤ n) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (K : Type u) [Field K] [NumberField K], Module.finrank ℚ K = n →
        (Nat.card (powMonoidHom 2 : ClassGroup (𝓞 K) →* ClassGroup (𝓞 K)).ker : ℝ) ≤
          C * |(NumberField.discr K : ℝ)| ^ (1 / 2 - 1 / (2 * (n : ℝ))) *
            (Real.log |(NumberField.discr K : ℝ)|) ^ (1 - n % 2) :=
  AffineCurveCounting.classGroup_two_torsion_bound.{u} n hn

end CCDN
