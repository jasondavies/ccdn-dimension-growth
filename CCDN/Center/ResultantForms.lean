/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Center.GenericBlockLine
public import CCDN.Center.MinorMatrix
public import CCDN.Center.ResultantCoefficientFamily
public import CCDN.Center.UniversalCenterChowRestriction
import CCDN.Center.GenericBlockLineHomogeneity

/-! A derivative-resultant family for one hyperplane block of the
universal center restriction. The Pluecker degree is D(2d-1). -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Matrix

/-- The selector of the hyperplane-coefficient variables `(i, j)` in the `i`-th row. -/
def chowRowBlock {q s : ℕ} (i : Fin q) : Fin q × Fin s → Bool :=
  fun p => decide (p.1 = i)

/-- The block weight of the `i`-th row selector `chowRowBlock i` is the row weight
`chowRowWeight i`. -/
lemma genericBlockWeight_chowRowBlock {q s : ℕ} (i : Fin q) :
    genericBlockWeight (chowRowBlock (s := s) i) = chowRowWeight i := by
  funext p
  simp [genericBlockWeight,chowRowBlock,chowRowWeight]

/-- A nonzero polynomial that is weighted homogeneous of degree `d` for the weights `w` has weighted
total degree `d`. -/
lemma weightedTotalDegree_of_nonzero_homogeneous
    {R σ : Type*} [CommSemiring R] (w : σ → ℕ)
    (f : MvPolynomial σ R) (d : ℕ)
    (hf : f.IsWeightedHomogeneous w d) (hf0 : f ≠ 0) :
    f.weightedTotalDegree w = d := by
  have he := hf.weighted_total_degree hf0
  rw [weightedTotalDegree_coe w f hf0] at he
  exact WithBot.coe_injective he

/-- The finite family of polynomials in the Plücker coordinates of a center given by the
coefficients of the derivative resultant `Res(f, f')` in degree `d`, where `f` is the restriction of
the universal center restriction of `F` to a generic line in the `i`-th row of hyperplane
coefficients. -/
def centerRowResultantFamily
    {K : Type*} [Field K] {r n s q : ℕ}
    (e : Fin (s + 1) ≃ (Fin (r + 1) ↪ Fin n)) (i : Fin q)
    (F : MvPolynomial (Fin q × Fin n) K) (d : ℕ) :
    Finset (MvPolynomial (Fin r ↪ Fin n) K) :=
  derivativeResultantCoefficientFamily
    (genericBlockLine (chowRowBlock i) (universalCenterChowMap e F)) d

/-- If `F` is homogeneous of degree `D` and `0 < d`, every member of
`centerRowResultantFamily e i F d` is homogeneous of degree `D * (2 * d - 1)` in the Plücker
coordinates. -/
theorem centerRowResultantFamily_homogeneous
    {K : Type*} [Field K] {r n s q D : ℕ}
    (e : Fin (s + 1) ≃ (Fin (r + 1) ↪ Fin n)) (i : Fin q)
    (F : MvPolynomial (Fin q × Fin n) K) (d : ℕ) (hd : 0 < d)
    (hF : F.IsHomogeneous D) :
    ∀ g ∈ centerRowResultantFamily e i F d, g.IsHomogeneous (D * (2 * d - 1)) :=
  genericBlockLine_resultant_family_homogeneous _ _ d D hd
    (universalCenterChowMap_coefficient_homogeneous e F hF)

/-- If `F` is homogeneous of degree `D` and `0 < d`, every member of
`centerRowResultantFamily e i F d` has total degree at most `D * (2 * d - 1)`. -/
theorem centerRowResultantFamily_totalDegree_le
    {K : Type*} [Field K] {r n s q D : ℕ}
    (e : Fin (s + 1) ≃ (Fin (r + 1) ↪ Fin n)) (i : Fin q)
    (F : MvPolynomial (Fin q × Fin n) K) (d : ℕ) (hd : 0 < d)
    (hF : F.IsHomogeneous D) :
    ∀ g ∈ centerRowResultantFamily e i F d, g.totalDegree ≤ D * (2 * d - 1) := by
  intro g hg
  exact (centerRowResultantFamily_homogeneous e i F d hd hF g hg).totalDegree_le

section

/-! Exact coefficient-extension specialization of the selected-row resultant
family. Centers may have coordinates in the extension field. -/

open MvPolynomial Matrix

private lemma universalCenterChowMap_specialize_extension
    {K L : Type*} [Field K] [Field L] (φ : K →+* L) {r n s q : ℕ}
    (A : Matrix (Fin r) (Fin (n + 1)) L)
    (e : Fin (s + 1) ≃ (Fin (r + 1) ↪ Fin (n + 1)))
    (F : MvPolynomial (Fin q × Fin (n + 1)) K) :
    map (eval₂Hom φ (matrixPluckerCoordinates A))
      (universalCenterChowMap e F) =
      chowLinearSubstitution (centerMinorProjectionMatrix A e) (map φ F) := by
  have he : (map (eval₂Hom φ (matrixPluckerCoordinates A))).comp
      (universalCenterChowMap (K := K) (q := q) e) =
      (chowLinearSubstitution (r := q) (centerMinorProjectionMatrix A e)).toRingHom.comp
        (map φ) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [universalCenterChowMap,chowLinearSubstitution]
    · intro p
      simp [universalCenterChowMap,chowLinearSubstitution,centerMinorProjectionMatrix,
        centerPluckerCoefficient,apply_ite]
  exact RingHom.congr_fun he F

/-- For a center matrix `A` over a field extension given by `φ`, some member of
`centerRowResultantFamily e i F d` is nonzero at the Plücker coordinates of `A` exactly when the
derivative resultant, in degree `d`, of the restriction of `F` along the center projection of `A` to
a generic line in the `i`-th row is nonzero. -/
theorem centerRowResultantFamily_nonvanishing_iff_extension
    {K L : Type*} [Field K] [Field L] (φ : K →+* L) {r n s q : ℕ}
    (e : Fin (s + 1) ≃ (Fin (r + 1) ↪ Fin (n + 1))) (i : Fin q)
    (F : MvPolynomial (Fin q × Fin (n + 1)) K) (d : ℕ)
    (A : Matrix (Fin r) (Fin (n + 1)) L) :
    (∃ g ∈ centerRowResultantFamily e i F d,
      eval₂ φ (matrixPluckerCoordinates A) g ≠ 0) ↔
    derivativeResultant (genericBlockLine (chowRowBlock i)
      (chowLinearSubstitution (centerMinorProjectionMatrix A e) (map φ F))) d ≠ 0 := by
  have he := derivativeResultantCoefficientFamily_nonvanishing_iff
    (genericBlockLine (chowRowBlock i) (universalCenterChowMap e F)) d φ
    (matrixPluckerCoordinates A)
  simpa only [centerRowResultantFamily,genericBlockLine_map,
    universalCenterChowMap_specialize_extension] using he

end

end
end CCDN
