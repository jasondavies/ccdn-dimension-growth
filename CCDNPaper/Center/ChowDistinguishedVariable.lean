/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDNPaper.Center.GenericLinearIndependence

/-! View the Chow equation as a polynomial in one hyperplane's
constant coefficient. Every other coefficient remains a separate variable;
their incidence images are algebraically independent. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- All hyperplane coefficients except the final constant coefficient. -/
abbrev ChowCoefficientVariables (m n : ℕ) :=
  (Fin (m + 1) × Fin n) ⊕ Fin m

/-- The bijection between the hyperplane coefficients `Fin (m + 1) × Fin (n + 1)` and
`Option (ChowCoefficientVariables m n)`, sending the constant coefficient `(Fin.last m, 0)` of
the last hyperplane to `none` and every other coefficient to `some` of its index. -/
def chowDistinguishedVariableEquiv (m n : ℕ) :
    (Fin (m + 1) × Fin (n + 1)) ≃ Option (ChowCoefficientVariables m n) where
  toFun q := Fin.cases
    (Fin.lastCases none (fun i => some (Sum.inr i)) q.1)
    (fun j => some (Sum.inl (q.1,j))) q.2
  invFun q := q.elim (Fin.last m,0) (chowIndependentVariables m n)
  left_inv q := by
    rcases q with ⟨i,j⟩
    refine Fin.cases ?_ (fun k => ?_) j
    · refine Fin.lastCases ?_ (fun k => ?_) i <;>
        simp [chowIndependentVariables]
    · simp [chowIndependentVariables]
  right_inv q := by
    cases q with
    | none => simp
    | some q => cases q <;> simp [chowIndependentVariables]

/-- The `K`-algebra isomorphism regrouping a polynomial in the hyperplane coefficients as a
univariate polynomial in the last hyperplane's constant coefficient `(Fin.last m, 0)`, with
coefficients polynomials in the remaining variables; no coefficient is specialized. -/
def chowAsUnivariate (K : Type*) [Field K] (m n : ℕ) :
    MvPolynomial (Fin (m + 1) × Fin (n + 1)) K ≃ₐ[K]
      Polynomial (MvPolynomial (ChowCoefficientVariables m n) K) :=
  (renameEquiv K (chowDistinguishedVariableEquiv m n)).trans
    (optionEquivLeft K _)

/-- The degree of `chowAsUnivariate K m n F` as a univariate polynomial equals the degree of
`F` in the constant coefficient `(Fin.last m, 0)` of the last hyperplane. -/
lemma chowAsUnivariate_natDegree {K : Type*} [Field K] {m n : ℕ}
    (F : MvPolynomial (Fin (m + 1) × Fin (n + 1)) K) :
    (chowAsUnivariate K m n F).natDegree = degreeOf (Fin.last m,0) F := by
  rw [chowAsUnivariate,AlgEquiv.trans_apply,natDegree_optionEquivLeft]
  simpa only [renameEquiv_apply,chowDistinguishedVariableEquiv,Equiv.coe_fn_mk,
    Fin.cases_zero,Fin.lastCases_last] using
    (degreeOf_rename_of_injective (chowDistinguishedVariableEquiv m n).injective
      (p := F) (Fin.last m,0))

/-- The coefficient map induced by incidence. -/
def chowCoefficientMap {K : Type*} [Field K] {n : ℕ} (m : ℕ)
    (I : Ideal (MvPolynomial (Fin n) K)) :
    MvPolynomial (ChowCoefficientVariables m n) K →ₐ[K]
      MvPolynomial (Fin (m + 1) × Fin n) (MvPolynomial (Fin n) K ⧸ I) :=
  (chowIncidenceMap (m + 1) I).comp (rename (chowIndependentVariables m n))

private lemma chowCoefficientMap_injective {K : Type*} [Field K] {m n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (hm : (filteredHilbertPolynomial I).natDegree = m) :
    Function.Injective (chowCoefficientMap m I) := by
  have he : chowCoefficientMap m I = aeval (fun q =>
      chowIncidenceMap (m + 1) I (X (chowIndependentVariables m n q))) := by
    ext q
    simp [chowCoefficientMap]
  rw [he]
  exact chowIncidence_independent_coordinates I hm

/-- The incidence image of `F` is obtained by evaluating the univariate polynomial
`chowAsUnivariate K m n F` at the incidence image of the distinguished variable
`X (Fin.last m, 0)`, after mapping its coefficients by `chowCoefficientMap m I`. -/
lemma chowIncidenceMap_eq_univariate_eval {K : Type*} [Field K] {m n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K))
    (F : MvPolynomial (Fin (m + 1) × Fin (n + 1)) K) :
    (chowAsUnivariate K m n F).eval₂ (chowCoefficientMap m I).toRingHom
        (chowIncidenceMap (m + 1) I (X (Fin.last m,0))) =
      chowIncidenceMap (m + 1) I F := by
  have he : (Polynomial.eval₂RingHom (chowCoefficientMap m I).toRingHom
      (chowIncidenceMap (m + 1) I (X (Fin.last m,0)))).comp
      (chowAsUnivariate K m n).toRingHom = (chowIncidenceMap (m + 1) I).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [chowAsUnivariate,chowCoefficientMap]
    · rintro ⟨i,j⟩
      refine Fin.cases ?_ (fun k => ?_) j
      · refine Fin.lastCases ?_ (fun k => ?_) i <;>
          simp [chowAsUnivariate,chowDistinguishedVariableEquiv,chowCoefficientMap,
            chowIndependentVariables]
      · simp [chowAsUnivariate,chowDistinguishedVariableEquiv,chowCoefficientMap,
          chowIndependentVariables]
  exact RingHom.congr_fun he F

/-- The distinguished variable occurs with positive degree in every
nonzero incidence equation at the correct number of hyperplane rows. -/
theorem chowAsUnivariate_natDegree_pos {K : Type*} [Field K] {m n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (hm : (filteredHilbertPolynomial I).natDegree = m)
    (F : MvPolynomial (Fin (m + 1) × Fin (n + 1)) K)
    (hF : F ≠ 0) (hmem : F ∈ chowIncidenceIdeal (m + 1) I) :
    0 < (chowAsUnivariate K m n F).natDegree := by
  by_contra hpos
  have hc := Polynomial.eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_not_pos hpos)
  have he := chowIncidenceMap_eq_univariate_eval I F
  change chowIncidenceMap (m + 1) I F = 0 at hmem
  rw [hmem,hc,Polynomial.eval₂_C] at he
  have hz := (injective_iff_map_eq_zero (chowCoefficientMap m I)).mp
    (chowCoefficientMap_injective I hm) _ he
  have hp : chowAsUnivariate K m n F = 0 := by rw [hc,hz,Polynomial.C_0]
  exact hF ((chowAsUnivariate K m n).injective (hp.trans (map_zero _).symm))

end
end CCDN
