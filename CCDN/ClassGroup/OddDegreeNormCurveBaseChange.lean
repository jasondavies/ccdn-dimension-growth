/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.ClassGroup.ClassGroupNormPolynomial
import CCDN.ClassGroup.OddDegreeNormCurves
import CCDN.Projection.ShearNormalization
/-! Odd-degree norm curves keep their degree and irreducibility in every
residue characteristic, including characteristic two. The signs ±1 remain
nonzero in every field. -/

@[expose] public section
namespace CCDN
noncomputable section
open scoped NumberField
open Polynomial NumberField

variable (K E : Type*) [Field K] [NumberField K] [Field E]

lemma signedNormCurvePolynomial_bivariate_map (β : 𝓞 K) (ε : ℤ) :
    bivariatePolynomialEquiv E
      (MvPolynomial.map (Int.castRingHom E) (signedNormCurvePolynomial K β ε)) =
      X ^ 2 - C (C (ε : E) *
        (integerNormPolynomial K β).map (Int.castRingHom E)) := by
  rw [← bivariatePolynomialEquiv_map]
  simp only [signedNormCurvePolynomial, AlgEquiv.apply_symm_apply]
  change Polynomial.map (Polynomial.mapRingHom (Int.castRingHom E))
    (X ^ 2 - C (C ε * integerNormPolynomial K β)) = _
  simp

theorem signedNormCurvePolynomial_map_irreducible_in_every_characteristic
    (β : 𝓞 K) {ε : ℤ} (hε : (ε : E) ≠ 0) (hn : Odd (Module.finrank ℚ K)) :
    Irreducible (MvPolynomial.map (Int.castRingHom E)
      (signedNormCurvePolynomial K β ε)) := by
  apply (MulEquiv.irreducible_iff (f := bivariatePolynomialEquiv E)).mp
  rw [signedNormCurvePolynomial_bivariate_map]
  apply odd_degree_double_cover_irreducible
  rw [natDegree_C_mul hε, (integerNormPolynomial_monic K β).natDegree_map,
    integerNormPolynomial_natDegree]
  exact hn

theorem signedNormCurvePolynomial_map_totalDegree
    (β : 𝓞 K) {ε : ℤ} (hε : (ε : E) ≠ 0) (hn : 2 ≤ Module.finrank ℚ K) :
    (MvPolynomial.map (Int.castRingHom E)
      (signedNormCurvePolynomial K β ε)).totalDegree = Module.finrank ℚ K := by
  have hd : (C (ε : E) * (integerNormPolynomial K β).map (Int.castRingHom E)).natDegree =
      Module.finrank ℚ K := by
    rw [natDegree_C_mul hε, (integerNormPolynomial_monic K β).natDegree_map,
      integerNormPolynomial_natDegree]
  have hh : bivariateTotalDegree (bivariatePolynomialEquiv E
      (MvPolynomial.map (Int.castRingHom E) (signedNormCurvePolynomial K β ε))) =
      Module.finrank ℚ K := by
    rw [signedNormCurvePolynomial_bivariate_map,
      double_cover_bivariateTotalDegree _ (by omega), hd]
  simpa only [bivariateTotalDegree, AlgEquiv.symm_apply_apply] using hh

end
end CCDN
