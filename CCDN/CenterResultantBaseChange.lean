module

public import CCDN.CenterResultantForms

/-! Exact coefficient-extension specialization of the selected-row resultant
family. Centers may have coordinates in the extension field. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Matrix

lemma universalCenterChowMap_specialize_extension
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
end CCDN
