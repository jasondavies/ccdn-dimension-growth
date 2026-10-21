module

public import CCDN.CenterMinorMatrix

/-! Coefficient extension commutes with the literal maximal-minor projection
and with restriction of a Chow equation. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Matrix

lemma chowLinearSubstitution_map
    {K L : Type*} [Field K] [Field L] (φ : K →+* L) {n s q : ℕ}
    (A : Matrix (Fin (s + 1)) (Fin (n + 1)) K)
    (F : MvPolynomial (Fin q × Fin (n + 1)) K) :
    map φ (chowLinearSubstitution A F) = chowLinearSubstitution (A.map φ) (map φ F) := by
  have he : (map φ).comp (chowLinearSubstitution (r := q) A).toRingHom =
      (chowLinearSubstitution (r := q) (A.map φ)).toRingHom.comp (map φ) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [chowLinearSubstitution]
    · intro p
      simp [chowLinearSubstitution]
  exact RingHom.congr_fun he F

lemma centerMinorProjectionMatrix_map
    {K L : Type*} [Field K] [Field L] (φ : K →+* L) {r n s : ℕ}
    (A : Matrix (Fin r) (Fin (n + 1)) K)
    (e : Fin (s + 1) ≃ (Fin (r + 1) ↪ Fin (n + 1))) :
    (centerMinorProjectionMatrix A e).map φ = centerMinorProjectionMatrix (A.map φ) e := by
  classical
  ext i j
  simp only [centerMinorProjectionMatrix, Matrix.map_apply, centerPluckerCoefficient,
    map_sum, apply_ite, map_mul, eval_X, map_zero, map_pow, map_neg, map_one,
    matrixPluckerCoordinates_map]

lemma linearIndependent_matrix_rows_map
    {K L : Type*} [Field K] [Field L] (φ : K →+* L) {r n : ℕ}
    (A : Matrix (Fin r) (Fin n) K) (hA : LinearIndependent K A.row) :
    LinearIndependent L (A.map φ).row := by
  obtain ⟨c, hc, hd⟩ := exists_nonzero_minor_of_independent_rows A hA
  apply LinearIndependent.of_comp (LinearMap.funLeft L L c)
  apply Matrix.linearIndependent_rows_of_det_ne_zero
  change (φ.mapMatrix (A.submatrix id c)).det ≠ 0
  rw [← RingHom.map_det]
  exact (map_ne_zero_iff φ φ.injective).mpr hd

lemma centerChowRestriction_map
    {K L : Type*} [Field K] [Field L] (φ : K →+* L) {r n s q : ℕ}
    (A : Matrix (Fin r) (Fin (n + 1)) K)
    (e : Fin (s + 1) ≃ (Fin (r + 1) ↪ Fin (n + 1)))
    (F : MvPolynomial (Fin q × Fin (n + 1)) K) :
    map φ (chowLinearSubstitution (centerMinorProjectionMatrix A e) F) =
      chowLinearSubstitution (centerMinorProjectionMatrix (A.map φ) e) (map φ F) := by
  rw [chowLinearSubstitution_map, centerMinorProjectionMatrix_map]

end
end CCDN
