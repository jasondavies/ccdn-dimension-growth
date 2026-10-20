module

public import AffineCurveCounting.GenericPlaneEulerMinorCharZero
public import AffineCurveCounting.UniversalPlaneMinor
public import AffineCurveCounting.EulerUniversalForms

/-! Every absolutely irreducible characteristic-zero hypersurface of degree
d at least two gives a nonzero Euler minor of order d²−1 in the universal
affine-plane parameter ring. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

lemma eulerClosedFormCoefficientMatrix_smul {R : Type*} [CommRing R]
    (u : R) (k : ℕ) (f : Polynomial (Polynomial R)) :
    eulerClosedFormCoefficientMatrix k (u • f) = u • eulerClosedFormCoefficientMatrix k f := by
  ext row col
  change eulerCoefficientEntryLinear k row col (u • f) =
    u • eulerCoefficientEntryLinear k row col f
  exact map_smul _ _ _

lemma eulerClosedForm_minor_smul {R : Type*} [CommRing R]
    (u : R) (k r : ℕ) (f : Polynomial (Polynomial R))
    (a : Fin r → ℕ × ℕ) (c : Fin r → EulerColumns k) :
    ((eulerClosedFormCoefficientMatrix k (u • f)).submatrix a c).det =
      u ^ r * ((eulerClosedFormCoefficientMatrix k f).submatrix a c).det := by
  rw [eulerClosedFormCoefficientMatrix_smul]
  change (u • (eulerClosedFormCoefficientMatrix k f).submatrix a c).det = _
  rw [Matrix.det_smul, Fintype.card_fin]

/-- The actual universal affine-plane family has a nonzero determinant of
the precise Noether order. Smooth coordinates and geometric irreducibility
of their generic section are constructed, not supplied. -/
theorem exists_universalPlane_euler_minor_charZero
    {K σ : Type*} [Field K] [CharZero K] [IsAlgClosed K] [Fintype σ]
    (k : ℕ) (f : MvPolynomial (Option σ) K) (hf : Irreducible f)
    (hd : f.totalDegree = k + 2) :
    ∃ (rows : Fin ((k + 2) ^ 2 - 1) → ℕ × ℕ)
      (cols : Fin ((k + 2) ^ 2 - 1) → EulerColumns k),
      Function.Injective rows ∧ Function.Injective cols ∧
      ((eulerClosedFormCoefficientMatrix k (universalPlanePolynomial f)).submatrix rows cols).det ≠ 0 := by
  obtain ⟨a, b, hb, _, rows, cols, hr, hc, hdet⟩ :=
    exists_positioned_genericPlane_euler_minor_charZero k f hf hd
  let R := MvPolynomial σ K
  let F := FractionRing R
  let φ : R →+* F := algebraMap R F
  have hne : φ (((eulerClosedFormCoefficientMatrix k
      (genericPlanePolynomial (normalizedHypersurfaceCoordinates a b hb f))).submatrix rows cols).det) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R F)).mpr hdet
  rw [eulerClosedForm_minor_map, normalized_genericPlane_universal_specialization,
    eulerClosedForm_minor_smul, ← eulerClosedForm_minor_map] at hne
  refine ⟨rows, cols, hr, hc, ?_⟩
  intro he
  exact hne (by rw [he, map_zero, mul_zero])

end
end AffineCurveCounting
