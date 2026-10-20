module

public import AffineCurveCounting.EulerPairSpecialization

/-! Universal homogeneous coefficient minors of the Euler-restricted operator.
The constructed forms have degree exactly d^2-1 in the homogeneous sense,
specialize to actual coefficient minors, and detect normalized irreducibility
in characteristic zero. Reducibility vanishing and height bounds are separate. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial Module

lemma eulerLowBasis_repr_apply {R : Type*} [CommRing R] (d : ℕ)
    (f : restrictTotalDegree (Fin 2) R d) (i : EulerLowIndex d) :
    (eulerLowBasis R d).repr f i = f.val.coeff ((boundedExponentEquivSym (Fin 2) d).symm i).val := by
  unfold eulerLowBasis
  erw [Basis.repr_reindex_apply]

def eulerCoefficientMonomial (R : Type*) [CommRing R] (d : ℕ) (i : EulerLowIndex d) :
    Polynomial (Polynomial R) :=
  bivariatePolynomialEquiv R (monomial ((boundedExponentEquivSym (Fin 2) d).symm i).val 1)

def eulerCoefficientData {R : Type*} [CommRing R] (d : ℕ)
    (f : Polynomial (Polynomial R)) (i : EulerLowIndex d) : R :=
  ((bivariatePolynomialEquiv R).symm f).coeff ((boundedExponentEquivSym (Fin 2) d).symm i).val

/-- These parameters are precisely the polynomial's ordinary monomial coefficients. -/
theorem eulerCoefficientData_reconstruct {R : Type*} [CommRing R] (d : ℕ)
    (f : Polynomial (Polynomial R)) (hf : bivariateTotalDegree f ≤ d) :
    ∑ i, eulerCoefficientData d f i • eulerCoefficientMonomial R d i = f := by
  let u : restrictTotalDegree (Fin 2) R d :=
    ⟨(bivariatePolynomialEquiv R).symm f, (mem_restrictTotalDegree _ _ _).mpr hf⟩
  have hh := congrArg (fun v : restrictTotalDegree (Fin 2) R d =>
    bivariatePolynomialEquiv R v.val) ((eulerLowBasis R d).sum_repr u)
  simpa only [Submodule.coe_sum, SetLike.val_smul, map_sum, map_smul,
    eulerLowBasis_repr_apply, eulerLowBasis_apply, AlgEquiv.apply_symm_apply,
    eulerCoefficientData, eulerCoefficientMonomial, u] using hh

lemma eulerCoefficientMonomial_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (d : ℕ) (i : EulerLowIndex d) :
    bivariateMap φ (eulerCoefficientMonomial R d i) = eulerCoefficientMonomial S d i := by
  simp only [eulerCoefficientMonomial, bivariatePolynomialEquiv_map, map_monomial, map_one]

/-- The differential operator is linear in the defining equation as well
as in its pair of unknowns. -/
def closedFormEquationLinear {R : Type*} [CommRing R]
    (u : Polynomial (Polynomial R) × Polynomial (Polynomial R)) :
    Polynomial (Polynomial R) →ₗ[R] Polynomial (Polynomial R) where
  toFun f := closedFormOperator f u
  map_add' f g := by
    simp only [closedFormOperator, LinearMap.coe_mk, AddHom.coe_mk, map_add, mul_add]
    ring
  map_smul' a f := closedFormOperator_smul_equation a f u

def eulerCoefficientEntryLinear {R : Type*} [CommRing R] (k : ℕ)
    (row : ℕ × ℕ) (col : EulerColumns k) : Polynomial (Polynomial R) →ₗ[R] R :=
  (LinearMap.proj row).comp ((bivariateCoefficients R).comp
    (closedFormEquationLinear (eulerBivariatePair R k (eulerPairBasis R k col))))

lemma eulerCoefficientEntryLinear_apply {R : Type*} [CommRing R] (k : ℕ)
    (row : ℕ × ℕ) (col : EulerColumns k) (f : Polynomial (Polynomial R)) :
    eulerCoefficientEntryLinear k row col f = eulerClosedFormCoefficientMatrix k f row col := rfl

lemma eulerCoefficientMatrix_expand {R : Type*} [CommRing R] (k : ℕ)
    (f : Polynomial (Polynomial R)) (hf : bivariateTotalDegree f ≤ k + 2)
    (row : ℕ × ℕ) (col : EulerColumns k) :
    ∑ i, eulerCoefficientData (k + 2) f i *
      eulerClosedFormCoefficientMatrix k (eulerCoefficientMonomial R (k + 2) i) row col =
      eulerClosedFormCoefficientMatrix k f row col := by
  have hh := congrArg (eulerCoefficientEntryLinear k row col)
    (eulerCoefficientData_reconstruct (k + 2) f hf)
  rw [map_sum] at hh
  simpa only [map_smul, smul_eq_mul, eulerCoefficientEntryLinear_apply] using hh

/-- Integer universal matrix in all coefficients of a degree-at-most-d equation. -/
def universalEulerMatrix (k : ℕ) : Matrix (ℕ × ℕ) (EulerColumns k)
    (MvPolynomial (EulerLowIndex (k + 2)) ℤ) :=
  fun row col => ∑ i, C (eulerClosedFormCoefficientMatrix k
    (eulerCoefficientMonomial ℤ (k + 2) i) row col) * X i

lemma universalEulerMatrix_homogeneous (k : ℕ) (row : ℕ × ℕ) (col : EulerColumns k) :
    (universalEulerMatrix k row col).IsHomogeneous 1 := by
  apply IsHomogeneous.sum
  intro i _
  exact isHomogeneous_C_mul_X _ _

/-- Every universal matrix entry specializes to the actual differential
coefficient matrix, with no characteristic restriction. -/
theorem universalEulerMatrix_specialize {R : Type*} [CommRing R]
    (k : ℕ) (f : Polynomial (Polynomial R)) (hf : bivariateTotalDegree f ≤ k + 2) :
    (universalEulerMatrix k).map (eval₂Hom (Int.castRingHom R) (eulerCoefficientData (k + 2) f)) =
      eulerClosedFormCoefficientMatrix k f := by
  classical
  ext row col
  simp only [Matrix.map_apply, universalEulerMatrix]
  simp only [map_sum, map_mul, eval₂Hom_C, Int.coe_castRingHom]
  have hX (i : EulerLowIndex (k + 2)) :
      eval₂Hom (Int.castRingHom R) (eulerCoefficientData (k + 2) f) (X i) =
        eulerCoefficientData (k + 2) f i := eval₂_X _ _ _
  simp only [hX]
  rw [← eulerCoefficientMatrix_expand k f hf row col]
  apply Finset.sum_congr rfl
  intro i _
  have he := congrFun (congrFun (eulerClosedFormCoefficientMatrix_map (Int.castRingHom R) k
    (eulerCoefficientMonomial ℤ (k + 2) i)) row) col
  rw [eulerCoefficientMonomial_map] at he
  change ((eulerClosedFormCoefficientMatrix k (eulerCoefficientMonomial ℤ (k + 2) i) row col : ℤ) : R) = _ at he
  rw [he]
  change _ * _ = _ * _
  exact mul_comm _ _

/-- The universal forms are the actual maximal coefficient minors. -/
def universalEulerMinor (k : ℕ)
    (rows : Fin ((k + 2) ^ 2 - 1) → ℕ × ℕ)
    (cols : Fin ((k + 2) ^ 2 - 1) → EulerColumns k) :
    MvPolynomial (EulerLowIndex (k + 2)) ℤ :=
  ((universalEulerMatrix k).submatrix rows cols).det

lemma universalEulerMinor_homogeneous (k : ℕ)
    (rows : Fin ((k + 2) ^ 2 - 1) → ℕ × ℕ)
    (cols : Fin ((k + 2) ^ 2 - 1) → EulerColumns k) :
    (universalEulerMinor k rows cols).IsHomogeneous ((k + 2) ^ 2 - 1) := by
  classical
  unfold universalEulerMinor
  rw [Matrix.det_apply']
  apply IsHomogeneous.sum
  intro σ _
  have hh := IsHomogeneous.prod Finset.univ
    (fun i => universalEulerMatrix k (rows (σ i)) (cols i)) (fun _ => 1)
    (fun i _ => universalEulerMatrix_homogeneous _ _ _)
  have hp : (∏ i, universalEulerMatrix k (rows (σ i)) (cols i)).IsHomogeneous
      ((k + 2) ^ 2 - 1) := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] using hh
  simpa using hp.C_mul (Equiv.Perm.sign σ : ℤ)

/-- The universal forms detect every irreducible plane equation of full
outer degree with a constant nonzero leading coefficient in characteristic zero. -/
theorem exists_universalEulerMinor_nonzero
    {F : Type*} [Field F] [CharZero F] [IsAlgClosed F]
    (k : ℕ) (f : Polynomial (Polynomial F)) (hf : Irreducible f)
    (htotal : bivariateTotalDegree f ≤ k + 2) (a : F) (ha : a ≠ 0)
    (hl : f.leadingCoeff = Polynomial.C a) (hdeg : f.natDegree = k + 2) :
    ∃ (rows : Fin ((k + 2) ^ 2 - 1) → ℕ × ℕ)
      (cols : Fin ((k + 2) ^ 2 - 1) → EulerColumns k),
      eval₂ (Int.castRingHom F) (eulerCoefficientData (k + 2) f)
        (universalEulerMinor k rows cols) ≠ 0 := by
  obtain ⟨rows, cols, _, _, hn⟩ := exists_eulerClosedForm_nonzero_minor k f hf a ha hl hdeg
  refine ⟨rows, cols, ?_⟩
  change (eval₂Hom (Int.castRingHom F) (eulerCoefficientData (k + 2) f))
    (((universalEulerMatrix k).submatrix rows cols).det) ≠ 0
  rw [RingHom.map_det]
  change (((universalEulerMatrix k).map
    (eval₂Hom (Int.castRingHom F) (eulerCoefficientData (k + 2) f))).submatrix rows cols).det ≠ 0
  rw [universalEulerMatrix_specialize k f htotal]
  exact hn

end
end AffineCurveCounting
