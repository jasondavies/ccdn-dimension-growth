module

public import CCDN.GenericPlaneMinorCharZero
public import CCDN.UniversalPlaneBadWitness

/-! Characteristic-zero nonvanishing of the universal witness and its descent
to an actual integer polynomial for a geometrically irreducible equation. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

theorem exists_universalPlane_minor_charZero
    {K σ : Type*} [Field K] [CharZero K] [IsAlgClosed K] [Fintype σ]
    (f : MvPolynomial (Option σ) K) (hf : Irreducible f)
    (hpos : 0 < f.totalDegree) :
    ∃ (rows : Fin (2 * f.totalDegree ^ 2 - 1) → ℕ × ℕ)
      (cols : Fin (2 * f.totalDegree ^ 2 - 1) → ClosedFormColumns f.totalDegree),
      Function.Injective rows ∧ Function.Injective cols ∧
      ((closedFormCoefficientMatrix f.totalDegree
        (universalPlanePolynomial f)).submatrix rows cols).det ≠ 0 := by
  obtain ⟨a, b, hb, _, rows, cols, hr, hc, hdet⟩ :=
    exists_positioned_genericPlane_minor_charZero f hf hpos
  let R := MvPolynomial σ K
  let F := FractionRing R
  let φ : R →+* F := algebraMap R F
  have hne : φ (((closedFormCoefficientMatrix f.totalDegree
      (genericPlanePolynomial (normalizedHypersurfaceCoordinates a b hb f))).submatrix rows cols).det) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R F)).mpr hdet
  rw [closedForm_minor_map, normalized_genericPlane_universal_specialization,
    closedForm_minor_smul, ← closedForm_minor_map] at hne
  refine ⟨rows, cols, hr, hc, ?_⟩
  intro he
  exact hne (by rw [he, map_zero, mul_zero])


lemma universalPlaneLeading_ne_zero_charZero
    {K σ : Type*} [Field K] [CharZero K] [IsAlgClosed K] [Fintype σ]
    (f : MvPolynomial (Option σ) K) (hf : Irreducible f) (hpos : 0 < f.totalDegree) :
    universalPlaneLeading f ≠ 0 := by
  obtain ⟨a, b, _, hdir, _⟩ := exists_monic_smooth_hypersurface_coordinates_charZero f hf hpos
  intro hz
  apply hdir
  rw [← universalPlaneLeading_specialize a b 0, hz, map_zero]

/-- An actual nonzero integer polynomial in the full parameter space,
constructed for every geometrically irreducible integer equation. -/
theorem exists_integer_universalPlane_badWitness
    {L σ : Type*} [Field L] [CharZero L] [IsAlgClosed L] [Fintype σ]
    (f : MvPolynomial (Option σ) ℤ)
    (hf : Irreducible (MvPolynomial.map (Int.castRingHom L) f))
    (hpos : 0 < f.totalDegree) :
    ∃ (rows : Fin (2 * f.totalDegree ^ 2 - 1) → ℕ × ℕ)
      (cols : Fin (2 * f.totalDegree ^ 2 - 1) → ClosedFormColumns f.totalDegree),
      Function.Injective rows ∧ Function.Injective cols ∧
      universalPlaneBadWitness f rows cols ≠ 0 ∧
      (universalPlaneBadWitness f rows cols).totalDegree ≤ 2 * f.totalDegree ^ 3 := by
  let φ : ℤ →+* L := Int.castRingHom L
  have ht : (MvPolynomial.map φ f).totalDegree = f.totalDegree := by
    unfold totalDegree
    rw [support_map_of_injective _ Int.cast_injective]
  have hex := exists_universalPlane_minor_charZero (MvPolynomial.map φ f) hf (ht ▸ hpos)
  rw [ht] at hex
  obtain ⟨rows, cols, hr, hc, hdet⟩ := hex
  have hm : ((closedFormCoefficientMatrix f.totalDegree
      (universalPlanePolynomial f)).submatrix rows cols).det ≠ 0 := by
    intro he
    rw [universalPlanePolynomial_map, ← closedForm_minor_map, he, map_zero] at hdet
    exact hdet rfl
  have hl : universalPlaneLeading f ≠ 0 := by
    have hn := universalPlaneLeading_ne_zero_charZero (MvPolynomial.map φ f) hf (ht ▸ hpos)
    have he : universalPlaneLeading (MvPolynomial.map φ f) = MvPolynomial.map φ (universalPlaneLeading f) := by
      simp only [universalPlaneLeading, ht, universalPlanePolynomial_map, bivariateMap_coeff]
    rw [he] at hn
    intro hz
    exact hn (by rw [hz, map_zero])
  exact ⟨rows, cols, hr, hc, mul_ne_zero hl hm, universalPlaneBadWitness_degree f rows cols⟩

end
end CCDN
