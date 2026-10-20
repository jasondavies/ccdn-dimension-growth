module

public import AffineCurveCounting.AffineNormalizationRank
public import AffineCurveCounting.FixedCoordinateGenericNormalization
public import AffineCurveCounting.UniversalHyperplaneNormalization

/-! Exact affine normalization degree for actual independent linear
coefficients, and for the named rational-function coefficient field.
All fraction fields are actual fraction fields of the displayed affine
coordinate ring; no field-degree or generic-finiteness assumption remains. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

theorem generic_affine_normalization_functionField_finrank
    {K L F : Type*} [Field K] [CharZero K] [Field L] [Algebra K L]
    [Field F] [Algebra L F] {n m : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    [(I.map (map (algebraMap K (AlgebraicClosure K)))).IsPrime]
    [hAF : Algebra (MvPolynomial (Fin n) L ⧸ I.map (map (algebraMap K L))) F]
    [IsScalarTower L (MvPolynomial (Fin n) L ⧸ I.map (map (algebraMap K L))) F]
    [IsFractionRing (MvPolynomial (Fin n) L ⧸ I.map (map (algebraMap K L))) F]
    (u : Fin m × Fin n → L) (hu : AlgebraicIndependent K u)
    (d : ℕ) (hdim : (filteredHilbertPolynomial I).natDegree = m)
    (hdegree : (filteredHilbertPolynomial I).leadingCoeff = (d : ℚ) / m.factorial) :
    Module.finrank (IntermediateField.adjoin L
      (Set.range (fun i => @algebraMap
        (MvPolynomial (Fin n) L ⧸ I.map (map (algebraMap K L))) F _ _ hAF
        ((Ideal.Quotient.mk (I.map (map (algebraMap K L))))
          (genericAffineParameterForms u i))))) F = d := by
  let : CharZero L := Algebra.charZero_of_charZero K L
  let IL := I.map (map (algebraMap K L))
  let : IL.IsPrime := prime_ideal_scalar_extension_of_algebraicClosure (L := L) I
  exact affine_normalization_functionField_finrank (F := F) IL
    (genericAffineParameterForms u) (genericAffineParameterForms_homogeneous u)
    (generic_fixed_coordinate_projection_integral I hdim u hu) d
    (by simpa only [IL,filteredHilbertPolynomial_scalar_extension] using hdim)
    (by simpa only [IL,filteredHilbertPolynomial_scalar_extension] using hdegree)

abbrev universalAffineCoefficientField (K : Type*) [Field K] (m n : ℕ) :=
  universalCoefficientField K (Fin m × Fin n)

/-- The independent coefficient tuple is constructed in the rational
function field itself, rather than supplied by the caller. -/
theorem universal_affine_normalization_functionField_finrank
    {K F : Type*} [Field K] [CharZero K] {n m : ℕ} [Field F]
    [Algebra (universalAffineCoefficientField K m n) F]
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    [(I.map (map (algebraMap K (AlgebraicClosure K)))).IsPrime]
    [hAF : Algebra (MvPolynomial (Fin n) (universalAffineCoefficientField K m n) ⧸
      I.map (map (algebraMap K (universalAffineCoefficientField K m n)))) F]
    [IsScalarTower (universalAffineCoefficientField K m n)
      (MvPolynomial (Fin n) (universalAffineCoefficientField K m n) ⧸
        I.map (map (algebraMap K (universalAffineCoefficientField K m n)))) F]
    [IsFractionRing (MvPolynomial (Fin n) (universalAffineCoefficientField K m n) ⧸
      I.map (map (algebraMap K (universalAffineCoefficientField K m n)))) F]
    (d : ℕ) (hdim : (filteredHilbertPolynomial I).natDegree = m)
    (hdegree : (filteredHilbertPolynomial I).leadingCoeff = (d : ℚ) / m.factorial) :
    Module.finrank (IntermediateField.adjoin (universalAffineCoefficientField K m n)
      (Set.range (fun i => @algebraMap
        (MvPolynomial (Fin n) (universalAffineCoefficientField K m n) ⧸
          I.map (map (algebraMap K (universalAffineCoefficientField K m n)))) F _ _ hAF
        ((Ideal.Quotient.mk (I.map
          (map (algebraMap K (universalAffineCoefficientField K m n)))))
          (genericAffineParameterForms (universalCoefficient K (Fin m × Fin n)) i))))) F = d :=
  generic_affine_normalization_functionField_finrank I _
    (universalCoefficient_algebraicIndependent K _) d hdim hdegree

end
end AffineCurveCounting
