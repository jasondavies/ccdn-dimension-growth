module

public import CCDN.Center.AffineNormalizationRank
public import CCDN.Center.FixedCoordinateGenericNormalization
/-! Exact affine normalization degree for algebraically independent linear
coefficients. All fraction fields are fraction fields of the displayed affine
coordinate ring. -/

@[expose] public section
namespace CCDN
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
  have : IL.IsPrime := prime_ideal_scalar_extension_of_algebraicClosure (L := L) I
  exact affine_normalization_functionField_finrank (F := F) IL
    (genericAffineParameterForms u) (genericAffineParameterForms_homogeneous u)
    (generic_fixed_coordinate_projection_integral I hdim u hu) d
    (by simpa only [IL,filteredHilbertPolynomial_scalar_extension] using hdim)
    (by simpa only [IL,filteredHilbertPolynomial_scalar_extension] using hdegree)

end
end CCDN
