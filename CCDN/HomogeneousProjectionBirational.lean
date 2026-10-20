module

public import CCDN.HomogeneousProjectionRankBound
public import CCDN.HomogeneousZeroDimensionField
public import CCDN.HomogeneousFiniteProjectionDegree
public import CCDN.PolynomialPredicates

/-! A finite homogeneous linear projection preserves the actual Hilbert
multiplicity if and only if its projected coordinates generate the source
function field. This includes the zero-dimensional affine cone. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Equality of source and actual image multiplicities forces birationality.
The image field, a finite linear normalization, and its rank are constructed
internally; there is no dimension, normalization, or rank assumption. -/
theorem homogeneous_finite_projection_birational_of_leadingCoeff_eq
    {K F : Type*} [Field K] [CharZero K] [Field F] [Algebra K F] {n s : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    [Algebra (MvPolynomial (Fin n) K ⧸ I) F]
    [IsScalarTower K (MvPolynomial (Fin n) K ⧸ I) F]
    [IsFractionRing (MvPolynomial (Fin n) K ⧸ I) F]
    (hI : IsHomogeneousIdeal I)
    (a : Fin s → MvPolynomial (Fin n) K) (ha : ∀ i, (a i).IsHomogeneous 1)
    (hint : (projectionCoordinateMap I a).IsIntegral)
    (heq : (filteredHilbertPolynomial (RingHom.ker (projectionCoordinateMap I a))).leadingCoeff =
      (filteredHilbertPolynomial I).leadingCoeff) :
    projectionImageField (F := F) I a = ⊤ := by
  by_cases hzero : (filteredHilbertPolynomial I).natDegree = 0
  · exact homogeneous_zero_dimension_projectionImageField_eq_top I hI hzero a
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hzero
  obtain ⟨d, hd, _, hlc⟩ := filteredHilbertPolynomial_positive_multiplicity I
    (Ideal.IsPrime.ne_top ‹I.IsPrime›)
  have hdegree : (filteredHilbertPolynomial I).leadingCoeff =
      (d : ℚ) / (m + 1).factorial := by simpa only [hm] using hlc
  obtain ⟨hfinite, hrank⟩ := homogeneous_projection_functionField_rank_bound (F := F)
    I hI a ha hint d d hm hdegree (heq.trans hdegree)
  let L := projectionImageField (F := F) I a
  let : Module.Finite L F := hfinite
  have hpos : 0 < Module.finrank L F := Module.finrank_pos
  apply IntermediateField.finrank_eq_one_iff_eq_top.mp
  change Module.finrank L F = 1
  nlinarith

/-- Degree preservation and function-field birationality are equivalent for
an actual finite homogeneous linear projection in characteristic zero. -/
theorem homogeneous_finite_projection_leadingCoeff_eq_iff_birational
    {K F : Type*} [Field K] [CharZero K] [Field F] [Algebra K F] {n s : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    [Algebra (MvPolynomial (Fin n) K ⧸ I) F]
    [IsScalarTower K (MvPolynomial (Fin n) K ⧸ I) F]
    [IsFractionRing (MvPolynomial (Fin n) K ⧸ I) F]
    (hI : IsHomogeneousIdeal I)
    (a : Fin s → MvPolynomial (Fin n) K) (ha : ∀ i, (a i).IsHomogeneous 1)
    (hint : (projectionCoordinateMap I a).IsIntegral) :
    (filteredHilbertPolynomial (RingHom.ker (projectionCoordinateMap I a))).leadingCoeff =
      (filteredHilbertPolynomial I).leadingCoeff ↔
    projectionImageField (F := F) I a = ⊤ := by
  constructor
  · exact homogeneous_finite_projection_birational_of_leadingCoeff_eq I hI a ha hint
  · exact homogeneous_finite_birational_projection_leadingCoeff_eq I hI a ha hint

end
end CCDN
