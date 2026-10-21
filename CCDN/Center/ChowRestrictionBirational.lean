module

public import CCDN.Center.GeometricProjectionHilbert
public import CCDN.Center.ProjectiveChowExactDegree
public import CCDN.Center.HomogeneousProjectionBirational
public import CCDN.Center.ChowProjectionCriterion
public import CCDN.Algebra.PolynomialPredicates
/-! A disjoint projection center gives an irreducible Chow restriction
exactly when its coordinate-field extension is birational. Source
and image degrees are the proved Hilbert multiplicities. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Matrix

theorem geometric_chow_restriction_irreducible_iff_birational
    {K : Type*} [Field K] [CharZero K] {n s m : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 2)) K)) [I.IsPrime]
    [(I.map (map (algebraMap K (AlgebraicClosure K)))).IsPrime]
    (hI : IsHomogeneousIdeal I)
    (d : ℕ) (hdim : (filteredHilbertPolynomial I).natDegree = m + 1)
    (hdegree : (filteredHilbertPolynomial I).leadingCoeff = (d : ℚ) / (m + 1).factorial)
    (F : MvPolynomial (Fin (m + 1) × Fin (n + 2)) K)
    (hF : Irreducible (map (algebraMap K (AlgebraicClosure K)) F))
    (hδ : ∀ i, F.IsWeightedHomogeneous (chowRowWeight i) d)
    (hzero : ∀ U, eval U (map (algebraMap K (AlgebraicClosure K)) F) = 0 ↔
      U ∈ projectiveChowIncidenceLocus (m + 1)
        (I.map (map (algebraMap K (AlgebraicClosure K)))))
    (A : Matrix (Fin (s + 2)) (Fin (n + 2)) K)
    (hcenter : ∀ p ∈ projectiveIdealZeroLocus (I.map (map (algebraMap K (AlgebraicClosure K)))),
      (A.map (algebraMap K (AlgebraicClosure K))) *ᵥ p.rep ≠ 0) :
    Irreducible (chowLinearSubstitution (A.map (algebraMap K (AlgebraicClosure K)))
      (map (algebraMap K (AlgebraicClosure K)) F)) ↔
      projectionImageField (F := FractionRing (MvPolynomial (Fin (n + 2)) K ⧸ I))
        I (chowProjectionForms A) = ⊤ := by
  classical
  let L := AlgebraicClosure K
  let φ := algebraMap K L
  let J := I.map (map φ)
  let AL := A.map φ
  let FL := map φ F
  let P := chowProjectionImageIdeal J AL
  let R := chowLinearSubstitution AL FL
  have hJ := homogeneous_ideal_scalar_extension (L := L) I hI
  have hJdim : (filteredHilbertPolynomial J).natDegree = m + 1 := by
    rw [filteredHilbertPolynomial_scalar_extension]
    exact hdim
  have hint := projection_integral_of_geometric_center_disjoint I hI A hcenter
  have hintL := chow_projection_integral_of_center_disjoint J hJ AL hcenter
  have : P.IsPrime := RingHom.ker_isPrime (projectionCoordinateMap J (chowProjectionForms AL)).toRingHom
  have hPdim : (filteredHilbertPolynomial P).natDegree = m + 1 :=
    (integral_projection_hilbert_dimension_eq J _ hintL).trans hJdim
  obtain ⟨e, _, _, he⟩ := filteredHilbertPolynomial_positive_multiplicity P
    (Ideal.IsPrime.ne_top ‹P.IsPrime›)
  have hedegree : (filteredHilbertPolynomial P).leadingCoeff = (e : ℚ) / (m + 1).factorial := by
    simpa only [hPdim] using he
  obtain ⟨G, hG, _, hGdegree, hGzero⟩ := exists_projective_chow_exact_degree P
    (chowProjectionImageIdeal_homogeneous J hJ AL) e hPdim hedegree
  have hδL (i) : FL.IsWeightedHomogeneous (chowRowWeight i) d := by
    intro a ha
    apply hδ i
    intro hz
    apply ha
    rw [coeff_map, hz, map_zero]
  have hRne : R ≠ 0 :=
    (chowLinearSubstitution_ne_zero_iff_center_disjoint J hJ hJdim AL FL hzero).mpr hcenter
  have hRdegree : R.totalDegree = (m + 1) * d :=
    (chowLinearSubstitution_totalDegree_of_ne_zero AL FL hF.ne_zero (fun _ => d) hδL hRne).trans
      (chow_uniform_row_degree_totalDegree FL hF.ne_zero d hδL)
  have hsame := chowLinearSubstitution_same_zeros_as_image J hJ AL hcenter FL G hzero hGzero
  have hir := irreducible_iff_degree_eq_of_same_zeros G R hG hsame
  rw [hRdegree, hGdegree, Nat.mul_left_cancel_iff (by omega : 0 < m + 1)] at hir
  have hfield := homogeneous_finite_projection_leadingCoeff_eq_iff_birational
    (F := FractionRing (MvPolynomial (Fin (n + 2)) K ⧸ I))
    I hI (chowProjectionForms A) (chowProjectionForms_homogeneous A) hint
  change (filteredHilbertPolynomial (chowProjectionImageIdeal I A)).leadingCoeff =
    (filteredHilbertPolynomial I).leadingCoeff ↔ _ at hfield
  rw [← chowProjectionImageIdeal_hilbertPolynomial_scalar_extension (L := L) I A] at hfield
  have hcoeff : (filteredHilbertPolynomial P).leadingCoeff =
      (filteredHilbertPolynomial I).leadingCoeff ↔ e = d := by
    rw [hedegree, hdegree, div_left_inj' (by positivity : ((m + 1).factorial : ℚ) ≠ 0)]
    exact Nat.cast_inj
  exact hir.trans ((eq_comm.trans hcoeff.symm).trans hfield)

end
end CCDN
