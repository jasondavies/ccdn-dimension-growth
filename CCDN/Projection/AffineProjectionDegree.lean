module

public import CCDN.Hilbert.ProjectiveClosureHilbertPolynomial
public import CCDN.Algebra.ProjectiveClosureSpecialization
public import CCDN.Projection.HomogeneousFiniteProjectionDegree
public import CCDN.Hilbert.PrincipalHilbertPolynomial
public import CCDN.Projection.IntegralProjectionHilbert
/-! Degree preservation for an affine linear projection whose
projective-closure map is finite and birational. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

theorem affine_projection_equation_degree_eq_of_closure
    {m n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℚ)) [I.IsPrime]
    (a : Fin (m + 2) → MvPolynomial (Fin n) ℚ)
    (ha : ∀ i, (a i).IsHomogeneous 1)
    (hint : (projectionCoordinateMap (projectiveClosureIdeal I)
      (closureProjectionCoordinates a)).IsIntegral)
    (hfield : IntermediateField.adjoin ℚ
      (Set.range (fun i => algebraMap
        (MvPolynomial (Fin (n + 1)) ℚ ⧸ projectiveClosureIdeal I)
        (FractionRing (MvPolynomial (Fin (n + 1)) ℚ ⧸ projectiveClosureIdeal I))
        ((Ideal.Quotient.mk (projectiveClosureIdeal I))
          (closureProjectionCoordinates a i)))) = ⊤)
    (d : ℕ) (hdim : (filteredHilbertPolynomial I).natDegree = m + 1)
    (hdegree : (filteredHilbertPolynomial I).leadingCoeff =
      (d : ℚ) / (m + 1).factorial)
    (f : MvPolynomial (Fin (m + 2)) ℚ) (hf : f ≠ 0) (hfpos : 0 < f.totalDegree)
    (hker : RingHom.ker (projectionCoordinateMap I a) = Ideal.span {f}) :
    f.totalDegree = d := by
  let J := RingHom.ker (projectionCoordinateMap I a)
  let : J.IsPrime := RingHom.ker_isPrime _
  have hJdim : (filteredHilbertPolynomial J).natDegree = m + 1 :=
    (integral_projection_hilbert_dimension_eq I _
      (affine_projection_integral_of_closure_integral I a hint)).trans hdim
  have hJdegree : (filteredHilbertPolynomial J).leadingCoeff =
      (f.totalDegree : ℚ) / (m + 1).factorial := by
    rw [show J = Ideal.span {f} from hker]
    exact principal_filteredHilbertPolynomial_leadingCoeff f hf hfpos
  have hsource := (projectiveClosureIdeal_hilbertPolynomial_parameters
    I (m + 1) d hdim hdegree).2
  have htarget := (projectiveClosureIdeal_hilbertPolynomial_parameters
    J (m + 1) f.totalDegree hJdim hJdegree).2
  have heq := homogeneous_finite_birational_projection_leadingCoeff_eq
    (F := FractionRing (MvPolynomial (Fin (n + 1)) ℚ ⧸ projectiveClosureIdeal I))
    (projectiveClosureIdeal I) (projectiveClosureIdeal_homogeneous I)
    (closureProjectionCoordinates a) (closureProjectionCoordinates_homogeneous a ha)
    hint hfield
  rw [← projectiveClosureIdeal_projection_kernel I a ha, hsource, htarget] at heq
  have hh := (div_left_inj' (by positivity : ((m + 1 + 1).factorial : ℚ) ≠ 0)).mp heq
  exact_mod_cast hh

end
end CCDN
