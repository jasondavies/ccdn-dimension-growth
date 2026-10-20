module

public import AffineCurveCounting.ChowAxisEvaluation
public import AffineCurveCounting.HilbertScalarExtension

/-! The distinguished coordinate computes the Chow block degree over the
original field whenever the source stays prime over an algebraically
closed extension. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

theorem chow_generator_last_coordinate_degree_of_geometric_prime
    {K L : Type*} [Field K] [Field L] [Algebra K L] [IsAlgClosed L] {m n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K))
    [(I.map (map (algebraMap K L))).IsPrime]
    (hm : (filteredHilbertPolynomial I).natDegree = m)
    (F : MvPolynomial (Fin (m + 1) × Fin (n + 1)) K)
    (hgen : chowIncidenceIdeal (m + 1) I = Ideal.span {F})
    (d : ℕ) (hd : F.IsWeightedHomogeneous (chowRowWeight (Fin.last m)) d) :
    F.degreeOf (Fin.last m,0) = d := by
  let J := I.map (map (algebraMap K L))
  have hmJ : (filteredHilbertPolynomial J).natDegree = m := by
    rw [filteredHilbertPolynomial_scalar_extension]
    exact hm
  have hgenJ : chowIncidenceIdeal (m + 1) J = Ideal.span {map (algebraMap K L) F} := by
    rw [← chowIncidenceIdeal_scalar_extension, hgen, Ideal.map_span, Set.image_singleton]
  have hdJ : (map (algebraMap K L) F).IsWeightedHomogeneous (chowRowWeight (Fin.last m)) d := by
    intro e he
    apply hd
    intro hz
    apply he
    rw [coeff_map, hz, map_zero]
  have hh := chow_generator_last_coordinate_degree J hmJ
    (map (algebraMap K L) F) hgenJ d hdJ
  simpa only [degreeOf, degrees_map_of_injective F (algebraMap K L).injective] using hh

theorem chow_generator_univariate_degree_of_geometric_prime
    {K L : Type*} [Field K] [Field L] [Algebra K L] [IsAlgClosed L] {m n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K))
    [(I.map (map (algebraMap K L))).IsPrime]
    (hm : (filteredHilbertPolynomial I).natDegree = m)
    (F : MvPolynomial (Fin (m + 1) × Fin (n + 1)) K)
    (hgen : chowIncidenceIdeal (m + 1) I = Ideal.span {F})
    (d : ℕ) (hd : F.IsWeightedHomogeneous (chowRowWeight (Fin.last m)) d) :
    (chowAsUnivariate K m n F).natDegree = d := by
  rw [chowAsUnivariate_natDegree]
  exact chow_generator_last_coordinate_degree_of_geometric_prime (L := L) I hm F hgen d hd

end
end AffineCurveCounting
