module

public import CCDN.GenericHyperplaneNormalizationDescent
public import CCDN.HomogeneousNormalizationRank

/-! A named rational-function field of universal hyperplane coefficients,
with its canonical independent tuple and actual finite normalization.
The function-field rank is exactly the original Hilbert multiplicity. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

abbrev universalCoefficientField (K σ : Type*) [Field K] := FractionRing (MvPolynomial σ K)

def universalCoefficient (K σ : Type*) [Field K] (i : σ) : universalCoefficientField K σ :=
  algebraMap (MvPolynomial σ K) (universalCoefficientField K σ) (X i)

theorem universalCoefficient_algebraicIndependent (K σ : Type*) [Field K] :
    AlgebraicIndependent K (universalCoefficient K σ) :=
  (algebraicIndependent_X σ K).map'
    (f := IsScalarTower.toAlgHom K (MvPolynomial σ K) (universalCoefficientField K σ))
    (IsFractionRing.injective (MvPolynomial σ K) (universalCoefficientField K σ))

abbrev universalHyperplaneField (K : Type*) [Field K] (r n : ℕ) :=
  universalCoefficientField K (Fin r × Fin (n + 1))

def universalHyperplaneForms (K : Type*) [Field K] (r n : ℕ) :
    Fin r → MvPolynomial (Fin (n + 1)) (universalHyperplaneField K r n) :=
  genericHyperplaneForms (universalCoefficient K (Fin r × Fin (n + 1)))

def universalHyperplaneSourceIdeal {K : Type*} [Field K] {n : ℕ}
    (r : ℕ) (I : Ideal (MvPolynomial (Fin n) K)) :
    Ideal (MvPolynomial (Fin (n + 1)) (universalHyperplaneField K r n)) :=
  projectiveClosureIdeal (I.map (map (algebraMap K (universalHyperplaneField K r n))))

instance universalHyperplaneSourceIdeal_isPrime
    {K : Type*} [Field K] {n : ℕ} (r : ℕ)
    (I : Ideal (MvPolynomial (Fin n) K))
    [(I.map (map (algebraMap K (AlgebraicClosure K)))).IsPrime] :
    (universalHyperplaneSourceIdeal r I).IsPrime := by
  let := prime_ideal_scalar_extension_of_algebraicClosure
    (L := universalHyperplaneField K r n) I
  exact projectiveClosureIdeal_isPrime _

theorem universalHyperplaneSourceIdeal_geometrically_prime
    {K L : Type*} [Field K] [Field L] {n r : ℕ}
    [Algebra (universalHyperplaneField K r n) L] [Algebra K L]
    [IsScalarTower K (universalHyperplaneField K r n) L]
    (I : Ideal (MvPolynomial (Fin n) K))
    [(I.map (map (algebraMap K (AlgebraicClosure K)))).IsPrime] :
    ((universalHyperplaneSourceIdeal r I).map
      (map (algebraMap (universalHyperplaneField K r n) L))).IsPrime := by
  rw [universalHyperplaneSourceIdeal, projectiveClosureIdeal_scalar_extension,
    ideal_scalar_extension_tower]
  let := prime_ideal_scalar_extension_of_algebraicClosure (L := L) I
  infer_instance

theorem universal_hyperplane_projection_integral
    {K : Type*} [Field K] {n r : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    [(I.map (map (algebraMap K (AlgebraicClosure K)))).IsPrime]
    (hr : (filteredHilbertPolynomial I).natDegree < r) :
    (projectionCoordinateMap (universalHyperplaneSourceIdeal r I)
      (universalHyperplaneForms K r n)).IsIntegral :=
  generic_hyperplane_projection_integral_of_geometric_prime I hr _
    (universalCoefficient_algebraicIndependent K _)

theorem universal_hyperplane_normalization_injective
    {K : Type*} [Field K] {n m : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    [(I.map (map (algebraMap K (AlgebraicClosure K)))).IsPrime]
    (hm : (filteredHilbertPolynomial I).natDegree = m) :
    Function.Injective (projectionCoordinateMap (universalHyperplaneSourceIdeal (m + 1) I)
      (universalHyperplaneForms K (m + 1) n)) :=
  generic_hyperplane_normalization_injective_of_geometric_prime I hm _
    (universalCoefficient_algebraicIndependent K _)

/-- Exact degree for the actual universal normalization, in any chosen
fraction field of its actual scalar-extended projective-closure cone. -/
theorem universal_hyperplane_normalization_finrank
    {K : Type*} [Field K] [CharZero K] {n m : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    [(I.map (map (algebraMap K (AlgebraicClosure K)))).IsPrime]
    (d : ℕ) (hm : (filteredHilbertPolynomial I).natDegree = m)
    (hd : (filteredHilbertPolynomial I).leadingCoeff = (d : ℚ) / m.factorial)
    (F : Type*) [Field F] [Algebra (universalHyperplaneField K (m + 1) n) F]
    [hAF : Algebra (MvPolynomial (Fin (n + 1)) (universalHyperplaneField K (m + 1) n) ⧸
      universalHyperplaneSourceIdeal (m + 1) I) F]
    [IsScalarTower (universalHyperplaneField K (m + 1) n)
      (MvPolynomial (Fin (n + 1)) (universalHyperplaneField K (m + 1) n) ⧸
        universalHyperplaneSourceIdeal (m + 1) I) F]
    [IsFractionRing (MvPolynomial (Fin (n + 1)) (universalHyperplaneField K (m + 1) n) ⧸
      universalHyperplaneSourceIdeal (m + 1) I) F] :
    let v : Fin (m + 1) → F := fun i => @algebraMap
      (MvPolynomial (Fin (n + 1)) (universalHyperplaneField K (m + 1) n) ⧸
        universalHyperplaneSourceIdeal (m + 1) I) F _ _ hAF
      ((Ideal.Quotient.mk (universalHyperplaneSourceIdeal (m + 1) I))
        (universalHyperplaneForms K (m + 1) n i))
    Module.finrank (IntermediateField.adjoin (universalHyperplaneField K (m + 1) n)
      (Set.range v)) F = d := by
  dsimp only
  let E := universalHyperplaneField K (m + 1) n
  let : CharZero E := Algebra.charZero_of_charZero K E
  let IE := I.map (map (algebraMap K E))
  let : IE.IsPrime := prime_ideal_scalar_extension_of_algebraicClosure (L := E) I
  obtain ⟨hJdim,hJdegree⟩ := projectiveClosureIdeal_hilbertPolynomial_parameters IE m d
    (by simpa only [IE, filteredHilbertPolynomial_scalar_extension] using hm)
    (by simpa only [IE, filteredHilbertPolynomial_scalar_extension] using hd)
  apply homogeneous_normalization_functionField_finrank
    (universalHyperplaneSourceIdeal (m + 1) I) (projectiveClosureIdeal_homogeneous IE)
    (universalHyperplaneForms K (m + 1) n)
    (genericHyperplaneForms_homogeneous _)
    (universal_hyperplane_normalization_injective I hm)
    (universal_hyperplane_projection_integral I (by rw [hm]; omega)) d hJdim hJdegree

/-- The concrete fraction-field instance has no supplied field model or
independent generic coefficients. -/
theorem universal_hyperplane_normalization_fractionRank
    {K : Type*} [Field K] [CharZero K] {n m : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    [(I.map (map (algebraMap K (AlgebraicClosure K)))).IsPrime]
    (d : ℕ) (hm : (filteredHilbertPolynomial I).natDegree = m)
    (hd : (filteredHilbertPolynomial I).leadingCoeff = (d : ℚ) / m.factorial) :
    let E := universalHyperplaneField K (m + 1) n
    let A := MvPolynomial (Fin (n + 1)) E ⧸ universalHyperplaneSourceIdeal (m + 1) I
    let F := FractionRing A
    let v : Fin (m + 1) → F := fun i => @algebraMap A F _ _
      (inferInstance : Algebra A (FractionRing A))
      ((Ideal.Quotient.mk (universalHyperplaneSourceIdeal (m + 1) I))
        (universalHyperplaneForms K (m + 1) n i))
    Module.finrank (IntermediateField.adjoin E (Set.range v)) F = d :=
  universal_hyperplane_normalization_finrank I d hm hd _

end
end CCDN
