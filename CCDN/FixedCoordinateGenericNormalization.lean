module

public import CCDN.GenericLinearNormalizationOpenness
public import CCDN.ClosureNormalizationInfinite
public import CCDN.ProjectiveClosureSpecialization
public import CCDN.GenericHyperplaneNormalizationDescent

/-! Generic affine linear normalization with the homogenizing coordinate
fixed. The finite specialization and its nonzero determinant are both
constructed from the source ideal; no generic finiteness premise is used. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

def genericAffineParameterForms {R : Type*} [CommRing R] {m n : ℕ}
    (u : Fin m × Fin n → R) : Fin m → MvPolynomial (Fin n) R :=
  fun i => ∑ j, C (u (i,j)) * X j

lemma genericAffineParameterForms_homogeneous {R : Type*} [CommRing R] {m n : ℕ}
    (u : Fin m × Fin n → R) (i : Fin m) :
    (genericAffineParameterForms u i).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ (fun j _ => isHomogeneous_C_mul_X _ j)

lemma homogeneous_linear_forms_coefficient_representation
    {K : Type*} [Field K] {m n : ℕ} (a : Fin m → MvPolynomial (Fin n) K)
    (ha : ∀ i, (a i).IsHomogeneous 1) :
    ∃ c : Fin m × Fin n → K, genericAffineParameterForms c = a := by
  classical
  have hspan (i) : a i ∈ Submodule.span K (Set.range (X : Fin n → MvPolynomial (Fin n) K)) := by
    rw [← homogeneousSubmodule_one_eq_span_X]
    exact ha i
  have hex (i) := (Submodule.mem_span_range_iff_exists_fun K).mp (hspan i)
  choose c hc using hex
  refine ⟨fun q => c q.1 q.2, ?_⟩
  funext i
  simpa only [genericAffineParameterForms, smul_eq_C_mul] using hc i

def genericFixedCoordinateFamily (K : Type*) [Field K] (m n : ℕ) :
    Fin (m + 1) → MvPolynomial (Fin (n + 1)) (MvPolynomial (Fin m × Fin n) K) :=
  Fin.cons (X 0) (fun i => ∑ j, C (X (i,j)) * X j.succ)

lemma genericFixedCoordinateFamily_homogeneous
    (K : Type*) [Field K] (m n : ℕ) (i : Fin (m + 1)) :
    (genericFixedCoordinateFamily K m n i).IsHomogeneous 1 := by
  refine Fin.cases (isHomogeneous_X _ _) (fun j => ?_) i
  exact IsHomogeneous.sum _ _ _ (fun k _ => isHomogeneous_C_mul_X _ _)

lemma genericFixedCoordinateFamily_map
    {K L : Type*} [Field K] [Field L] {m n : ℕ}
    (φ : MvPolynomial (Fin m × Fin n) K →+* L) :
    (fun i => map φ (genericFixedCoordinateFamily K m n i)) =
      closureProjectionCoordinates (genericAffineParameterForms (fun q => φ (X q))) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [genericFixedCoordinateFamily, closureProjectionCoordinates]
  · simp [genericFixedCoordinateFamily, closureProjectionCoordinates, genericAffineParameterForms]

/-- Independent coefficients give a finite normalization of the
projective closure while its homogenizing coordinate remains fixed. -/
theorem generic_fixed_coordinate_projection_integral
    {K L : Type*} [Field K] [Infinite K] [Field L] [Algebra K L]
    {n m : ℕ} (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (hm : (filteredHilbertPolynomial I).natDegree = m)
    (u : Fin m × Fin n → L) (hu : AlgebraicIndependent K u) :
    (projectionCoordinateMap (projectiveClosureIdeal (I.map (map (algebraMap K L))))
      (closureProjectionCoordinates (genericAffineParameterForms u))).IsIntegral := by
  obtain ⟨_,_,hbound,_⟩ := filteredHilbertPolynomial_positive_multiplicity I
    (Ideal.IsPrime.ne_top ‹I.IsPrime›)
  have hmn : m ≤ n := by simpa only [hm, Fintype.card_fin] using hbound
  obtain ⟨a,ha,_,_,hint⟩ := exists_closure_normalization_infinite_of_le m n hmn I hm
  obtain ⟨c,hc⟩ := homogeneous_linear_forms_coefficient_representation a ha
  have hspecial : (fun i => map (eval c) (genericFixedCoordinateFamily K m n i)) =
      closureProjectionCoordinates a := by
    rw [genericFixedCoordinateFamily_map]
    simpa only [eval_X] using congrArg closureProjectionCoordinates hc
  have hgeneric : (fun i => map (aeval u).toRingHom (genericFixedCoordinateFamily K m n i)) =
      closureProjectionCoordinates (genericAffineParameterForms u) := by
    rw [genericFixedCoordinateFamily_map]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
  have h := generic_linear_projection_integral_of_specialization
    (projectiveClosureIdeal I) (projectiveClosureIdeal_homogeneous I)
    (genericFixedCoordinateFamily K m n) (genericFixedCoordinateFamily_homogeneous K m n)
    c (by rwa [hspecial]) u hu
  rwa [projectiveClosureIdeal_scalar_extension, hgeneric] at h

theorem generic_affine_parameter_projection_integral
    {K L : Type*} [Field K] [Infinite K] [Field L] [Algebra K L]
    {n m : ℕ} (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (hm : (filteredHilbertPolynomial I).natDegree = m)
    (u : Fin m × Fin n → L) (hu : AlgebraicIndependent K u) :
    (projectionCoordinateMap (I.map (map (algebraMap K L)))
      (genericAffineParameterForms u)).IsIntegral :=
  affine_projection_integral_of_closure_integral _ _
    (generic_fixed_coordinate_projection_integral I hm u hu)

theorem generic_affine_parameter_projection_injective
    {K L : Type*} [Field K] [Infinite K] [Field L] [Algebra K L]
    {n m : ℕ} (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    [(I.map (map (algebraMap K (AlgebraicClosure K)))).IsPrime]
    (hm : (filteredHilbertPolynomial I).natDegree = m)
    (u : Fin m × Fin n → L) (hu : AlgebraicIndependent K u) :
    Function.Injective (projectionCoordinateMap (I.map (map (algebraMap K L)))
      (genericAffineParameterForms u)) := by
  let IL := I.map (map (algebraMap K L))
  let : IL.IsPrime := prime_ideal_scalar_extension_of_algebraicClosure (L := L) I
  let ψ := projectionCoordinateMap IL (genericAffineParameterForms u)
  have hint : ψ.IsIntegral := generic_affine_parameter_projection_integral I hm u hu
  have hdim := integral_projection_hilbert_dimension_eq IL ψ hint
  have hk : RingHom.ker ψ = ⊥ := ideal_eq_bot_of_full_hilbert_dimension _
    (RingHom.ker_ne_top _) (by
      simpa only [IL, filteredHilbertPolynomial_scalar_extension, hm, Fintype.card_fin] using hdim)
  exact (RingHom.injective_iff_ker_eq_bot ψ).mpr hk

theorem generic_fixed_coordinate_projection_injective
    {K L : Type*} [Field K] [Infinite K] [Field L] [Algebra K L]
    {n m : ℕ} (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    [(I.map (map (algebraMap K (AlgebraicClosure K)))).IsPrime]
    (hm : (filteredHilbertPolynomial I).natDegree = m)
    (u : Fin m × Fin n → L) (hu : AlgebraicIndependent K u) :
    Function.Injective
      (projectionCoordinateMap (projectiveClosureIdeal (I.map (map (algebraMap K L))))
        (closureProjectionCoordinates (genericAffineParameterForms u))) := by
  let IL := I.map (map (algebraMap K L))
  let : IL.IsPrime := prime_ideal_scalar_extension_of_algebraicClosure (L := L) I
  let J := projectiveClosureIdeal IL
  let ψ := projectionCoordinateMap J (closureProjectionCoordinates (genericAffineParameterForms u))
  have hIL : (filteredHilbertPolynomial IL).natDegree = m := by
    rw [filteredHilbertPolynomial_scalar_extension]
    exact hm
  obtain ⟨d,_,_,hd⟩ := filteredHilbertPolynomial_positive_multiplicity IL
    (Ideal.IsPrime.ne_top ‹IL.IsPrime›)
  have hJ : (filteredHilbertPolynomial J).natDegree = m + 1 :=
    (projectiveClosureIdeal_hilbertPolynomial_parameters IL m d hIL
      (by simpa only [hIL] using hd)).1
  have hint : ψ.IsIntegral := generic_fixed_coordinate_projection_integral I hm u hu
  have hdim := integral_projection_hilbert_dimension_eq J ψ hint
  have hk : RingHom.ker ψ = ⊥ := ideal_eq_bot_of_full_hilbert_dimension _
    (RingHom.ker_ne_top _) (by simpa only [Fintype.card_fin, hJ] using hdim)
  exact (RingHom.injective_iff_ker_eq_bot ψ).mpr hk

end
end CCDN
