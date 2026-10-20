module

public import CCDN.BoundedCenterProjectionAllRows
public import CCDN.BoundedBirationalCenter
public import CCDN.PolynomialPredicates

/-! Complementary projections retain the geometric and degree
properties of the minor projection with the same center. This interface
is independent of the bound used to construct the center rows. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Matrix

/-- Properties of the normalized projection onto a complementary
linear subspace, and of its homogeneous image ideal. -/
structure BirationalComplementProjection {r n : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) ℚ)) [J.IsPrime]
    (M : Matrix (Fin r) (Fin (n + 1)) ℤ) (D : ℤ)
    (P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ) : Prop where
  scale_ne_zero : D ≠ 0
  scaled_idempotent : P * P = D • P
  idempotent : IsIdempotentElem (normalizedIntegerProjection D P)
  kernel : (normalizedIntegerProjection D P).ker =
    Submodule.span ℚ (Set.range (M.map (Int.castRingHom ℚ)).row)
  complementary : IsCompl (Submodule.span ℚ (Set.range (M.map (Int.castRingHom ℚ)).row))
    (normalizedIntegerProjection D P).range
  projection_along : ∀ x, x - normalizedIntegerProjection D P x ∈
    Submodule.span ℚ (Set.range (M.map (Int.castRingHom ℚ)).row)
  integral : (projectionCoordinateMap J (chowProjectionForms (P.map (Int.castRingHom ℚ)))).IsIntegral
  birational : projectionImageField (F := FractionRing (MvPolynomial (Fin (n + 1)) ℚ ⧸ J))
    J (chowProjectionForms (P.map (Int.castRingHom ℚ))) = ⊤
  image_homogeneous : ∀ f ∈ chowProjectionImageIdeal J (P.map (Int.castRingHom ℚ)), ∀ N,
    homogeneousComponent N f ∈ chowProjectionImageIdeal J (P.map (Int.castRingHom ℚ))
  image_geometrically_prime : ((chowProjectionImageIdeal J (P.map (Int.castRingHom ℚ))).map
    (map (algebraMap ℚ (AlgebraicClosure ℚ)))).IsPrime
  image_dimension : (filteredHilbertPolynomial
    (chowProjectionImageIdeal J (P.map (Int.castRingHom ℚ)))).natDegree =
    (filteredHilbertPolynomial J).natDegree
  image_leadingCoeff : (filteredHilbertPolynomial
    (chowProjectionImageIdeal J (P.map (Int.castRingHom ℚ)))).leadingCoeff =
    (filteredHilbertPolynomial J).leadingCoeff

lemma integral_matrix_projection_no_base_point {n s : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) ℚ))
    (hJ : IsHomogeneousIdeal J)
    (A : Matrix (Fin (s + 1)) (Fin (n + 1)) ℚ)
    (hint : (projectionCoordinateMap J (chowProjectionForms A)).IsIntegral)
    (x : ProjectivePoint n) (hx : x ∈ projectiveIdealZeroLocus J) : A *ᵥ x.rep ≠ 0 := by
  intro hz
  apply x.rep_nonzero
  apply homogeneous_integral_projection_zero_fiber J hJ (chowProjectionForms A)
    (chowProjectionForms_homogeneous A) hint x.rep
  · intro f hf
    simpa only [aeval_eq_eval] using projectiveIdealZeroLocus_rep hx f hf
  · intro i
    simpa only [aeval_eq_eval, chowProjectionForms_eval, Pi.zero_apply] using congrFun hz i

/-- Any bounded independent good center gives a bounded complementary
projection. The bound T is arbitrary, so sharper detector bounds can reuse
this construction unchanged. -/
theorem exists_bounded_birational_complement_of_minor_projection
    {r n s : ℕ} (J : Ideal (MvPolynomial (Fin (n + 1)) ℚ)) [J.IsPrime]
    [(J.map (map (algebraMap ℚ (AlgebraicClosure ℚ)))).IsPrime]
    (hJ : IsHomogeneousIdeal J)
    (M : Matrix (Fin r) (Fin (n + 1)) ℤ)
    (hM : LinearIndependent ℚ (M.map (Int.castRingHom ℚ)).row)
    (T : ℕ) (hb : ∀ i j, |M i j| ≤ (T : ℤ))
    (e : Fin (s + 2) ≃ (Fin (r + 1) ↪ Fin (n + 1)))
    (hint : (projectionCoordinateMap J (chowProjectionForms
      (centerMinorProjectionMatrix (M.map (Int.castRingHom ℚ)) e))).IsIntegral)
    (hfield : projectionImageField (F := FractionRing (MvPolynomial (Fin (n + 1)) ℚ ⧸ J)) J
      (chowProjectionForms (centerMinorProjectionMatrix (M.map (Int.castRingHom ℚ)) e)) = ⊤) :
    ∃ (D : ℤ) (P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ),
      BirationalComplementProjection J M D P ∧
      (∀ i j, |P i j| ≤ 2 * (r.factorial : ℤ) * (T : ℤ) ^ r) ∧
      Module.finrank ℚ (normalizedIntegerProjection D P).range + r = n + 1 ∧
      ∀ x ∈ projectiveIdealZeroLocus J,
        ∃ hx : normalizedIntegerProjection D P x.rep ≠ 0,
          (Projectivization.mk ℚ (normalizedIntegerProjection D P x.rep) hx).mulHeight ≤
            (n + 1 : ℕ) * (2 * (r.factorial : ℝ) * (T : ℝ) ^ r) * x.mulHeight := by
  obtain ⟨D,hD,P,hP,hPP,hi,hker,hcompl,hdim,hsub,_⟩ :=
    exists_bounded_rational_center_projection_all_rows M hM T hb
  have hk : (P.map (Int.castRingHom ℚ)).mulVecLin.ker =
      (centerMinorProjectionMatrix (M.map (Int.castRingHom ℚ)) e).mulVecLin.ker := by
    rw [normalizedIntegerProjection_matrix_ker D hD P, hker,
      centerMinorProjectionMatrix_ker _ hM e]
    rfl
  have hpi := projection_integral_of_matrix_kernel_le J _ _ hk.le hint
  have hpf : projectionImageField (F := FractionRing (MvPolynomial (Fin (n + 1)) ℚ ⧸ J)) J
      (chowProjectionForms (P.map (Int.castRingHom ℚ))) = ⊤ := by
    rw [projectionImageField_eq_of_matrix_kernel_eq J _ _ hk]
    exact hfield
  have hdata : BirationalComplementProjection J M D P :=
    { scale_ne_zero := hD
      scaled_idempotent := hPP
      idempotent := hi
      kernel := hker
      complementary := hcompl
      projection_along := hsub
      integral := hpi
      birational := hpf
      image_homogeneous := chowProjectionImageIdeal_homogeneous J hJ _
      image_geometrically_prime := projection_kernel_geometrically_prime J _
      image_dimension := integral_projection_hilbert_dimension_eq J _ hpi
      image_leadingCoeff := homogeneous_finite_birational_projection_leadingCoeff_eq J hJ _
        (chowProjectionForms_homogeneous _) hpi hpf }
  refine ⟨D,P,hdata,hP,hdim,?_⟩
  intro x hx
  have hnon := integral_matrix_projection_no_base_point J hJ _ hpi x hx
  have hnon' : normalizedIntegerProjection D P x.rep ≠ 0 :=
    fun hz => hnon ((normalizedIntegerProjection_eq_zero_iff D hD P x.rep).mp hz)
  refine ⟨hnon', normalizedIntegerProjection_projective_height D hD P (by positivity) ?_ x hnon'⟩
  intro i j
  exact_mod_cast hP i j

end
end CCDN
