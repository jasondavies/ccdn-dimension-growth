module

public import CCDN.IndependentPrimitiveExtension
public import CCDN.ClosureNormalizationInfinite
public import CCDN.ProjectiveClosureHilbertPolynomial
public import CCDN.ProjectiveClosureProjection
public import CCDN.HilbertFullDimension

/-! A finite birational linear projection of the projective closure
that retains the homogenizing coordinate. The tuple is independent even
in degree one and in affine dimension zero. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

theorem exists_independent_fixed_coordinate_closure_projection
    {K : Type*} [Field K] [CharZero K] {m n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (hmn : m + 1 ≤ n) (d : ℕ)
    (hdim : (filteredHilbertPolynomial I).natDegree = m)
    (hdegree : (filteredHilbertPolynomial I).leadingCoeff = (d : ℚ) / m.factorial) :
    ∃ a : Fin (m + 2) → MvPolynomial (Fin (n + 1)) K,
      (∀ i, (a i).IsHomogeneous 1) ∧ LinearIndependent K a ∧ a 1 = X 0 ∧
      (projectionCoordinateMap (projectiveClosureIdeal I) a).IsIntegral ∧
      projectionImageField (F := FractionRing (MvPolynomial (Fin (n + 1)) K ⧸ projectiveClosureIdeal I))
        (projectiveClosureIdeal I) a = ⊤ := by
  obtain ⟨b, hb, _, _, hcone⟩ :=
    exists_closure_normalization_infinite_of_le m n (by omega) I hdim
  let J := projectiveClosureIdeal I
  obtain ⟨hJdim, hJdegree⟩ := projectiveClosureIdeal_hilbertPolynomial_parameters I m d hdim hdegree
  have hker : RingHom.ker (projectionCoordinateMap J (closureProjectionCoordinates b)) = ⊥ :=
    ideal_eq_bot_of_full_hilbert_dimension _ (RingHom.ker_ne_top _) (by
      simpa only [Fintype.card_fin] using
        (integral_projection_hilbert_dimension_eq J _ hcone).trans hJdim)
  have hinj : Function.Injective (projectionCoordinateMap J (closureProjectionCoordinates b)) :=
    (RingHom.injective_iff_ker_eq_bot _).mpr hker
  obtain ⟨v, hv, hli, hint, hfield⟩ := exists_independent_linear_primitive_extension
    (F := FractionRing (MvPolynomial (Fin (n + 1)) K ⧸ J)) J
    (closureProjectionCoordinates b) (closureProjectionCoordinates_homogeneous b hb)
    hcone hinj (by omega) d hJdim hJdegree
  refine ⟨Fin.cons v (closureProjectionCoordinates b), ?_, hli, ?_, hint, hfield⟩
  · intro i
    exact Fin.cases hv (closureProjectionCoordinates_homogeneous b hb) i
  · rfl

end
end CCDN
