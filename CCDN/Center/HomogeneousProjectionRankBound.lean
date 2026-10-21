module

public import CCDN.Center.ProjectionImageFractionField
public import CCDN.Center.HomogeneousNormalizationRank
public import CCDN.Projection.LinearNormalizationInfinite
public import CCDN.Algebra.PolynomialPredicates
/-! A finite homogeneous linear projection has function-field degree at most
the quotient of source and image multiplicities. The proof constructs a
finite independent linear normalization of its image. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The image multiplicity times the function-field degree is bounded
by the source multiplicity. -/
theorem homogeneous_projection_functionField_rank_bound
    {K F : Type*} [Field K] [CharZero K] [Field F] [Algebra K F] {n s m : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    [Algebra (MvPolynomial (Fin n) K ⧸ I) F]
    [IsScalarTower K (MvPolynomial (Fin n) K ⧸ I) F]
    [IsFractionRing (MvPolynomial (Fin n) K ⧸ I) F]
    (hI : IsHomogeneousIdeal I)
    (a : Fin s → MvPolynomial (Fin n) K) (ha : ∀ i, (a i).IsHomogeneous 1)
    (hint : (projectionCoordinateMap I a).IsIntegral)
    (d e : ℕ) (hdimdeg : HasProjectiveDimensionDegree I m d)
    (himage : (filteredHilbertPolynomial (RingHom.ker (projectionCoordinateMap I a))).leadingCoeff =
      (e : ℚ) / (m + 1).factorial) :
    Module.Finite (projectionImageField (F := F) I a) F ∧
      e * Module.finrank (projectionImageField (F := F) I a) F ≤ d := by
  classical
  obtain ⟨hdim, hdegree⟩ := hdimdeg
  let A := MvPolynomial (Fin n) K ⧸ I
  let ψ := projectionCoordinateMap I a
  let J := RingHom.ker ψ
  have : J.IsPrime := RingHom.ker_isPrime ψ.toRingHom
  let B := MvPolynomial (Fin s) K ⧸ J
  let L := projectionImageField (F := F) I a
  let β : B →ₐ[K] L := projectionImageFieldMap (F := F) I a
  let : Algebra B L := β.toRingHom.toAlgebra
  let : IsScalarTower K B L := IsScalarTower.of_algHom β
  let : IsFractionRing B L := projectionImageFieldMap_isFractionRing (F := F) I a
  have hJdim : (filteredHilbertPolynomial J).natDegree = m + 1 :=
    (integral_projection_hilbert_dimension_eq I ψ hint).trans hdim
  obtain ⟨_, _, hdimle, _⟩ := filteredHilbertPolynomial_positive_multiplicity J
    (Ideal.IsPrime.ne_top ‹J.IsPrime›)
  have hms : m + 1 ≤ s := by simpa only [hJdim, Fintype.card_fin] using hdimle
  obtain ⟨b, hb, hbint, hbinj⟩ := exists_linear_integral_normalization_infinite_of_le m s hms J hJdim
  have hJhom := projection_kernel_homogeneousComponent_mem I hI a ha
  let v : Fin (m + 1) → L := fun i => β ((Ideal.Quotient.mk J) (b i))
  let E := IntermediateField.adjoin K (Set.range v)
  let u : Fin (m + 1) → E := fun i => ⟨v i, IntermediateField.subset_adjoin K _ ⟨i, rfl⟩⟩
  let : Algebra E F := (L.val.comp E.val).toRingHom.toAlgebra
  let : IsScalarTower K E F := IsScalarTower.of_algHom (L.val.comp E.val)
  let : IsScalarTower E L F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hvB : AlgebraicIndependent K (fun i => (Ideal.Quotient.mk J) (b i)) := by
    change Function.Injective (aeval (fun i => (Ideal.Quotient.mk J) (b i)))
    rw [← projectionCoordinateMap_eq_aeval]
    exact hbinj
  have hv : AlgebraicIndependent K v := hvB.map' (projectionImageFieldMap_injective I a)
  have hu : AlgebraicIndependent K u := AlgebraicIndependent.of_comp E.val hv
  let l : Fin (m + 1) → MvPolynomial (Fin n) K := fun i => aeval a (b i)
  have hl (i) : (l i).totalDegree ≤ 1 := by
    have hh := (hb i).aeval a ha
    simpa only [Nat.one_mul] using hh.totalDegree_le
  have heval (i) : algebraMap A F ((Ideal.Quotient.mk I) (l i)) = algebraMap E F (u i) := by
    exact (DFunLike.congr_fun (projectionImageFieldMap_comp_val (F := F) I a)
      ((Ideal.Quotient.mk J) (b i))).symm
  obtain ⟨hfinite, hrank⟩ := hilbert_functionField_finite_rank_le (R := E) (F := F) I d
    (by simpa only [Fintype.card_fin] using hdim)
    (by simpa only [Fintype.card_fin] using hdegree) l hl u hu heval
  let : Module.Finite E F := hfinite
  let : Module.Finite L F := Module.Finite.of_restrictScalars_finite E L F
  have hEL : Module.finrank E L = e :=
    homogeneous_normalization_functionField_finrank (F := L) J hJhom b hb hbinj hbint e
      ⟨hJdim, himage⟩
  let : Module.Free E L := Module.Free.of_divisionRing E L
  let : Module.Free L F := Module.Free.of_divisionRing L F
  refine ⟨inferInstance, ?_⟩
  rw [← hEL, Module.finrank_mul_finrank]
  exact hrank

end
end CCDN
