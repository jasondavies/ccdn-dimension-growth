module

public import CCDN.RationalSurfaceSalbergerCover
public import CCDN.ProjectiveClosureDegree
public import CCDN.HomogeneousChartIrreducible
public import CCDN.PolynomialPredicates

/-! Salberger's surface cover on the standard projective affine chart.
Every returned curve is an actual homogeneous geometrically prime ideal;
its degree is the actual projective Hilbert degree, proved by closure. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

lemma projectiveClosure_union_chart {n : ℕ}
    (S : Finset (Ideal (CoordinatePolynomial n))) :
    affineProjectivePoint ⁻¹' (⋃ J ∈ S.image projectiveClosureIdeal,
      projectiveIdealZeroLocus J) = ⋃ I ∈ S, idealZeroLocus I := by
  classical
  ext a
  constructor
  · intro ha
    obtain ⟨J,hJ,haJ⟩ := Set.mem_iUnion₂.mp ha
    obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hJ
    exact Set.mem_iUnion₂.mpr ⟨I,hI,(projectiveClosureIdeal_chart_point I a).mp haJ⟩
  · intro ha
    obtain ⟨I,hI,haI⟩ := Set.mem_iUnion₂.mp ha
    exact Set.mem_iUnion₂.mpr ⟨projectiveClosureIdeal I,Finset.mem_image.mpr ⟨I,hI,rfl⟩,
      (projectiveClosureIdeal_chart_point I a).mpr haI⟩

/-- The paper's projective surface and actual projective curves, with the
integer-point count taken in x₀=1. Constants are chosen before the equation
and the box, and the hyperplane x₀=0 is required to intersect properly. -/
theorem projective_surface_salberger_cover (d : ℕ) (hd : 1 ≤ d) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (F : CoordinatePolynomial 4), F.IsHomogeneous d →
      Irreducible (map (algebraMap ℚ (AlgebraicClosure ℚ)) F) →
      (¬ X 0 ∣ F) → ∀ B : ℝ, 1 ≤ B →
      ∃ (S : Finset (Ideal (CoordinatePolynomial 4)))
        (δ : Ideal (CoordinatePolynomial 4) → ℕ),
        (∀ J ∈ S, J.IsPrime ∧
          IsHomogeneousIdeal J ∧
          (J.map (map (algebraMap ℚ (AlgebraicClosure ℚ)))).IsPrime ∧
          F ∈ J ∧ X 0 ∉ J ∧ 0 < δ J ∧ HasProjectiveCurveDegree J (δ J) ∧ δ J ≤ d ^ 2) ∧
        (S.card : ℝ) ≤ C * (B ^ (1 / Real.sqrt (d : ℝ)) * Real.log B + 1) ∧
        (count (smoothSurfaceLocus (affineChart 3 F) \
          affineProjectivePoint ⁻¹' (⋃ J ∈ S, projectiveIdealZeroLocus J)) B : ℝ) ≤
          C * B ^ (2 / Real.sqrt (d : ℝ) + c / Real.log (1 + Real.log B)) := by
  classical
  obtain ⟨C,c,hC,hc,hcover⟩ := rational_surface_salberger_cover d hd
  refine ⟨C,c,hC,hc,?_⟩
  intro F hhom habs hX B hB
  have hXK : ¬ X 0 ∣ map (algebraMap ℚ (AlgebraicClosure ℚ)) F := by
    intro hh
    apply hX
    have hmem : map (algebraMap ℚ (AlgebraicClosure ℚ)) F ∈
        (Ideal.span {(X 0 : CoordinatePolynomial 4)}).map
          (map (algebraMap ℚ (AlgebraicClosure ℚ))) := by
      simpa only [Ideal.map_span, Set.image_singleton, map_X, Ideal.mem_span_singleton] using hh
    exact Ideal.mem_span_singleton.mp
      ((mem_ideal_scalar_extension_iff (Ideal.span {X 0}) F).mp hmem)
  have hfabs : Irreducible (map (algebraMap ℚ (AlgebraicClosure ℚ)) (affineChart 3 F)) := by
    rw [← affineChart_map]
    exact affineChart_irreducible_of_not_variable_dvd _ (hhom.map _) habs hXK
  have hfdeg : (affineChart 3 F).totalDegree = d :=
    affineChart_degree_of_not_variable_dvd F hhom hX
  obtain ⟨T,δ,hT,hcard,hcount⟩ := hcover (affineChart 3 F) hfabs hfdeg B hB
  let e := @projectiveClosureIdeal ℚ _ 3
  let δ' := fun J => δ (Function.invFun e J)
  have hinj : Function.Injective e := projectiveClosureIdeal_injective
  have hleft : Function.LeftInverse (Function.invFun e) e := Function.leftInverse_invFun hinj
  refine ⟨T.image e,δ',?_,?_,?_⟩
  · intro J hJ
    obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hJ
    obtain ⟨hp,_,hf,hgeo,hpos,hdeg,hδ⟩ := hT I hI
    let : I.IsPrime := hp
    let : (I.map (map (algebraMap ℚ (AlgebraicClosure ℚ)))).IsPrime := hgeo
    have hδeq : δ' (e I) = δ I := congrArg δ (hleft I)
    rw [hδeq]
    exact ⟨inferInstance,projectiveClosureIdeal_homogeneous I,
      projectiveClosureIdeal_geometrically_prime (L := AlgebraicClosure ℚ) I,
      (homogeneous_mem_projectiveClosureIdeal_iff I F hhom).mpr hf,
      projectiveClosureIdeal_not_X_zero I,hpos,projectiveClosureIdeal_curveDegree I hdeg,hδ⟩
  · rw [Finset.card_image_of_injective T hinj]
    exact hcard
  · simpa only [e, projectiveClosure_union_chart] using hcount

end
end CCDN
