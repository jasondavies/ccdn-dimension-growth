module

public import AffineCurveCounting.ProjectivePlaneProjection
public import AffineCurveCounting.ProjectivePlaneLinearCount

/-! A projective curve with a proper standard chart reduces to a plane
equation of the same degree. Projection loses at most d(d-1) affine points
and at most d further points lie on the omitted hyperplane. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

lemma boundedHomogenize_irreducible {K : Type*} [Field K] {n : ℕ}
    (f : MvPolynomial (Fin n) K) (hf : Irreducible f) :
    Irreducible (boundedHomogenize f.totalDegree f) := by
  have hhom := boundedHomogenize_homogeneous f le_rfl
  have h0 : boundedHomogenize f.totalDegree f ≠ 0 := by
    intro h
    have hh := affineChart_boundedHomogenize f.totalDegree f
    rw [h, map_zero] at hh
    exact hf.ne_zero hh.symm
  apply irreducible_of_affineChart_irreducible
  · rw [affineChart_boundedHomogenize, hhom.totalDegree h0]
  · rwa [affineChart_boundedHomogenize]

theorem exists_projective_plane_count_reduction {n d : ℕ}
    (I : Ideal (CoordinatePolynomial (n + 1))) [I.IsPrime] (hX : X 0 ∉ I)
    (hd : 0 < d) (hdegree : HasProjectiveCurveDegree I d) :
    ∃ f : MvPolynomial (Fin 3) ℚ, f.IsHomogeneous d ∧ Irreducible f ∧
      ∀ B : ℝ, 1 ≤ B →
        projectiveCount (projectiveIdealZeroLocus I) B ≤
          projectiveCount (projectiveZeroLocus f) (projectionBoxFactor n d * B) + d ^ 2 := by
  classical
  let J := projectiveChartIdeal I
  have hJ : HasAffineCurveDegree J d := projectiveChartIdeal_degree I hX hdegree
  obtain ⟨k₀, k₁, f, hk₀, hk₁, hfir, hfd, hker, hcount⟩ :=
    exists_bounded_projection_card_le J d hd hJ
  have hfI : aeval ![momentCoordinate ℚ n k₀, momentCoordinate ℚ n k₁] f ∈ J :=
    (hker f).mpr dvd_rfl
  refine ⟨boundedHomogenize d f, boundedHomogenize_homogeneous f hfd.le,
    ?_, ?_⟩
  · simpa only [hfd] using boundedHomogenize_irreducible f hfir
  · intro B hB
    let S := projectivePoints (projectiveIdealZeroLocus I) B
    let T := S.filter (fun x => x.rep 0 ≠ 0)
    let U := S.filter (fun x => ¬ x.rep 0 ≠ 0)
    let R := T.image projectiveAffineCoordinates
    let π : RatPoint n → RatPoint 2 := fun z =>
      ![eval z (momentCoordinate ℚ n k₀), eval z (momentCoordinate ℚ n k₁)]
    have hR : ∀ z ∈ R, ∀ g ∈ J, eval z g = 0 := by
      intro z hz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨hxS, hx0⟩ := Finset.mem_filter.mp hx
      exact projectiveChartIdeal_point I hX x (mem_projectivePoints.mp hxS).2 hx0
    have hc := hcount R hR
    have hRT : R.card = T.card := by
      apply Finset.card_image_of_injOn
      intro x hx y hy he
      exact projectiveAffineCoordinates_injective (Finset.mem_filter.mp hx).2
        (Finset.mem_filter.mp hy).2 he
    change R.card ≤ (R.image π).card + d * (d - 1) at hc
    rw [hRT] at hc
    have himage : (R.image π).card ≤
        projectiveCount (projectiveZeroLocus (boundedHomogenize d f))
          (projectionBoxFactor n d * B) := by
      rw [← Finset.card_image_of_injective (R.image π) (affineProjectivePoint_injective 2)]
      apply Finset.card_le_card
      intro y hy
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨hxS, hx0⟩ := Finset.mem_filter.mp hx
      obtain ⟨hxB, hxI⟩ := mem_projectivePoints.mp hxS
      apply mem_projectivePoints.mpr
      exact ⟨projectivePlaneChartProjection_height hk₀ hk₁ x hx0 hB hxB,
        projectivePlaneChartProjection_zero I hX f hfd hfI x hxI hx0⟩
    have hU : U.card ≤ d := by
      have h := projective_section_card_le_degree I hdegree (X 0) (isHomogeneous_X _ _)
        hX (fun x : U => x.val) Subtype.val_injective
        (fun x => (mem_projectivePoints.mp (Finset.mem_filter.mp x.property).1).2)
        (fun x => by simpa using (Finset.mem_filter.mp x.property).2)
      simpa only [Fintype.card_coe, mul_one] using h
    have hsum : T.card + U.card = S.card := Finset.card_filter_add_card_filter_not _
    have hdcalc : d * (d - 1) + d = d ^ 2 := by
      have h := Nat.sub_add_cancel hd
      nlinarith
    change S.card ≤ _
    omega

end
end AffineCurveCounting
