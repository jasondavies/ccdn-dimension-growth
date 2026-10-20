module

public import AffineCurveCounting.GeometricCurveProjection
public import AffineCurveCounting.ProjectiveChartScalarExtension
public import AffineCurveCounting.AffineProjectionCount
public import AffineCurveCounting.ProjectiveProjectionCount

/-! The same explicitly constructed geometrically integral plane curve
has the source degree, source function field and the additive point-count
comparison in Propositions 4.3.1 and 4.3.2. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

theorem affine_curve_count_le_of_moment_projection {n d k₀ k₁ : ℕ}
    (I : Ideal (CoordinatePolynomial n))
    (f : MvPolynomial (Fin 2) ℚ)
    (hk₀ : k₀ ≤ n ^ 2 * d) (hk₁ : k₁ ≤ n * d ^ 2)
    (hker : ∀ g, aeval ![momentCoordinate ℚ n k₀, momentCoordinate ℚ n k₁] g ∈ I ↔ f ∣ g)
    (hcount : ∀ S : Finset (Fin n → ℚ), (∀ z ∈ S, ∀ g ∈ I, eval z g = 0) →
      S.card ≤ (S.image (fun z i =>
        eval z (![momentCoordinate ℚ n k₀, momentCoordinate ℚ n k₁] i))).card + d * (d - 1))
    (B : ℝ) (hB : 1 ≤ B) :
    count (idealZeroLocus I) B ≤
      count (zeroLocus f) (projectionBoxFactor n d * B) + d * (d - 1) := by
  classical
  let S := integralPoints (idealZeroLocus I) B
  let R := S.image rationalPoint
  let π : RatPoint n → RatPoint 2 := fun z =>
    ![eval z (momentCoordinate ℚ n k₀), eval z (momentCoordinate ℚ n k₁)]
  let P := S.image (degreeProjection n k₀ k₁)
  have hR : ∀ z ∈ R, ∀ g ∈ I, eval z g = 0 := by
    intro w hw
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
    exact (mem_integralPoints.mp hz).2
  have hc := hcount R hR
  have hRcard : R.card = S.card := Finset.card_image_of_injective S (rationalPoint_injective n)
  have himg : R.image π = P.image rationalPoint := by
    simp only [R, P, Finset.image_image]
    congr 1
    funext z
    exact (rationalPoint_degreeProjection z).symm
  have hπ : (fun z i => eval z
      (![momentCoordinate ℚ n k₀, momentCoordinate ℚ n k₁] i)) = π := by
    funext z i
    fin_cases i <;> rfl
  rw [hπ, hRcard, himg, Finset.card_image_of_injective P (rationalPoint_injective 2)] at hc
  have hP : P ⊆ integralPoints (zeroLocus f) (projectionBoxFactor n d * B) := by
    rintro _ hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
    have hzbox := mem_integerBox.mpr (mem_integralPoints.mp hz).1
    apply mem_integralPoints.mpr
    refine ⟨mem_integerBox.mp (degreeProjection_box hk₀ hk₁ (by linarith) hzbox), ?_⟩
    change eval (rationalPoint (degreeProjection n k₀ k₁ z)) f = 0
    rw [rationalPoint_degreeProjection]
    have hfI := (hker f).mpr (dvd_refl f)
    have hh := (mem_integralPoints.mp hz).2 _ hfI
    rw [eval_polynomial_coordinate_map] at hh
    convert hh using 1
    congr 2
    funext j
    fin_cases j <;> rfl
  exact hc.trans (Nat.add_le_add_right (Finset.card_le_card hP) _)

/-- The affine curve clause of Proposition 4.3.1, retaining explicit
birational projection coordinates and the stronger error d(d-1). -/
theorem exists_geometric_affine_curve_count_reduction
    {L : Type*} [Field L] [Algebra ℚ L] {n : ℕ}
    (I : Ideal (CoordinatePolynomial n)) [I.IsPrime]
    [(I.map (map (algebraMap ℚ L))).IsPrime]
    (d : ℕ) (hd : 0 < d) (hdegree : HasAffineCurveDegree I d) :
    ∃ (k₀ k₁ : ℕ) (f : MvPolynomial (Fin 2) ℚ),
      k₀ ≤ n ^ 2 * d ∧ k₁ ≤ n * d ^ 2 ∧ Irreducible f ∧
      Irreducible (map (algebraMap ℚ L) f) ∧ f.totalDegree = d ∧
      let a := ![momentCoordinate ℚ n k₀, momentCoordinate ℚ n k₁]
      (∀ g, aeval a g ∈ I ↔ f ∣ g) ∧
      IntermediateField.adjoin ℚ
        (Set.range (fun i => algebraMap (CoordinatePolynomial n ⧸ I)
          (FractionRing (CoordinatePolynomial n ⧸ I))
          ((Ideal.Quotient.mk I) (a i)))) = ⊤ ∧
      ∀ B : ℝ, 1 ≤ B → count (idealZeroLocus I) B ≤
        count (zeroLocus f) (projectionBoxFactor n d * B) + d * (d - 1) := by
  obtain ⟨k₀, k₁, f, hk₀, hk₁, hf, hfL, hfd, hker, hfield, _, _, hcount⟩ :=
    exists_geometrically_integral_curve_projection (L := L) I d hd hdegree
  exact ⟨k₀, k₁, f, hk₀, hk₁, hf, hfL, hfd, hker, hfield,
    affine_curve_count_le_of_moment_projection I f hk₀ hk₁ hker hcount⟩

theorem projective_curve_count_le_of_moment_projection {n d k₀ k₁ : ℕ}
    (I : Ideal (CoordinatePolynomial (n + 1))) [I.IsPrime] (hX : X 0 ∉ I)
    (hd : 0 < d) (hdegree : HasProjectiveCurveDegree I d)
    (f : MvPolynomial (Fin 2) ℚ) (hfd : f.totalDegree = d)
    (hk₀ : k₀ ≤ n ^ 2 * d) (hk₁ : k₁ ≤ n * d ^ 2)
    (hfI : aeval ![momentCoordinate ℚ n k₀, momentCoordinate ℚ n k₁] f ∈ projectiveChartIdeal I)
    (hcount : ∀ S : Finset (Fin n → ℚ),
      (∀ z ∈ S, ∀ g ∈ projectiveChartIdeal I, eval z g = 0) →
      S.card ≤ (S.image (fun z i =>
        eval z (![momentCoordinate ℚ n k₀, momentCoordinate ℚ n k₁] i))).card + d * (d - 1))
    (B : ℝ) (hB : 1 ≤ B) :
    projectiveCount (projectiveIdealZeroLocus I) B ≤
      projectiveCount (projectiveZeroLocus (boundedHomogenize d f))
        (projectionBoxFactor n d * B) + d ^ 2 := by
  classical
  let S := projectivePoints (projectiveIdealZeroLocus I) B
  let T := S.filter (fun x => x.rep 0 ≠ 0)
  let U := S.filter (fun x => ¬ x.rep 0 ≠ 0)
  let R := T.image projectiveAffineCoordinates
  let π : RatPoint n → RatPoint 2 := fun z =>
    ![eval z (momentCoordinate ℚ n k₀), eval z (momentCoordinate ℚ n k₁)]
  have hR : ∀ z ∈ R, ∀ g ∈ projectiveChartIdeal I, eval z g = 0 := by
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
  have hπ : (fun z i => eval z
      (![momentCoordinate ℚ n k₀, momentCoordinate ℚ n k₁] i)) = π := by
    funext z i
    fin_cases i <;> rfl
  rw [hπ, hRT] at hc
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
    exact mem_projectivePoints.mpr
      ⟨projectivePlaneChartProjection_height hk₀ hk₁ x hx0 hB hxB,
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

/-- The projective curve clause of Proposition 4.3.2 on a proper standard
chart. The affine plane equation generates exactly the chart function field;
its projective closure stays irreducible after extending coefficients. -/
theorem exists_geometric_projective_curve_count_reduction_of_chart
    {L : Type*} [Field L] [Algebra ℚ L] {n d : ℕ}
    (I : Ideal (CoordinatePolynomial (n + 1))) [I.IsPrime]
    [(I.map (map (algebraMap ℚ L))).IsPrime]
    (hX : X 0 ∉ I) (hd : 0 < d) (hdegree : HasProjectiveCurveDegree I d) :
    ∃ (k₀ k₁ : ℕ) (f : MvPolynomial (Fin 2) ℚ),
      k₀ ≤ n ^ 2 * d ∧ k₁ ≤ n * d ^ 2 ∧ Irreducible f ∧ f.totalDegree = d ∧
      let J := projectiveChartIdeal I
      let a := ![momentCoordinate ℚ n k₀, momentCoordinate ℚ n k₁]
      (∀ g, aeval a g ∈ J ↔ f ∣ g) ∧
      IntermediateField.adjoin ℚ
        (Set.range (fun i => algebraMap (CoordinatePolynomial n ⧸ J)
          (FractionRing (CoordinatePolynomial n ⧸ J))
          ((Ideal.Quotient.mk J) (a i)))) = ⊤ ∧
      (boundedHomogenize d f).IsHomogeneous d ∧
      Irreducible (boundedHomogenize d f) ∧
      Irreducible (map (algebraMap ℚ L) (boundedHomogenize d f)) ∧
      ∀ B : ℝ, 1 ≤ B → projectiveCount (projectiveIdealZeroLocus I) B ≤
        projectiveCount (projectiveZeroLocus (boundedHomogenize d f))
          (projectionBoxFactor n d * B) + d ^ 2 := by
  let J := projectiveChartIdeal I
  let : (J.map (map (algebraMap ℚ L))).IsPrime :=
    projectiveChartIdeal_geometrically_prime I hX
  obtain ⟨k₀, k₁, f, hk₀, hk₁, hf, hfL, hfd, hker, hfield, _, _, hcount⟩ :=
    exists_geometrically_integral_curve_projection (L := L) J d hd
      (projectiveChartIdeal_degree I hX hdegree)
  refine ⟨k₀, k₁, f, hk₀, hk₁, hf, hfd, hker, hfield,
    boundedHomogenize_homogeneous f hfd.le, ?_, ?_, ?_⟩
  · simpa only [hfd] using boundedHomogenize_irreducible f hf
  · rw [← scaledHomogenize_one, scaledHomogenize_map, map_one, scaledHomogenize_one]
    have hdeg : (map (algebraMap ℚ L) f).totalDegree = d := by
      unfold totalDegree
      rw [support_map_of_injective _ (algebraMap ℚ L).injective]
      exact hfd
    simpa only [hdeg] using boundedHomogenize_irreducible _ hfL
  · exact projective_curve_count_le_of_moment_projection I hX hd hdegree f hfd hk₀ hk₁
      ((hker f).mpr dvd_rfl) hcount

end
end AffineCurveCounting
