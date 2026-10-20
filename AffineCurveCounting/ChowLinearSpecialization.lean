module

public import AffineCurveCounting.ProjectiveChowEquation
public import AffineCurveCounting.IntegralProjectionImage
public import AffineCurveCounting.HomogeneousProjectionNoBasePoint
public import AffineCurveCounting.HomogeneousProjectionEquation
public import AffineCurveCounting.BalancedParameterFiniteness

/-! Linear pullback of hyperplane tuples and actual image incidence under a
projection with center disjoint from the source. Integrality and lifting of
geometric image points are consequences of that geometric condition. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial Matrix

/-- Coordinate forms of an actual linear projection matrix. -/
def chowProjectionForms {K : Type*} [Field K] {n s : ℕ}
    (A : Matrix (Fin (s + 1)) (Fin (n + 1)) K) (i : Fin (s + 1)) :
    MvPolynomial (Fin (n + 1)) K := ∑ j, C (A i j) * X j

lemma chowProjectionForms_homogeneous {K : Type*} [Field K] {n s : ℕ}
    (A : Matrix (Fin (s + 1)) (Fin (n + 1)) K) (i : Fin (s + 1)) :
    (chowProjectionForms A i).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ (fun j _ => isHomogeneous_C_mul_X _ j)

lemma chowProjectionForms_eval {K : Type*} [Field K] {n s : ℕ}
    (A : Matrix (Fin (s + 1)) (Fin (n + 1)) K) (i : Fin (s + 1))
    (x : Fin (n + 1) → K) :
    eval x (chowProjectionForms A i) = (A *ᵥ x) i := by
  simp [chowProjectionForms, Matrix.mulVec, dotProduct]

/-- Pullback of actual target hyperplane coefficients along the matrix. -/
def chowPullbackCoefficients {K : Type*} [Field K] {n s r : ℕ}
    (A : Matrix (Fin (s + 1)) (Fin (n + 1)) K)
    (U : Fin r × Fin (s + 1) → K) (q : Fin r × Fin (n + 1)) : K :=
  ∑ k, U (q.1,k) * A k q.2

/-- Substitution in the source Chow equation induced by an actual projection. -/
def chowLinearSubstitution {K : Type*} [Field K] {n s r : ℕ}
    (A : Matrix (Fin (s + 1)) (Fin (n + 1)) K) :
    MvPolynomial (Fin r × Fin (n + 1)) K →ₐ[K]
      MvPolynomial (Fin r × Fin (s + 1)) K :=
  aeval (fun q => ∑ k, C (A k q.2) * X (q.1,k))

lemma chowLinearSubstitution_eval {K : Type*} [Field K] {n s r : ℕ}
    (A : Matrix (Fin (s + 1)) (Fin (n + 1)) K)
    (F : MvPolynomial (Fin r × Fin (n + 1)) K)
    (U : Fin r × Fin (s + 1) → K) :
    eval U (chowLinearSubstitution A F) = eval (chowPullbackCoefficients A U) F := by
  change eval U (eval₂ C _ F) = _
  rw [← eval_assoc]
  congr 1
  congr 1
  funext q
  simp [chowPullbackCoefficients, mul_comm]

lemma chowPullbackCoefficients_relation {K : Type*} [Field K] {n s r : ℕ}
    (A : Matrix (Fin (s + 1)) (Fin (n + 1)) K)
    (U : Fin r × Fin (s + 1) → K) (x : Fin (n + 1) → K) (i : Fin r) :
    ∑ j, chowPullbackCoefficients A U (i,j) * x j = ∑ k, U (i,k) * (A *ᵥ x) k := by
  simp only [chowPullbackCoefficients, Finset.sum_mul, Matrix.mulVec, dotProduct,
    Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]

/-- The actual homogeneous image ideal of the matrix projection. -/
def chowProjectionImageIdeal {K : Type*} [Field K] {n s : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) K))
    (A : Matrix (Fin (s + 1)) (Fin (n + 1)) K) :
    Ideal (MvPolynomial (Fin (s + 1)) K) :=
  RingHom.ker (projectionCoordinateMap J (chowProjectionForms A))

lemma chowProjectionImageIdeal_homogeneous {K : Type*} [Field K] {n s : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hJ : ∀ f ∈ J, ∀ M, homogeneousComponent M f ∈ J)
    (A : Matrix (Fin (s + 1)) (Fin (n + 1)) K) :
    ∀ f ∈ chowProjectionImageIdeal J A, ∀ M,
      homogeneousComponent M f ∈ chowProjectionImageIdeal J A :=
  projection_kernel_homogeneousComponent_mem J hJ _ (chowProjectionForms_homogeneous A)

/-- Disjointness from the actual projective center implies integrality; it is
not an extra finiteness hypothesis. -/
theorem chow_projection_integral_of_center_disjoint
    {K : Type*} [Field K] [IsAlgClosed K] {n s : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hJ : ∀ f ∈ J, ∀ M, homogeneousComponent M f ∈ J)
    (A : Matrix (Fin (s + 1)) (Fin (n + 1)) K)
    (hcenter : ∀ p ∈ projectiveIdealZeroLocus J, A *ᵥ p.rep ≠ 0) :
    (projectionCoordinateMap J (chowProjectionForms A)).IsIntegral := by
  apply integral_projection_of_homogeneous_origin_fiber (L := K) J hJ _
    (chowProjectionForms_homogeneous A)
  intro x hx
  by_contra hx0
  have hxJ : ∀ f ∈ J, eval x f = 0 := fun f hf => hx f (Ideal.mem_sup_left hf)
  have hxA : A *ᵥ x = 0 := by
    funext i
    rw [← chowProjectionForms_eval]
    exact hx _ (Ideal.mem_sup_right (Ideal.subset_span ⟨i,rfl⟩))
  have hinc : (fun q : Fin (s + 1) × Fin (n + 1) => A q.1 q.2) ∈
      projectiveChowIncidenceLocus (s + 1) J := by
    apply (projectiveChowIncidenceLocus_iff_cone J hJ _).mpr
    refine ⟨x, hx0, hxJ, ?_⟩
    intro i
    exact congrFun hxA i
  obtain ⟨p, hp, hrel⟩ := hinc
  apply hcenter p hp
  funext i
  exact hrel i

/-- Every nonzero point of the actual image cone has an actual nonzero source
point, and conversely; no closure or dominance premise replaces the image. -/
theorem chow_projection_cone_image_iff
    {K : Type*} [Field K] [IsAlgClosed K] {n s : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) K))
    (A : Matrix (Fin (s + 1)) (Fin (n + 1)) K)
    (hint : (projectionCoordinateMap J (chowProjectionForms A)).IsIntegral)
    (y : Fin (s + 1) → K) (hy : y ≠ 0) :
    (∀ f ∈ chowProjectionImageIdeal J A, eval y f = 0) ↔
      ∃ x : Fin (n + 1) → K, x ≠ 0 ∧ (∀ f ∈ J, eval x f = 0) ∧ A *ᵥ x = y := by
  constructor
  · intro hz
    obtain ⟨x, hxJ, he⟩ := exists_point_of_integral_projection_kernel_zero J
      (chowProjectionForms A) hint y hz
    have hxy : A *ᵥ x = y := funext (fun i => (chowProjectionForms_eval A i x).symm.trans (he i))
    refine ⟨x, ?_, hxJ, hxy⟩
    intro hx
    apply hy
    simpa only [hx, Matrix.mulVec_zero] using hxy.symm
  · rintro ⟨x, _, hx, rfl⟩ f hf
    have hh := hx (aeval (chowProjectionForms A) f)
      ((mem_projectionCoordinateMap_ker J _ f).mp hf)
    change (aeval x) ((aeval (chowProjectionForms A)) f) = 0 at hh
    rw [comp_aeval_apply] at hh
    simpa only [aeval_eq_eval, chowProjectionForms_eval] using hh

/-- The pulled-back tuple meets the source exactly when the target tuple
meets the actual image. The center is assumed geometrically disjoint, and
integrality and point lifting are proved from that assumption. -/
theorem chow_projection_incidence_iff
    {K : Type*} [Field K] [IsAlgClosed K] {n s r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hJ : ∀ f ∈ J, ∀ M, homogeneousComponent M f ∈ J)
    (A : Matrix (Fin (s + 1)) (Fin (n + 1)) K)
    (hcenter : ∀ p ∈ projectiveIdealZeroLocus J, A *ᵥ p.rep ≠ 0)
    (U : Fin r × Fin (s + 1) → K) :
    chowPullbackCoefficients A U ∈ projectiveChowIncidenceLocus r J ↔
      U ∈ projectiveChowIncidenceLocus r (chowProjectionImageIdeal J A) := by
  have hint := chow_projection_integral_of_center_disjoint J hJ A hcenter
  rw [projectiveChowIncidenceLocus_iff_cone J hJ,
    projectiveChowIncidenceLocus_iff_cone _ (chowProjectionImageIdeal_homogeneous J hJ A)]
  constructor
  · rintro ⟨x, hx, hxJ, hrel⟩
    have hAx : A *ᵥ x ≠ 0 := by
      intro hz
      apply hx
      apply homogeneous_integral_projection_zero_fiber (L := K) J hJ
        (chowProjectionForms A) (chowProjectionForms_homogeneous A) hint x hxJ
      intro i
      simpa only [aeval_eq_eval, chowProjectionForms_eval, Pi.zero_apply] using congrFun hz i
    refine ⟨A *ᵥ x, hAx, (chow_projection_cone_image_iff J A hint _ hAx).mpr
      ⟨x, hx, hxJ, rfl⟩, ?_⟩
    intro i
    rw [← chowPullbackCoefficients_relation]
    exact hrel i
  · rintro ⟨y, hy, hyJ, hrel⟩
    obtain ⟨x, hx, hxJ, rfl⟩ := (chow_projection_cone_image_iff J A hint y hy).mp hyJ
    refine ⟨x, hx, hxJ, ?_⟩
    intro i
    rw [chowPullbackCoefficients_relation]
    exact hrel i

end
end AffineCurveCounting
