module

public import CCDN.HomogeneousCurveHilbert
public import CCDN.HomogeneousPrimeComponents
public import CCDN.ProjectiveCoefficientExtension
public import CCDN.TopFormIrreducibility

/-! Height-independent quadratic-degree bounds for the projective curve
cases of CCDN 4.1.5. Homogeneous separators and all scalar-extension point
maps are constructed internally. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

lemma exists_homogeneous_component_not_mem
    {K σ : Type*} [Field K] (I : Ideal (MvPolynomial σ K))
    (f : MvPolynomial σ K) (hf : f ∉ I) :
    ∃ N ≤ f.totalDegree, homogeneousComponent N f ∉ I := by
  classical
  by_contra! h
  apply hf
  rw [← sum_homogeneousComponent f]
  apply I.sum_mem
  intro N hN
  exact h N (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hN)

theorem non_rational_projective_curve_count_le_degree_sq
    {K : Type*} [Field K] [Algebra ℚ K] [IsAlgClosed K] [IsGalois ℚ K]
    {n : ℕ} (I : Ideal (MvPolynomial (Fin (n + 1)) K)) [I.IsPrime]
    (hI : ∀ f ∈ I, ∀ N, homogeneousComponent N f ∈ I)
    (d : ℕ) (hdim : (filteredHilbertPolynomial I).natDegree = 2)
    (hdegree : (filteredHilbertPolynomial I).leadingCoeff = (d : ℚ) / 2)
    (hundef : ¬ ∃ J : Ideal (CoordinatePolynomial (n + 1)),
      J.map (map (algebraMap ℚ K)) = I) (B : ℝ) :
    projectiveCount (rationalProjectiveIdealZeroLocusOver I) B ≤ d ^ 2 := by
  classical
  let : CharZero K := Algebra.charZero_of_charZero ℚ K
  obtain ⟨γ, hγ⟩ := exists_galois_moving_polynomial_ideal ℚ K I
    (fun h => hundef ⟨I.comap (map (algebraMap ℚ K)), h⟩)
  let J := I.map (mapEquiv (Fin (n + 1)) γ.toRingEquiv)
  let : J.IsPrime := Ideal.map_isPrime_of_equiv _
  have hJmap : J = I.map (map γ.toRingHom) := by
    dsimp only [J]
    rw [← Ideal.map_coe]
    congr 1
  have hJne : J ≠ I := by rwa [hJmap]
  have hpoly : filteredHilbertPolynomial J = filteredHilbertPolynomial I :=
    filteredHilbertPolynomial_coefficientEquiv I γ.toRingEquiv
  have hJdim : (filteredHilbertPolynomial J).natDegree = 2 := by rwa [hpoly]
  have hJhom : ∀ f ∈ J, ∀ N, homogeneousComponent N f ∈ J := by
    intro f hf N
    rw [hJmap] at hf ⊢
    obtain ⟨g, hg, rfl⟩ := (Ideal.mem_map_iff_of_surjective
      (map γ.toRingHom) (map_surjective _ γ.surjective)).mp hf
    rw [← map_homogeneousComponent]
    exact Ideal.mem_map_of_mem _ (hI g hg N)
  have hnot : ¬ J ≤ I :=
    prime_ideal_not_le_of_same_positive_dimension J I hJdim hdim hJne
  obtain ⟨f, hfJ, hfd, hfI⟩ := exists_low_degree_ideal_separator J I d
    (by rw [hpoly, hdim]; simpa using hdegree) hnot
  obtain ⟨N, hN, hNI⟩ := exists_homogeneous_component_not_mem I f hfI
  let g := homogeneousComponent N f
  have hgJ : g ∈ J := hJhom f hfJ N
  have hg : g.IsHomogeneous N := homogeneousComponent_isHomogeneous _ _
  let S := projectivePoints (rationalProjectiveIdealZeroLocusOver I) B
  let z : S → Projectivization K (Fin (n + 1) → K) :=
    fun x => projectiveCoefficientExtension ℚ K (Fin (n + 1)) x.val
  have hinj : Function.Injective z :=
    (projectiveCoefficientExtension_injective ℚ K (Fin (n + 1))).comp Subtype.val_injective
  have hzI (x : S) : z x ∈ projectiveIdealZeroLocus I :=
    projectiveCoefficientExtension_mem_ideal I hI x.val (mem_projectivePoints.mp x.property).2
  have hxJ (x : S) : x.val ∈ rationalProjectiveIdealZeroLocusOver J := by
    intro v hv he q hq
    rw [hJmap] at hq
    obtain ⟨p, hp, rfl⟩ := (Ideal.mem_map_iff_of_surjective
      (map γ.toRingHom) (map_surjective _ γ.surjective)).mp hq
    rw [eval_coefficient_galois_at_base_point,
      (mem_projectivePoints.mp x.property).2 v hv he p hp, map_zero]
  have hzg (x : S) : eval (z x).rep g = 0 :=
    projectiveIdealZeroLocus_rep
      (projectiveCoefficientExtension_mem_ideal J hJhom x.val (hxJ x)) g hgJ
  have hh := projective_section_card_le_degree I
    (projectiveCurveDegree_of_filteredHilbertPolynomial I hI d hdim hdegree)
    g hg hNI z hinj hzI hzg
  have hNd : N ≤ d := hN.trans hfd
  have hcount : projectiveCount (rationalProjectiveIdealZeroLocusOver I) B ≤ d * N := by
    simpa only [Fintype.card_coe, S, projectiveCount] using hh
  exact hcount.trans (by simpa only [pow_two] using Nat.mul_le_mul_left d hNd)

theorem nonabsolute_projective_curve_count_le_degree_sq
    {K : Type*} [Field K] [Algebra ℚ K] [IsAlgClosed K] [IsGalois ℚ K]
    {n : ℕ} (I : Ideal (CoordinatePolynomial (n + 1))) [I.IsPrime]
    (hI : ∀ f ∈ I, ∀ N, homogeneousComponent N f ∈ I)
    (d : ℕ) (hdim : (filteredHilbertPolynomial I).natDegree = 2)
    (hdegree : (filteredHilbertPolynomial I).leadingCoeff = (d : ℚ) / 2)
    (hred : ¬ (I.map (map (algebraMap ℚ K))).IsPrime) (B : ℝ) :
    projectiveCount (projectiveIdealZeroLocus I) B ≤ d ^ 2 := by
  obtain ⟨P, hP⟩ := Ideal.nonempty_minimalPrimes
    (scalar_extension_ideal_ne_top (K := K) I (Ideal.IsPrime.ne_top ‹I.IsPrime›))
  let : P.IsPrime := hP.isPrime
  obtain ⟨e, _, hed, hedim, hedegree⟩ :=
    algebraic_component_degree_le ℚ K I d hdim (by simpa using hdegree) P hP
  have hPhom := minimal_prime_ideal_homogeneous _
    (scalar_extension_ideal_homogeneous I hI) P hP
  have hsubset : projectiveIdealZeroLocus I ⊆ rationalProjectiveIdealZeroLocusOver P := by
    intro x hx v hv he
    exact galois_base_point_on_every_component ℚ K I P hP v (hx v hv he)
  have hh := non_rational_projective_curve_count_le_degree_sq P hPhom e hedim
    (by simpa using hedegree) (galois_component_not_defined_over_base ℚ K I hred P hP) B
  exact (projectiveCount_mono hsubset le_rfl).trans (hh.trans (Nat.pow_le_pow_left hed 2))

end
end CCDN
