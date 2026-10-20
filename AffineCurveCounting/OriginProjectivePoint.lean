module

public import AffineCurveCounting.ProjectiveClosureHilbertPolynomial
public import AffineCurveCounting.HypersurfaceOriginStalk

/-! The actual projective closure of the affine origin is geometrically
prime and has projective dimension zero and degree one. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

lemma idealOfVars_scalar_extension {K L σ : Type*}
    [Field K] [Field L] [Algebra K L] :
    (idealOfVars σ K).map (map (algebraMap K L)) = idealOfVars σ L := by
  rw [idealOfVars, Ideal.map_span]
  congr 1
  ext f
  simp only [Set.mem_image, Set.mem_range]
  constructor
  · rintro ⟨_, ⟨i,rfl⟩,rfl⟩
    exact ⟨i,(map_X _ _).symm⟩
  · rintro ⟨i,rfl⟩
    exact ⟨X i,⟨i,rfl⟩,map_X _ _⟩

theorem idealOfVars_filtered_finrank {K σ : Type*}
    [Field K] [Fintype σ] (N : ℕ) :
    Module.finrank K (filteredCoordinateSpace (idealOfVars σ K) N) = 1 := by
  let I := idealOfVars σ K
  have heval : RingHom.ker (aeval (0 : σ → K)) = I := by
    change RingHom.ker (aeval (0 : σ → K)) = idealOfVars σ K
    rw [idealOfVars_eq_ker_constantCoeff]
    ext f
    simp only [RingHom.mem_ker, aeval_zero,
      Algebra.algebraMap_self, RingHom.id_apply]
  let e := Ideal.quotientKerAlgEquivOfSurjective
    (f := aeval (0 : σ → K)) (fun c => ⟨C c, by simp⟩)
  have htop : filteredCoordinateSpace I N = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨f,rfl⟩ := Ideal.Quotient.mk_surjective x
    refine Submodule.mem_map.mpr ⟨C (constantCoeff f), ?_, ?_⟩
    · exact (mem_restrictTotalDegree _ _ _).mpr (by simp)
    · apply Ideal.Quotient.eq.mpr
      rw [show I = RingHom.ker constantCoeff from idealOfVars_eq_ker_constantCoeff]
      change constantCoeff (C (constantCoeff f) - f) = 0
      simp
  rw [htop, finrank_top]
  let e' := (Ideal.quotientEquivAlgOfEq K heval.symm).trans e
  simpa using e'.toLinearEquiv.finrank_eq

theorem idealOfVars_filteredHilbertPolynomial {K σ : Type*}
    [Field K] [Fintype σ] [LinearOrder σ] :
    filteredHilbertPolynomial (idealOfVars σ K) = 1 := by
  apply filteredHilbertPolynomial_eq_of_eventual
  exact ⟨0, fun N _ => by rw [idealOfVars_filtered_finrank]; simp⟩

def originProjectiveIdeal (K : Type*) [Field K] (n : ℕ) :
    Ideal (MvPolynomial (Fin (n + 1)) K) :=
  projectiveClosureIdeal (idealOfVars (Fin n) K)

instance originProjectiveIdeal_isPrime {K : Type*} [Field K] {n : ℕ} :
    (originProjectiveIdeal K n).IsPrime := by
  let : (idealOfVars (Fin n) K).IsPrime := idealOfVars_isMaximal.isPrime
  exact projectiveClosureIdeal_isPrime _

theorem originProjectiveIdeal_geometrically_prime {K L : Type*}
    [Field K] [Field L] [Algebra K L] (n : ℕ) :
    ((originProjectiveIdeal K n).map (map (algebraMap K L))).IsPrime := by
  unfold originProjectiveIdeal
  rw [projectiveClosureIdeal_scalar_extension, idealOfVars_scalar_extension]
  exact originProjectiveIdeal_isPrime

theorem originProjectiveIdeal_hilbert_parameters {K : Type*} [Field K] (n : ℕ) :
    (filteredHilbertPolynomial (originProjectiveIdeal K n)).natDegree = 1 ∧
      (filteredHilbertPolynomial (originProjectiveIdeal K n)).leadingCoeff = 1 := by
  let : (idealOfVars (Fin n) K).IsPrime := idealOfVars_isMaximal.isPrime
  simpa [originProjectiveIdeal] using
    projectiveClosureIdeal_hilbertPolynomial_parameters (idealOfVars (Fin n) K) 0 1
    (by rw [idealOfVars_filteredHilbertPolynomial]; simp)
    (by rw [idealOfVars_filteredHilbertPolynomial]; simp)

theorem originProjectiveIdeal_chart_point {K : Type*} [Field K] {n : ℕ}
    (a : Fin n → K) :
    affineProjectivePoint a ∈ projectiveIdealZeroLocus (originProjectiveIdeal K n) ↔ a = 0 := by
  rw [originProjectiveIdeal, projectiveClosureIdeal_chart_point]
  constructor
  · intro h
    funext i
    simpa only [eval_X, Pi.zero_apply] using
      h (X i) (Ideal.subset_span ⟨i,rfl⟩)
  · rintro rfl f hf
    rw [idealOfVars_eq_ker_constantCoeff] at hf
    simpa only [eval_zero, RingHom.mem_ker] using hf

theorem originProjectiveIdeal_locus {K : Type*} [Field K] (n : ℕ) :
    projectiveIdealZeroLocus (originProjectiveIdeal K n) =
      {affineProjectivePoint (0 : Fin n → K)} := by
  ext x
  constructor
  · intro hx
    have hs (i : Fin n) : x.rep i.succ = 0 := by
      have hXi : X i.succ ∈ originProjectiveIdeal K n := by
        rw [originProjectiveIdeal, homogeneous_mem_projectiveClosureIdeal_iff _ _
          (isHomogeneous_X K i.succ)]
        simp only [affineChart, eval₂Hom_X', Fin.cons_succ]
        exact Ideal.subset_span ⟨i,rfl⟩
      simpa only [eval_X] using projectiveIdealZeroLocus_rep hx _ hXi
    have h0 : x.rep 0 ≠ 0 := by
      intro h
      apply x.rep_nonzero
      funext i
      exact Fin.cases h hs i
    have ha : projectiveAffineCoordinates x = 0 := by
      funext i
      simp only [projectiveAffineCoordinates, hs, zero_div, Pi.zero_apply]
    have he := projectiveAffineCoordinates_mk x h0
    rw [ha] at he
    exact Set.mem_singleton_iff.mpr he.symm
  · rintro rfl
    exact (originProjectiveIdeal_chart_point 0).mpr rfl

end
end AffineCurveCounting
