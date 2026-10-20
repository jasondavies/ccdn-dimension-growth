module

public import AffineCurveCounting.BoundedMinorSpecialization
public import AffineCurveCounting.HypersurfacePositioning
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-! A single bounded linear elimination step. A chosen nonzero ideal equation
of degree d becomes monic after a linear coordinate change with integer
direction bounded by d+1. The quotient is integral over the remaining linear
coordinates. No bound on degrees of equations in subsequent contraction ideals
is asserted here. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

/-- A bounded integral direction simultaneously avoids the top form and the
coordinate hyperplane needed for an invertible linear substitution. -/
theorem exists_bounded_full_degree_direction {σ : Type*} [Fintype σ]
    (f : MvPolynomial (Option σ) ℚ) (hf : f ≠ 0) :
    ∃ b : Option σ → ℤ, (∀ i, 0 ≤ b i ∧ b i ≤ f.totalDegree + 1) ∧
      b none ≠ 0 ∧
      eval (fun i => (b i : ℚ)) (homogeneousComponent f.totalDegree f) ≠ 0 := by
  let P := X none * homogeneousComponent f.totalDegree f
  have hp : P ≠ 0 := mul_ne_zero (X_ne_zero none) (top_homogeneousComponent_ne_zero f hf)
  have hd : P.totalDegree ≤ f.totalDegree + 1 := by
    apply (totalDegree_mul _ _).trans
    rw [totalDegree_X]
    have hh := (homogeneousComponent_isHomogeneous f.totalDegree f).totalDegree_le
    omega
  obtain ⟨b, hb, hval⟩ := exists_integer_grid_rational_eval_ne_zero P hp _ hd
  change eval (fun i => (b i : ℚ))
    (X none * homogeneousComponent f.totalDegree f) ≠ 0 at hval
  rw [eval_mul, eval_X] at hval
  exact ⟨b, hb, by exact_mod_cast (mul_ne_zero_iff.mp hval).1,
    (mul_ne_zero_iff.mp hval).2⟩

/-- Bounded integer directions give an actual full-degree monic equation,
without an irreducibility or smooth-point assumption. -/
theorem exists_bounded_monic_linear_coordinates {σ : Type*} [Fintype σ]
    (f : MvPolynomial (Option σ) ℚ) (hf : f ≠ 0) :
    ∃ (b : Option σ → ℤ) (hb : (b none : ℚ) ≠ 0),
      (∀ i, 0 ≤ b i ∧ b i ≤ f.totalDegree + 1) ∧
      eval (fun i => (b i : ℚ)) (homogeneousComponent f.totalDegree f) ≠ 0 ∧
      (optionEquivLeft ℚ σ
        (normalizedHypersurfaceCoordinates 0 (fun i => (b i : ℚ)) hb f)).Monic ∧
      (optionEquivLeft ℚ σ
        (normalizedHypersurfaceCoordinates 0 (fun i => (b i : ℚ)) hb f)).natDegree =
        f.totalDegree ∧
      (normalizedHypersurfaceCoordinates 0 (fun i => (b i : ℚ)) hb f).totalDegree =
        f.totalDegree := by
  obtain ⟨b, hbound, hb, hdir⟩ := exists_bounded_full_degree_direction f hf
  have hbQ : (b none : ℚ) ≠ 0 := by exact_mod_cast hb
  refine ⟨b, hbQ, hbound, hdir,
    normalizedHypersurfaceCoordinates_monic 0 _ hbQ f hdir,
    normalizedHypersurfaceCoordinates_natDegree 0 _ hbQ f hdir, ?_⟩
  apply le_antisymm (normalizedHypersurfaceCoordinates_totalDegree_le 0 _ hbQ f)
  rw [← normalizedHypersurfaceCoordinates_natDegree 0 _ hbQ f hdir,
    natDegree_optionEquivLeft]
  exact degreeOf_le_totalDegree _ _

/-- The retained variables, transported back through the actual coordinate
automorphism, as elements of the original quotient. -/
def coordinateEliminationMap {K σ : Type*} [Field K]
    (I : Ideal (MvPolynomial (Option σ) K))
    (e : MvPolynomial (Option σ) K ≃ₐ[K] MvPolynomial (Option σ) K) :
    MvPolynomial σ K →ₐ[K] MvPolynomial (Option σ) K ⧸ I :=
  (Ideal.Quotient.mkₐ K I).comp (e.symm.toAlgHom.comp (rename some))

lemma coordinateEliminationMap_direction_X {K σ : Type*} [Field K]
    (I : Ideal (MvPolynomial (Option σ) K)) (b : Option σ → K)
    (hb : b none ≠ 0) (i : σ) :
    coordinateEliminationMap I (hypersurfaceAffineCoordinates 0 b hb) (X i) =
      (Ideal.Quotient.mk I) (X (some i) - C (b (some i) / b none) * X none) := by
  simp [coordinateEliminationMap, hypersurfaceAffineCoordinates,
    polynomialOriginShiftEquiv, directionCoordinates, directionCoordinatesInv,
    div_eq_mul_inv, map_mul, mul_assoc]

/-- A monic equation in the eliminated coordinate proves integrality over
the retained coordinates, for any ideal containing the equation. -/
theorem coordinateEliminationMap_isIntegral {K σ : Type*} [Field K]
    (I : Ideal (MvPolynomial (Option σ) K))
    (e : MvPolynomial (Option σ) K ≃ₐ[K] MvPolynomial (Option σ) K)
    (q : MvPolynomial (Option σ) K)
    (hq : q ∈ I.map e)
    (hm : (optionEquivLeft K σ q).Monic) :
    (coordinateEliminationMap I e).IsIntegral := by
  let E := e.trans (optionEquivLeft K σ)
  let J := I.map E
  have hJ : (optionEquivLeft K σ q) ∈ J := by
    change (optionEquivLeft K σ q) ∈ I.map
      ((optionEquivLeft K σ).toRingEquiv.toRingHom.comp e.toRingEquiv.toRingHom)
    rw [← Ideal.map_map]
    exact Ideal.mem_map_of_mem _ hq
  let φ := (Ideal.Quotient.mkₐ (MvPolynomial σ K) J).comp
    (Algebra.ofId (MvPolynomial σ K) (Polynomial (MvPolynomial σ K)))
  have hφ : φ.IsIntegral := hm.quotient_isIntegral hJ
  have hmap : J.map E.symm = I := by
    change Ideal.map E.symm.toRingEquiv.toRingHom
      (Ideal.map E.toRingEquiv.toRingHom I) = I
    rw [Ideal.map_map]
    have he : E.symm.toRingEquiv.toRingHom.comp E.toRingEquiv.toRingHom = RingHom.id _ :=
      E.toRingEquiv.symm_toRingHom_comp_toRingHom
    change I.map (E.symm.toRingEquiv.toRingHom.comp E.toRingEquiv.toRingHom) = I
    rw [he, Ideal.map_id]
  let ψ : (Polynomial (MvPolynomial σ K) ⧸ J) ≃ₐ[K]
      (MvPolynomial (Option σ) K ⧸ I) :=
    Ideal.quotientEquivAlg J I E.symm hmap.symm
  have hψ : RingHom.IsIntegral (R := Polynomial (MvPolynomial σ K) ⧸ J)
      (A := MvPolynomial (Option σ) K ⧸ I) ψ.toRingEquiv.toRingHom := by
    apply RingHom.isIntegral_of_surjective
    exact ψ.surjective
  have hint := RingHom.IsIntegral.trans (R := MvPolynomial σ K)
    (S := Polynomial (MvPolynomial σ K) ⧸ J)
    (T := MvPolynomial (Option σ) K ⧸ I)
    φ.toRingHom ψ.toRingEquiv.toRingHom hφ hψ
  have heq : ψ.toAlgHom.comp (φ.restrictScalars K) = coordinateEliminationMap I e := by
    ext i
    simp [φ, coordinateEliminationMap]
    rw [IsScalarTower.algebraMap_eq (MvPolynomial σ K)
      (Polynomial (MvPolynomial σ K)) (Polynomial (MvPolynomial σ K) ⧸ J)]
    change ψ (Ideal.Quotient.mk J (Polynomial.C (X i))) =
      (Ideal.Quotient.mk I) (e.symm (X (some i)))
    change (Ideal.Quotient.mk I) (E.symm (Polynomial.C (X i))) =
      (Ideal.Quotient.mk I) (e.symm (X (some i)))
    simp [E, optionEquivLeft_symm_C_X]
  change (ψ.toAlgHom.comp (φ.restrictScalars K)).IsIntegral at hint
  rwa [heq] at hint

/-- An actual bounded linear elimination for any ideal with a chosen nonzero
equation. Its remaining coordinates are linear forms in the original variables. -/
theorem exists_bounded_integral_linear_elimination {σ : Type*} [Fintype σ]
    (I : Ideal (MvPolynomial (Option σ) ℚ))
    (f : MvPolynomial (Option σ) ℚ) (hf : f ≠ 0) (hfi : f ∈ I) :
    ∃ (b : Option σ → ℤ) (hb : (b none : ℚ) ≠ 0),
      (∀ i, 0 ≤ b i ∧ b i ≤ f.totalDegree + 1) ∧
      (coordinateEliminationMap I
        (hypersurfaceAffineCoordinates 0 (fun i => (b i : ℚ)) hb)).IsIntegral := by
  obtain ⟨b, hb, hbound, _, hm, _, _⟩ := exists_bounded_monic_linear_coordinates f hf
  refine ⟨b, hb, hbound, ?_⟩
  apply coordinateEliminationMap_isIntegral I _
    (normalizedHypersurfaceCoordinates 0 (fun i => (b i : ℚ)) hb f) _ hm
  exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hfi)

end
end AffineCurveCounting
