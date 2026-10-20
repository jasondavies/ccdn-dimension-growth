module

public import CCDN.ZeroDimensionalGeometricPoint
public import CCDN.GeometricAffineProjection
public import CCDN.OriginProjectivePoint

/-! The zero-dimensional boundary of the actual affine projection theorem.
The source is a rational point; the zero integer projection maps it finitely
and birationally to the origin in the affine line. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

theorem exists_geometric_affine_projection_zero_dimension
    {L : Type*} [Field L] [Algebra ℚ L] [IsAlgClosed L] [IsGalois ℚ L]
    (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℚ)) [I.IsPrime]
    [(I.map (map (algebraMap ℚ L))).IsPrime]
    (d : ℕ) (hdim : (filteredHilbertPolynomial I).natDegree = 0)
    (hdegree : (filteredHilbertPolynomial I).leadingCoeff = d) :
    ∃ b : Fin 1 → Fin n → ℤ,
      (∀ i j, |b i j| ≤ integerBirationalProjectionHeight n d) ∧
      (projectionCoordinateMap I (fun i => integerLinearForm (b i))).IsIntegral ∧
      IntermediateField.adjoin ℚ
        (Set.range (fun i => algebraMap (MvPolynomial (Fin n) ℚ ⧸ I)
          (FractionRing (MvPolynomial (Fin n) ℚ ⧸ I))
          ((Ideal.Quotient.mk I) (integerLinearForm (b i))))) = ⊤ ∧
      ∃ f : MvPolynomial (Fin 1) ℚ,
        Irreducible f ∧ Irreducible (map (algebraMap ℚ L) f) ∧ f.totalDegree = d ∧
        RingHom.ker (projectionCoordinateMap I (fun i => integerLinearForm (b i))) =
          Ideal.span {f} ∧
        ∀ B : ℝ, 1 ≤ B → count (idealZeroLocus I) B ≤
          d * count (zeroLocus f)
            ((affineProjectionHeightConstant n : ℝ) * (d : ℝ) ^ (2 * n) * B) := by
  classical
  obtain ⟨x, hIker, hP⟩ := zero_dimensional_geometrically_integral_point (L := L) I hdim
  have hd : d = 1 := by
    have hh : (d : ℚ) = 1 := by simpa only [hP, Polynomial.leadingCoeff_one] using hdegree.symm
    exact_mod_cast hh
  subst d
  let b : Fin 1 → Fin n → ℤ := fun _ _ => 0
  let a : Fin 1 → MvPolynomial (Fin n) ℚ := fun i => integerLinearForm (b i)
  have ha : a = 0 := by
    funext i
    simp [a, b, integerLinearForm]
  have hsurj : Function.Surjective (projectionCoordinateMap I a) := by
    intro z
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
    refine ⟨C (eval x p), ?_⟩
    change Ideal.Quotient.mk I (aeval a (C (eval x p))) = Ideal.Quotient.mk I p
    rw [aeval_C, algebraMap_eq]
    apply Ideal.Quotient.eq.mpr
    rw [hIker]
    change eval x (C (eval x p) - p) = 0
    simp
  have hgen := reconstruction_generates_functionField
    (F := FractionRing (MvPolynomial (Fin n) ℚ ⧸ I)) I a 1 (fun i => C (x i))
    (by
      rw [map_one]
      intro h
      exact Ideal.IsPrime.ne_top ‹I.IsPrime› (Ideal.eq_top_of_isUnit_mem I h isUnit_one))
    (by
      intro i
      rw [hIker]
      change eval x (aeval a 1 * X i - aeval a (C (x i))) = 0
      simp)
  have hker : RingHom.ker (projectionCoordinateMap I a) = Ideal.span {X (0 : Fin 1)} := by
    have hvars : RingHom.ker (projectionCoordinateMap I a) = idealOfVars (Fin 1) ℚ := by
      ext p
      rw [mem_projectionCoordinateMap_ker, hIker, idealOfVars_eq_ker_constantCoeff]
      change eval x (aeval a p) = 0 ↔ constantCoeff p = 0
      rw [ha, aeval_zero]
      simp only [algebraMap_eq, eval_C]
    rw [hvars, idealOfVars]
    congr 1
    ext p
    simp only [Set.mem_range, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      congr 1
      exact Subsingleton.elim _ _
    · rintro rfl
      exact ⟨0, rfl⟩
  have hir : Irreducible (X (0 : Fin 1) : MvPolynomial (Fin 1) ℚ) := by
    apply irreducible_of_totalDegree_eq_one (totalDegree_X _)
    intro c hc
    apply isUnit_of_dvd_one
    simpa using hc (Finsupp.single 0 1)
  refine ⟨b, ?_, RingHom.isIntegral_of_surjective _ hsurj, hgen,
    X 0, hir, ?_, totalDegree_X _, hker, ?_⟩
  · intro i j
    simp only [b, abs_zero]
    exact Nat.cast_nonneg _
  · rw [map_X]
    apply irreducible_of_totalDegree_eq_one (totalDegree_X _)
    intro c hc
    apply isUnit_of_dvd_one
    simpa using hc (Finsupp.single 0 1)
  · intro B hB
    have hfiber (z : Fin 1 → ℚ) (s : Finset (Fin n → ℚ))
        (hzero : ∀ y ∈ s, ∀ g ∈ I, eval y g = 0)
        (_hproj : ∀ y ∈ s, ∀ i, eval y (a i) = z i) : s.card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro y hy w hw
      funext i
      have hmem : X i - C (x i) ∈ I := by
        rw [hIker]
        change eval x (X i - C (x i)) = 0
        simp
      have hy' := hzero y hy _ hmem
      have hw' := hzero w hw _ hmem
      simp only [map_sub, eval_X, eval_C, sub_eq_zero] at hy' hw'
      exact hy'.trans hw'.symm
    have hrel : aeval (R := ℚ) a (X 0) ∈ I := by simp [ha]
    have hh := affine_integer_linear_count_transfer I b (X 0) hrel 1 hfiber
      0 B le_rfl (fun _ _ => by simp [b])
    simp only [one_mul, mul_zero, zero_mul] at hh
    simp only [one_mul]
    exact hh.trans (count_mono (Set.Subset.refl _) (by positivity))

end
end CCDN
