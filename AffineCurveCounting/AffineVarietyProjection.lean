module

public import AffineCurveCounting.ZeroDimensionalAffineProjection

/-! CCDN Proposition 4.3.1 in every affine dimension. The projection and
its geometrically integral hypersurface image are constructed, including
the zero-dimensional case. The explicit box exponent is 2n. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

/-- The full affine projection theorem, retaining the actual finite
birational integer coordinate map and the exact image equation. -/
theorem exists_geometrically_integral_affine_projection
    {L : Type*} [Field L] [Algebra ℚ L] [IsAlgClosed L] [IsGalois ℚ L]
    (m n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℚ)) [I.IsPrime]
    [(I.map (map (algebraMap ℚ L))).IsPrime]
    (d : ℕ) (hdim : (filteredHilbertPolynomial I).natDegree = m)
    (hdegree : (filteredHilbertPolynomial I).leadingCoeff = (d : ℚ) / m.factorial) :
    ∃ b : Fin (m + 1) → Fin n → ℤ,
      (∀ i j, |b i j| ≤ integerBirationalProjectionHeight n d) ∧
      (projectionCoordinateMap I (fun i => integerLinearForm (b i))).IsIntegral ∧
      IntermediateField.adjoin ℚ
        (Set.range (fun i => algebraMap (MvPolynomial (Fin n) ℚ ⧸ I)
          (FractionRing (MvPolynomial (Fin n) ℚ ⧸ I))
          ((Ideal.Quotient.mk I) (integerLinearForm (b i))))) = ⊤ ∧
      ∃ f : MvPolynomial (Fin (m + 1)) ℚ,
        Irreducible f ∧ Irreducible (map (algebraMap ℚ L) f) ∧ f.totalDegree = d ∧
        RingHom.ker (projectionCoordinateMap I (fun i => integerLinearForm (b i))) =
          Ideal.span {f} ∧
        ∀ B : ℝ, 1 ≤ B → count (idealZeroLocus I) B ≤
          d * count (zeroLocus f)
            ((affineProjectionHeightConstant n : ℝ) * (d : ℝ) ^ (2 * n) * B) := by
  cases m with
  | zero =>
      exact exists_geometric_affine_projection_zero_dimension n I d hdim
        (by simpa only [Nat.factorial_zero, Nat.cast_one, div_one] using hdegree)
  | succ m =>
      have hpos := filteredHilbertPolynomial_leadingCoeff_pos I
        (Ideal.IsPrime.ne_top ‹I.IsPrime›)
      rw [hdegree] at hpos
      have hdQ : (0 : ℚ) < d := by
        simpa only [zero_mul] using
          (lt_div_iff₀ (by positivity : (0 : ℚ) < (m + 1).factorial)).mp hpos
      have hd : 1 ≤ d := by exact_mod_cast hdQ
      exact exists_geometric_affine_projection_positive_dimension m n I d hd hdim hdegree

/-- The dimension-only constants are chosen before the ideal, the degree,
and the radius. The stronger preceding theorem also records the finite
birational integer projection producing this same image. -/
theorem affine_variety_projection_constants (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ e : ℕ,
      ∀ (m : ℕ) (I : Ideal (MvPolynomial (Fin n) ℚ)), I.IsPrime →
      (I.map (map (algebraMap ℚ (AlgebraicClosure ℚ)))).IsPrime →
      ∀ d : ℕ, (filteredHilbertPolynomial I).natDegree = m →
      (filteredHilbertPolynomial I).leadingCoeff = (d : ℚ) / m.factorial →
      ∃ (b : Fin (m + 1) → Fin n → ℤ) (f : MvPolynomial (Fin (m + 1)) ℚ),
        (projectionCoordinateMap I (fun i => integerLinearForm (b i))).IsIntegral ∧
        Irreducible f ∧ Irreducible (map (algebraMap ℚ (AlgebraicClosure ℚ)) f) ∧
        f.totalDegree = d ∧
        RingHom.ker (projectionCoordinateMap I (fun i => integerLinearForm (b i))) =
          Ideal.span {f} ∧
        ∀ B : ℝ, 1 ≤ B → count (idealZeroLocus I) B ≤
          d * count (zeroLocus f) (C * (d : ℝ) ^ e * B) := by
  refine ⟨affineProjectionHeightConstant n,
    by exact_mod_cast affineProjectionHeightConstant_pos n, 2 * n, ?_⟩
  intro m I hI hgeom d hdim hdegree
  let : I.IsPrime := hI
  let : (I.map (map (algebraMap ℚ (AlgebraicClosure ℚ)))).IsPrime := hgeom
  obtain ⟨b, _, hint, _, f, hf, hfgeom, hfdegree, hker, hcount⟩ :=
    exists_geometrically_integral_affine_projection (L := AlgebraicClosure ℚ)
      m n I d hdim hdegree
  exact ⟨b, f, hint, hf, hfgeom, hfdegree, hker, hcount⟩

end
end AffineCurveCounting
