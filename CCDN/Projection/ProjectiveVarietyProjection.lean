module

public import CCDN.Projection.BoundedDegreeNormalizationFiber
public import CCDN.Height.ProjectiveLinearCountTransfer
public import CCDN.Projection.BoundedBirationalHypersurfaceProjection
public import CCDN.Algebra.PolynomialPredicates
/-! The exact degree factor in the projective projection count.
A finite birational integer projection preserves the Hilbert degree,
and every fiber is bounded by d through its integral linear normalization. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- A constructed finite birational hypersurface projection has exactly the
degree factor d in its point-count comparison, with a polynomial height cost
depending only on ambient dimension. -/
theorem exists_projective_variety_projection
    (m n : ℕ) (hmn : m ≤ n)
    (I : Ideal (MvPolynomial (Fin (n + 1)) ℚ)) [I.IsPrime]
    (hI : IsHomogeneousIdeal I)
    (d : ℕ) (hd : 1 ≤ d)
    (hdimdeg : HasProjectiveDimensionDegree I m d) :
    ∃ b : Fin (m + 2) → Fin (n + 1) → ℤ,
      (projectionCoordinateMap I (fun i => integerLinearForm (b i))).IsIntegral ∧
      IntermediateField.adjoin ℚ
        (Set.range (fun i => algebraMap (MvPolynomial (Fin (n + 1)) ℚ ⧸ I)
          (FractionRing (MvPolynomial (Fin (n + 1)) ℚ ⧸ I))
          ((Ideal.Quotient.mk I) (integerLinearForm (b i))))) = ⊤ ∧
      ∃ f : MvPolynomial (Fin (m + 2)) ℚ,
        Irreducible f ∧ f.IsHomogeneous d ∧ f.totalDegree = d ∧
        RingHom.ker (projectionCoordinateMap I (fun i => integerLinearForm (b i))) =
          Ideal.span {f} ∧
        ∀ B : ℝ, projectiveCount (projectiveIdealZeroLocus I) B ≤
          d * projectiveCount (projectiveZeroLocus f)
            (((n + 1 : ℕ) * birationalProjectionHeightConstant (n + 1) : ℕ) *
              (d : ℝ) ^ (2 * (n + 1)) * B) := by
  obtain ⟨b, hb, hnorm, hinj, hint, hfield, f, hf, hfhom, hfdeg, hker⟩ :=
    exists_bounded_birational_hypersurface_projection_of_le m (n + 1)
      (by omega) I hI d hdimdeg
  refine ⟨b, hint, hfield, f, hf, hfhom, hfdeg, hker, ?_⟩
  have hrel : aeval (fun i => integerLinearForm (b i)) f ∈ I := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change f ∈ RingHom.ker (projectionCoordinateMap I (fun i => integerLinearForm (b i)))
    rw [hker]
    exact Ideal.subset_span (Set.mem_singleton f)
  have hfiber (z : Fin (m + 2) → ℚ) (s : Finset (Fin (n + 1) → ℚ))
      (hzero : ∀ x ∈ s, ∀ g ∈ I, eval x g = 0)
      (hproj : ∀ x ∈ s, ∀ i, eval x (integerLinearForm (b i)) = z i) :
      s.card ≤ d := by
    have hh := bounded_degree_normalization_fiber_card_le I 1 (by omega)
      (fun i : Fin (m + 1) => integerLinearForm (b i.succ))
      (fun i => integerLinearForm_degree (b i.succ)) hinj hnorm d hdimdeg
      (fun i => z i.succ) s hzero (fun x hx i => hproj x hx i.succ)
    simpa only [one_pow, Nat.mul_one] using hh
  let H : ℝ := birationalProjectionHeightConstant (n + 1) * (d : ℝ) ^ (2 * (n + 1))
  have hH : 0 ≤ H := by positivity
  have hbH (i j) : |(b i j : ℝ)| ≤ H := by
    have hh : |(b i j : ℝ)| ≤ integerBirationalProjectionHeight (n + 1) d := by
      exact_mod_cast hb i j
    apply hh.trans
    dsimp only [H]
    exact_mod_cast integerBirationalProjectionHeight_le (n + 1) d hd
  intro B
  have hh := projective_integer_linear_count_transfer
    I b f (by rwa [hfdeg]) hrel d hfiber H B hH hbH
  convert hh using 1
  simp only [H, Nat.cast_mul, mul_assoc]

end
end CCDN
