module

public import AffineCurveCounting.HypersurfaceAbsoluteAuxiliary

/-! A single auxiliary polynomial for all rational points of bounded projective
height, with no finite-family hypothesis. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

/-- The full projective-height formulation of the absolutely irreducible
case of CCDN Theorem 3.1.1. -/
theorem hypersurface_absolute_projective_auxiliary
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] {n d : ℕ}
    (f : MvPolynomial (Fin (n + 3)) ℤ) (hf : f.IsHomogeneous d) (hd : 0 < d)
    (hir : Irreducible (map (Int.castRingHom K) f))
    {B : ℝ} (hB : 1 ≤ B) :
    ∃ (bad : Finset ℕ) (M : ℕ),
      (∀ p, p ∈ bad ↔ 27 * d ^ 4 < p ∧ HypersurfaceBadReduction f p) ∧
      (M : ℝ) ≤ hypersurfaceAbsoluteAuxiliaryConstant n *
        ((d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) * Real.exp (∑ p ∈ bad, Real.log p / p) *
            B ^ ((n + 2 : ℝ) / ((n + 1 : ℝ) * (d : ℝ) ^ (1 / (n + 1 : ℝ)))) /
              (integerCoefficientHeight f : ℝ) ^ (1 / ((n + 1 : ℝ) * d * (d : ℝ) ^ (1 / (n + 1 : ℝ)))) +
          (d : ℝ) ^ (1 - 1 / (n + 1 : ℝ)) * Real.log B + (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ))) ∧
      ∃ g : MvPolynomial (Fin (n + 3)) ℤ, g ≠ 0 ∧ g.IsHomogeneous M ∧
        (∀ x : ProjectivePoint (n + 2), x.mulHeight ≤ B →
          x ∈ projectiveZeroLocus (map (Int.castRingHom ℚ) f) →
          x ∈ projectiveZeroLocus (map (Int.castRingHom ℚ) g)) ∧ ¬ f ∣ g := by
  classical
  let S := projectivePoints (projectiveZeroLocus (map (Int.castRingHom ℚ) f)) B
  let e := (Fintype.equivFin S).symm
  let z : Fin (Fintype.card S) → IntPoint (n + 3) := fun i => primitiveProjectiveRep (e i).val
  have hprim (i) : Finset.univ.gcd (z i) = 1 := primitiveProjectiveRep_gcd _
  have hzero (i) : eval (z i) f = 0 :=
    (mem_integer_projectiveZeroLocus hf _).mp (mem_projectivePoints.mp (e i).property).2
  have hbox (i j) : |(z i j : ℝ)| ≤ B :=
    (primitiveProjectiveRep_bound _ j).trans (mem_projectivePoints.mp (e i).property).1
  obtain ⟨bad, M, hbad, hdegree, g, hg0, hgh, hgz, hgnd⟩ :=
    hypersurface_absolute_auxiliary_degree f hf hd hir z hprim hzero hB hbox
  refine ⟨bad, M, hbad, hdegree, g, hg0, hgh, ?_, hgnd⟩
  intro x hxB hxf
  let xS : S := ⟨x, mem_projectivePoints.mpr ⟨hxB, hxf⟩⟩
  obtain ⟨i, hi⟩ := e.surjective xS
  have hh := hgz i
  dsimp only [z] at hh
  rw [hi] at hh
  exact (mem_integer_projectiveZeroLocus hgh x).mpr hh

end
end AffineCurveCounting
