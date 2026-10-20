module

public import CCDN.TopFormAuxiliary
public import CCDN.CompleteIntersectionDegreeBudget

/-! The uniform surface auxiliary gives an actual finite curve cover of
all bounded integer zeros, with total curve degree O(d^(9/2) B^(1/sqrt d)). -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- An absolutely irreducible top form supplies the auxiliary equation, the
actual rational curve components, and their total degree bound. The component
cover is exact on the auxiliary section and covers every original integer
zero in the specified box. -/
theorem top_form_surface_curve_components
    (f : MvPolynomial (Fin 3) ℤ)
    (hir : Irreducible (map (Int.castRingHom (AlgebraicClosure ℚ))
      (homogeneousComponent f.totalDegree f)))
    {B : ℝ} (hB : 1 ≤ B) :
    ∃ g : MvPolynomial (Fin 3) ℤ, g ≠ 0 ∧
      ¬ map (Int.castRingHom ℚ) f ∣ map (Int.castRingHom ℚ) g ∧
      (g.totalDegree : ℝ) ≤ topFormAuxiliaryConstant 1 *
        (f.totalDegree : ℝ) ^ (7 / 2 : ℝ) *
          B ^ (1 / (f.totalDegree : ℝ) ^ (1 / 2 : ℝ)) ∧
      (∀ x : IntPoint 3, (∀ j, |(x j : ℝ)| ≤ B) → eval x f = 0 → eval x g = 0) ∧
      ∃ S : Finset (Ideal (CoordinatePolynomial 3)),
        ∃ d : Ideal (CoordinatePolynomial 3) → ℕ,
          (∀ P ∈ S, P.IsPrime ∧ P.height = 2 ∧
            map (Int.castRingHom ℚ) f ∈ P ∧ map (Int.castRingHom ℚ) g ∈ P ∧
            0 < d P ∧ HasAffineCurveDegree P (d P)) ∧
          zeroLocus (map (Int.castRingHom ℚ) f) ∩ zeroLocus (map (Int.castRingHom ℚ) g) =
            ⋃ P ∈ S, idealZeroLocus P ∧
          ((∑ P ∈ S, d P : ℕ) : ℝ) ≤ topFormAuxiliaryConstant 1 *
            (f.totalDegree : ℝ) ^ (9 / 2 : ℝ) *
              B ^ (1 / (f.totalDegree : ℝ) ^ (1 / 2 : ℝ)) ∧
          (∀ P ∈ S, (polynomialSectionIdeal (map (Int.castRingHom ℚ) f)
            (map (Int.castRingHom ℚ) g)).IsMinimalPrime P) ∧
          ∀ x : IntPoint 3, (∀ j, |(x j : ℝ)| ≤ B) → eval x f = 0 →
            ∃ P ∈ S, rationalPoint x ∈ idealZeroLocus P := by
  classical
  have habs := absolute_irreducible_of_top_homogeneousComponent_irreducible f hir
  have hfQ : Irreducible (map (Int.castRingHom ℚ) f) :=
    rational_irreducible_of_charZero_map f habs
  have hd : 0 < f.totalDegree := absolute_integer_polynomial_totalDegree_pos f habs
  have hdR : (0 : ℝ) < f.totalDegree := by exact_mod_cast hd
  obtain ⟨g, hg0, hgnd, hgdeg, hgz⟩ := top_form_auxiliary_rational (n := 1) f hir hB
  have hgdegree : (g.totalDegree : ℝ) ≤ topFormAuxiliaryConstant 1 *
      (f.totalDegree : ℝ) ^ (7 / 2 : ℝ) *
        B ^ (1 / (f.totalDegree : ℝ) ^ (1 / 2 : ℝ)) := by
    norm_num at hgdeg ⊢
    exact hgdeg
  obtain ⟨S, d, hcomponents, hcover, hbudget, hminimal⟩ :=
    exists_completeIntersection_curve_components (map (Int.castRingHom ℚ) f)
      (map (Int.castRingHom ℚ) g) hfQ hgnd
  have hmapdegree (p : MvPolynomial (Fin 3) ℤ) :
      (map (Int.castRingHom ℚ) p).totalDegree = p.totalDegree := by
    unfold totalDegree
    rw [support_map_of_injective _ Int.cast_injective]
  have hpower : (f.totalDegree : ℝ) * (f.totalDegree : ℝ) ^ (7 / 2 : ℝ) =
      (f.totalDegree : ℝ) ^ (9 / 2 : ℝ) := by
    calc
      _ = (f.totalDegree : ℝ) ^ (1 : ℝ) * (f.totalDegree : ℝ) ^ (7 / 2 : ℝ) := by
        rw [Real.rpow_one]
      _ = (f.totalDegree : ℝ) ^ ((1 : ℝ) + 7 / 2) := (Real.rpow_add hdR _ _).symm
      _ = _ := by norm_num
  refine ⟨g, hg0, hgnd, hgdegree, hgz, S, d, hcomponents, hcover, ?_, hminimal, ?_⟩
  · have hbudgetR : ((∑ P ∈ S, d P : ℕ) : ℝ) ≤
        (f.totalDegree : ℝ) * g.totalDegree := by
      rw [hmapdegree f, hmapdegree g] at hbudget
      exact_mod_cast hbudget
    calc
      _ ≤ (f.totalDegree : ℝ) * g.totalDegree := hbudgetR
      _ ≤ (f.totalDegree : ℝ) * (topFormAuxiliaryConstant 1 *
          (f.totalDegree : ℝ) ^ (7 / 2 : ℝ) *
            B ^ (1 / (f.totalDegree : ℝ) ^ (1 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left hgdegree hdR.le
      _ = topFormAuxiliaryConstant 1 *
          ((f.totalDegree : ℝ) * (f.totalDegree : ℝ) ^ (7 / 2 : ℝ)) *
            B ^ (1 / (f.totalDegree : ℝ) ^ (1 / 2 : ℝ)) := by ring
      _ = _ := by rw [hpower]
  · intro x hx hxf
    have hmapzero (p : MvPolynomial (Fin 3) ℤ) (hp : eval x p = 0) :
        eval (rationalPoint x) (map (Int.castRingHom ℚ) p) = 0 := by
      have hh := congrArg (Int.castRingHom ℚ) hp
      rw [map_eval, map_zero] at hh
      exact hh
    have hxsection : rationalPoint x ∈
        zeroLocus (map (Int.castRingHom ℚ) f) ∩ zeroLocus (map (Int.castRingHom ℚ) g) :=
      ⟨hmapzero f hxf, hmapzero g (hgz x hx hxf)⟩
    rw [hcover] at hxsection
    obtain ⟨P, hxP⟩ := Set.mem_iUnion.mp hxsection
    obtain ⟨hPS, hxP⟩ := Set.mem_iUnion.mp hxP
    exact ⟨P, hPS, hxP⟩

end
end CCDN
