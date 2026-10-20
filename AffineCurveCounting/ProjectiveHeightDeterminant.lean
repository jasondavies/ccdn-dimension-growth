module

public import AffineCurveCounting.ProjectivePrimeDeterminant
public import AffineCurveCounting.HeightDeterminant

/-! Coefficient-controlled bad primes for homogeneous projective evaluation
matrices. Good reduction of a full-degree affine chart implies good reduction
of the entire projective equation. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial Finset

theorem homogeneous_irreducible_reduction_of_not_planeBadReduction
    {d p : ℕ} [Fact p.Prime] (f : MvPolynomial (Fin 3) ℤ)
    (hf : f.IsHomogeneous d) (hdeg : (affineChart 2 f).totalDegree = d)
    (hgood : ¬PlaneBadReduction (affineChart 2 f) p) :
    Irreducible (map (Int.castRingHom (ZMod p)) f) := by
  let K := AlgebraicClosure (ZMod p)
  obtain ⟨hdegree, hir⟩ := (not_planeBadReduction_iff (affineChart 2 f) p).mp hgood
  have hc : affineChart 2 (map (Int.castRingHom K) f) =
      map (Int.castRingHom K) (affineChart 2 f) := affineChart_map _ f
  have hf0 : map (Int.castRingHom K) f ≠ 0 := by
    intro h
    apply hir.ne_zero
    rw [← hc, h, map_zero]
  have hhom := hf.map (Int.castRingHom K)
  have hi : Irreducible (map (Int.castRingHom K) f) := by
    apply irreducible_of_affineChart_irreducible
    · rw [hc, hdegree, hdeg, hhom.totalDegree hf0]
    · rw [hc]
      exact hir
  apply mvPolynomial_irreducible_of_field_map (algebraMap (ZMod p) K)
  have he : (algebraMap (ZMod p) K).comp (Int.castRingHom (ZMod p)) =
      Int.castRingHom K := by ext; simp
  simpa only [MvPolynomial.map_map, he] using hi

/-- The global projective determinant lower bound with every local counting
and bad-prime charge estimate discharged. -/
theorem projective_determinant_log_lower_height
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {s N d M : ℕ} (hs : 0 < s)
    (f : MvPolynomial (Fin 3) ℤ) (hf : f.IsHomogeneous d) (hd : 2 ≤ d)
    (hdeg : (affineChart 2 f).totalDegree = d)
    (hir : Irreducible (map (Int.castRingHom K) (affineChart 2 f)))
    (H : ℝ) (hH : 1 ≤ H) (hcoeff : ∀ m, |((affineChart 2 f).coeff m : ℝ)| ≤ H)
    (F : Fin N → MvPolynomial (Fin 3) ℤ) (hF : ∀ j, (F j).IsHomogeneous M)
    (z : Fin s → IntPoint 3) (hprim : ∀ i, univ.gcd (z i) = 1)
    (hz : ∀ i, eval (z i) f = 0)
    (hrows : LinearIndependent ℚ
      ((Matrix.of fun i j => eval (z i) (F j)).map ((↑) : ℤ → ℚ)).row) :
    (s : ℝ) ^ 2 / 2 * (Real.log s - 4 * Real.log d -
      Real.log (1 + Real.log H / (d : ℝ) ^ 2) - heightDeterminantError 164) ≤
        Real.log (Int.Matrix.minorGcd (Matrix.of fun i j => eval (z i) (F j))) := by
  obtain ⟨bad, hmem, hcharge⟩ := exists_plane_bad_prime_set (affineChart 2 f)
    (by omega) hir H hH hcoeff
  rw [hdeg] at hmem hcharge
  have hred (p : ℕ) (hp : p ∈ ((Ioc 0 s).filter Nat.Prime) \ bad)
      (hlo : 27 * (d : ℝ) ^ 4 < p) :
      Irreducible (map (Int.castRingHom (ZMod p)) f) := by
    let : Fact p.Prime := ⟨(mem_filter.mp (mem_sdiff.mp hp).1).2⟩
    apply homogeneous_irreducible_reduction_of_not_planeBadReduction f hf hdeg
    intro hbad
    exact (mem_sdiff.mp hp).2 ((hmem p).mpr ⟨hlo, hbad⟩)
  have hlower := projective_determinant_log_lower_at_rank hs f hf hd F hF z hprim hz hrows
    bad hred
  have hh := mul_le_mul_of_nonneg_left hcharge (show 0 ≤ (s : ℝ) ^ 2 / 2 by positivity)
  dsimp only [heightDeterminantError]
  nlinarith

end
end AffineCurveCounting
