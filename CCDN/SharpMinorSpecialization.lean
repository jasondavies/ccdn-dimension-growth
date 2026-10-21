module

public import CCDN.MinorCoordinateDegree
public import CCDN.ProjectiveZeroLocus
public import Mathlib.LinearAlgebra.Matrix.AbsoluteValue

/-! The sharp numerical specialization in CCDN Lemma 5.3. A
nonvanishing homogeneous condition on Plücker coordinates has a full-rank
integer witness with entries at most max(1, deg F), without a factor from
the number of rows. Every maximal minor has the stated factorial height
bound. The construction of the geometric bad-center polynomial is separate. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Matrix

theorem homogeneous_minor_nonvanishing_implies_independent
    {r n : ℕ} (F : MvPolynomial (Fin r ↪ Fin n) ℚ)
    (hhom : F.IsHomogeneous F.totalDegree) (hdeg : 0 < F.totalDegree)
    (A : Matrix (Fin r) (Fin n) ℚ)
    (hF : eval (fun c : Fin r ↪ Fin n => (A.submatrix id c).det) F ≠ 0) :
    LinearIndependent ℚ A.row := by
  classical
  by_contra hli
  have hz (c : Fin r ↪ Fin n) : (A.submatrix id c).det = 0 := by
    by_contra hd
    apply hli
    apply LinearIndependent.of_comp (LinearMap.funLeft ℚ ℚ c)
    exact Matrix.linearIndependent_rows_of_det_ne_zero hd
  apply hF
  have he : (fun c : Fin r ↪ Fin n => (A.submatrix id c).det) = fun _ => 0 := funext hz
  rw [he]
  change eval (0 : (Fin r ↪ Fin n) → ℚ) F = 0
  simpa only [zero_smul, zero_pow hdeg.ne', zero_mul] using
    homogeneous_eval_smul hhom (0 : ℚ) (fun _ => 0)

/-- Sharp bounded specialization of a homogeneous Plücker condition. A
constant condition is handled by a coordinate-row matrix. -/
theorem exists_sharp_integer_minor_specialization {r n : ℕ}
    (F : MvPolynomial (Fin r ↪ Fin n) ℚ)
    (hhom : F.IsHomogeneous F.totalDegree)
    (A : Matrix (Fin r) (Fin n) ℚ) (hli : LinearIndependent ℚ A.row)
    (hF : eval (fun c : Fin r ↪ Fin n => (A.submatrix id c).det) F ≠ 0) :
    ∃ M : Matrix (Fin r) (Fin n) ℤ,
      (∀ i j, 0 ≤ M i j ∧ M i j ≤ max 1 F.totalDegree) ∧
      LinearIndependent ℚ (M.map (Int.castRingHom ℚ)).row ∧
      eval (fun c : Fin r ↪ Fin n =>
        ((M.map (Int.castRingHom ℚ)).submatrix id c).det) F ≠ 0 ∧
      ∀ c : Fin r ↪ Fin n,
        |(M.submatrix id c).det| ≤ (r.factorial : ℤ) * ((max 1 F.totalDegree : ℕ) : ℤ) ^ r := by
  classical
  suffices ∃ M : Matrix (Fin r) (Fin n) ℤ,
      (∀ i j, 0 ≤ M i j ∧ M i j ≤ max 1 F.totalDegree) ∧
      LinearIndependent ℚ (M.map (Int.castRingHom ℚ)).row ∧
      eval (fun c : Fin r ↪ Fin n =>
        ((M.map (Int.castRingHom ℚ)).submatrix id c).det) F ≠ 0 by
    obtain ⟨M, hb, hi, hv⟩ := this
    refine ⟨M, hb, hi, hv, fun c => ?_⟩
    have hh := Matrix.det_le (abv := AbsoluteValue.abs) (A := M.submatrix id c)
      (fun i j => (abs_of_nonneg (hb i (c j)).1) ▸ (hb i (c j)).2)
    simpa only [AbsoluteValue.abs_apply, Fintype.card_fin, nsmul_eq_mul] using hh
  by_cases hdeg : F.totalDegree = 0
  · obtain ⟨c, hc, _⟩ := exists_nonzero_minor_of_independent_rows A hli
    let M : Matrix (Fin r) (Fin n) ℤ := fun i j => if c i = j then 1 else 0
    have hm : (M.map (Int.castRingHom ℚ)).submatrix id c = 1 := by
      ext i j
      change (((if c i = c j then 1 else 0) : ℤ) : ℚ) = if i = j then 1 else 0
      simp only [hc.eq_iff]
      split_ifs <;> simp
    refine ⟨M, ?_, ?_, ?_⟩
    · intro i j
      simp only [M, hdeg]
      split_ifs <;> norm_num
    · apply LinearIndependent.of_comp (LinearMap.funLeft ℚ ℚ c)
      have hd : ((M.map (Int.castRingHom ℚ)).submatrix id c).det ≠ 0 := by
        rw [hm, Matrix.det_one]
        exact one_ne_zero
      exact Matrix.linearIndependent_rows_of_det_ne_zero hd
    · have hconst := totalDegree_eq_zero_iff_eq_C.mp hdeg
      rw [hconst] at hF ⊢
      simpa only [eval_C] using hF
  · let U := aeval universalMaximalMinor F
    have hU : U ≠ 0 := by
      intro hz
      apply hF
      rw [← eval_minor_substitution]
      change eval (fun p => A p.1 p.2) U = 0
      rw [hz, map_zero]
    obtain ⟨v, hv, hvalue⟩ := exists_integer_grid_eval_ne_zero_of_degreeOf U hU
      F.totalDegree (minor_substitution_degreeOf_le F)
    let M : Matrix (Fin r) (Fin n) ℤ := fun i j => v (i, j)
    have hvalue' : eval (fun c : Fin r ↪ Fin n =>
        ((M.map (Int.castRingHom ℚ)).submatrix id c).det) F ≠ 0 := by
      rwa [← eval_minor_substitution]
    refine ⟨M, ?_, homogeneous_minor_nonvanishing_implies_independent F hhom
      (Nat.pos_of_ne_zero hdeg) _ hvalue', hvalue'⟩
    intro i j
    exact ⟨(hv (i, j)).1, (hv (i, j)).2.trans
      (by exact_mod_cast le_max_right (1 : ℕ) F.totalDegree)⟩

end
end CCDN
