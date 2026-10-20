module

public import AffineCurveCounting.BoundedLinearProjection
public import Mathlib.LinearAlgebra.Projection

/-! A genuine rational projection from bounded independent center rows.
The integral scalar-idempotent matrix already constructed by cofactors is
normalized to an idempotent linear map. Its image is a complementary space,
with the exact expected dimension and canonical projection property. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open Matrix LinearMap

/-- Normalize an integral scalar-idempotent matrix over the rationals. -/
def normalizedIntegerProjection {n : ℕ}
    (D : ℤ) (P : Matrix (Fin n) (Fin n) ℤ) :
    (Fin n → ℚ) →ₗ[ℚ] (Fin n → ℚ) :=
  (D : ℚ)⁻¹ • (P.map (Int.castRingHom ℚ)).mulVecLin

lemma normalizedIntegerProjection_apply {n : ℕ}
    (D : ℤ) (P : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℚ) :
    normalizedIntegerProjection D P x = (D : ℚ)⁻¹ • ((P.map (Int.castRingHom ℚ)) *ᵥ x) := rfl

lemma normalizedIntegerProjection_idempotent {n : ℕ}
    (D : ℤ) (hD : D ≠ 0) (P : Matrix (Fin n) (Fin n) ℤ)
    (hP : P * P = D • P) :
    IsIdempotentElem (normalizedIntegerProjection D P) := by
  have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast hD
  have hPq : P.map (Int.castRingHom ℚ) * P.map (Int.castRingHom ℚ) =
      (D : ℚ) • P.map (Int.castRingHom ℚ) := by
    ext i j
    have he := congrArg (Int.castRingHom ℚ) (congrArg (fun M => M i j) hP)
    simpa only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, map_sum, map_mul,
      Matrix.map_apply, Int.coe_castRingHom] using he
  change (normalizedIntegerProjection D P) * (normalizedIntegerProjection D P) = _
  apply LinearMap.ext
  intro x
  funext j
  change ((D : ℚ)⁻¹ • ((P.map (Int.castRingHom ℚ)) *ᵥ
    ((D : ℚ)⁻¹ • ((P.map (Int.castRingHom ℚ)) *ᵥ x)))) j = _
  rw [Matrix.mulVec_smul, smul_smul, Matrix.mulVec_mulVec, hPq, Matrix.smul_mulVec,
    smul_smul]
  rw [show (D : ℚ)⁻¹ * (D : ℚ)⁻¹ * D = (D : ℚ)⁻¹ by field_simp]
  rfl

lemma normalizedIntegerProjection_eq_zero_iff {n : ℕ}
    (D : ℤ) (hD : D ≠ 0) (P : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℚ) :
    normalizedIntegerProjection D P x = 0 ↔ (P.map (Int.castRingHom ℚ)) *ᵥ x = 0 := by
  rw [normalizedIntegerProjection_apply, smul_eq_zero]
  have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast hD
  exact or_iff_right (inv_ne_zero hDq)

lemma normalizedIntegerProjection_sub_mem_ker {n : ℕ}
    (D : ℤ) (hD : D ≠ 0) (P : Matrix (Fin n) (Fin n) ℤ)
    (hP : P * P = D • P) (x : Fin n → ℚ) :
    x - normalizedIntegerProjection D P x ∈ (normalizedIntegerProjection D P).ker := by
  have hi := normalizedIntegerProjection_idempotent D hD P hP
  rw [LinearMap.mem_ker, map_sub]
  have he := congrArg (fun f : Module.End ℚ (Fin n → ℚ) => f x) hi
  exact sub_eq_zero.mpr he.symm

/-- The normalization is exactly projection onto its image along the center,
not merely a linear map with the same kernel. -/
theorem exists_bounded_rational_center_projection {s n : ℕ}
    (A : Matrix (Fin (s + 1)) (Fin (n + 1)) ℤ)
    (hli : LinearIndependent ℚ (fun i => fun j => (A i j : ℚ)))
    (T : ℕ) (hA : ∀ i j, |A i j| ≤ (T : ℤ)) :
    ∃ D : ℤ, D ≠ 0 ∧ ∃ P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ,
      (∀ i j, |P i j| ≤ 2 * ((s + 1).factorial : ℤ) * (T : ℤ) ^ (s + 1)) ∧
      P * P = D • P ∧
      IsIdempotentElem (normalizedIntegerProjection D P) ∧
      (normalizedIntegerProjection D P).ker =
        Submodule.span ℚ (Set.range (fun i => fun j => (A i j : ℚ))) ∧
      IsCompl (Submodule.span ℚ (Set.range (fun i => fun j => (A i j : ℚ))))
        (normalizedIntegerProjection D P).range ∧
      Module.finrank ℚ (normalizedIntegerProjection D P).range + (s + 1) = n + 1 ∧
      (∀ x : Fin (n + 1) → ℚ,
        x - normalizedIntegerProjection D P x ∈
          Submodule.span ℚ (Set.range (fun i => fun j => (A i j : ℚ)))) ∧
      ∀ x : Fin (n + 1) → ℚ, ∀ y : (normalizedIntegerProjection D P).range,
        x - y.val ∈ Submodule.span ℚ (Set.range (fun i => fun j => (A i j : ℚ))) →
          normalizedIntegerProjection D P x = y.val := by
  obtain ⟨D, hD, P, hb, hPP, hk⟩ := exists_bounded_integer_scaled_projection A hli T hA
  have hid := normalizedIntegerProjection_idempotent D hD P hPP
  have hker : (normalizedIntegerProjection D P).ker =
      Submodule.span ℚ (Set.range (fun i => fun j => (A i j : ℚ))) := by
    ext x
    exact (normalizedIntegerProjection_eq_zero_iff D hD P x).trans (hk x)
  have hcompl := hid.isCompl.symm
  rw [hker] at hcompl
  have hdim := (normalizedIntegerProjection D P).finrank_range_add_finrank_ker
  rw [hker, finrank_span_eq_card hli, Fintype.card_fin, Module.finrank_fin_fun] at hdim
  refine ⟨D, hD, P, hb, hPP, hid, hker, hcompl, hdim, ?_, ?_⟩
  · intro x
    rw [← hker]
    exact normalizedIntegerProjection_sub_mem_ker D hD P hPP x
  · intro x y hxy
    rw [← hker, LinearMap.mem_ker, map_sub] at hxy
    have hy := hid.mem_range_iff.mp y.property
    rw [hy] at hxy
    exact sub_eq_zero.mp hxy

end
end AffineCurveCounting
