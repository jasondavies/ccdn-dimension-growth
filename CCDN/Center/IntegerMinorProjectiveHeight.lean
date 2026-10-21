/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Height.ProjectiveIntegerHeight
public import CCDN.Center.MinorSpecialization
/-! Integral maximal minors give the intrinsic projective height of a
center. The minor vector need not be primitive, and the height does not
depend on the coordinate ordering. -/

@[expose] public section
namespace CCDN
noncomputable section
open Matrix

theorem integer_tuple_height_le {ι : Type*} [Fintype ι]
    (z : ι → ℤ) (hz : z ≠ 0) {B : ℝ} (hB : ∀ i, |(z i : ℝ)| ≤ B) :
    Height.mulHeight (fun i => (z i : ℚ)) ≤ B := by
  classical
  obtain ⟨i,hi⟩ := Function.ne_iff.mp hz
  have hcard : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨i⟩
  let e : Fin (Fintype.card ι - 1 + 1) ≃ ι :=
    (finCongr (by omega)).trans (Fintype.equivFin ι).symm
  have hz' : (fun j => z (e j)) ≠ 0 := by
    intro hh
    apply hz
    funext k
    simpa using congrFun hh (e.symm k)
  have hh := projective_integer_height_le (n := Fintype.card ι - 1)
    (fun j => z (e j)) hz' (fun j => hB (e j))
  rw [Projectivization.mulHeight_mk] at hh
  change Height.mulHeight ((fun k => (z k : ℚ)) ∘ e) ≤ B at hh
  rwa [Height.mulHeight_comp_equiv] at hh

lemma integer_maximal_minors_ne_zero {r n : ℕ}
    (A : Matrix (Fin r) (Fin n) ℤ)
    (hA : LinearIndependent ℚ (A.map (Int.castRingHom ℚ)).row) :
    (fun c : Fin r ↪ Fin n => ((A.submatrix id c).det : ℚ)) ≠ 0 := by
  obtain ⟨c,hc,hd⟩ := Matrix.exists_det_submatrix_ne_zero_of_linearIndependent_row
    (A.map (Int.castRingHom ℚ)) hA
  intro hz
  have hh := congrFun hz ⟨c,hc⟩
  apply hd
  change (Int.castRingHom ℚ) (A.submatrix id c).det = 0 at hh
  rw [RingHom.map_det] at hh
  exact hh

theorem integer_maximal_minor_projective_height {r n T : ℕ}
    (A : Matrix (Fin r) (Fin n) ℤ)
    (hA : LinearIndependent ℚ (A.map (Int.castRingHom ℚ)).row)
    (hbound : ∀ i j, |A i j| ≤ (T : ℤ)) :
    (Projectivization.mk ℚ (fun c : Fin r ↪ Fin n => ((A.submatrix id c).det : ℚ))
      (integer_maximal_minors_ne_zero A hA)).mulHeight ≤ (r.factorial * T ^ r : ℕ) := by
  rw [Projectivization.mulHeight_mk]
  apply integer_tuple_height_le (fun c : Fin r ↪ Fin n => (A.submatrix id c).det)
  · intro hz
    apply integer_maximal_minors_ne_zero A hA
    funext c
    rw [show (A.submatrix id c).det = 0 from congrFun hz c]
    simp
  · intro c
    have hh := Matrix.det_le (abv := AbsoluteValue.abs) (A := A.submatrix id c)
      (fun i j => hbound i (c j))
    have hi : |(A.submatrix id c).det| ≤ (r.factorial * T ^ r : ℕ) := by
      simpa only [AbsoluteValue.abs_apply,Fintype.card_fin,nsmul_eq_mul,
        Nat.cast_mul,Nat.cast_pow] using hh
    exact_mod_cast hi

end
end CCDN
