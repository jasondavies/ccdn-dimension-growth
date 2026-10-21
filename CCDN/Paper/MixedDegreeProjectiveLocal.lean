/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.HomogeneousChart
public import CCDN.Determinant.HypersurfaceLocalDeterminant
public import CCDN.Determinant.PlaneMultiplicity
import CCDN.Determinant.HypersurfaceResidue
import CCDN.Determinant.ProjectiveHypersurfaceLocal
import CCDN.Determinant.ProjectiveLocalDeterminant
import CCDN.ForMathlib.Matrix
/-! Local determinant divisibility for homogeneous columns of arbitrary
degrees, with the normalization required by affine-chart evaluation.

Each entry is multiplied by the inverse pivot coordinate to that column's
degree. For equal degrees these factors form one unit per row, as in
`projective_hypersurface_chart_det_divisibility`. For unequal degrees this
normalization is part of the assertion, not a removable row factor. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The local divisor for varying-degree columns, evaluated in one
projective chart modulo the required prime power. -/
theorem mixed_degree_projective_chart_det_divisibility {p n μ s d : ℕ} [Fact p.Prime]
    (f : MvPolynomial (Fin (n + 3)) ℤ) (hfhom : f.IsHomogeneous d)
    (F : Fin s → MvPolynomial (Fin (n + 3)) ℤ) (deg : Fin s → ℕ)
    (hF : ∀ j, (F j).IsHomogeneous (deg j))
    (z : Fin s → Fin (n + 3) → ℤ) (a : Fin (n + 2) → ℤ)
    (hf : map (Int.castRingHom (ZMod p)) (originShift a (affineChart (n + 2) f)) ∈
      idealOfVars (Fin (n + 2)) (ZMod p) ^ μ)
    (hμ : homogeneousComponent μ
      (map (Int.castRingHom (ZMod p)) (originShift a (affineChart (n + 2) f))) ≠ 0)
    (hres : ∀ i j, (p : ℤ) ∣ z i j.succ - a j * z i 0)
    (hz : ∀ i, eval (z i) f = 0)
    (u : Fin s → ℤ)
    (hu : ∀ i, (p : ℤ) ^ hypersurfaceMultiplicityExponent (n + 1) μ s ∣
      u i * z i 0 - 1) :
    (p : ℤ) ^ hypersurfaceMultiplicityExponent (n + 1) μ s ∣
      (Matrix.of fun i j => u i ^ deg j * eval (z i) (F j)).det := by
  classical
  let N := hypersurfaceMultiplicityExponent (n + 1) μ s
  by_cases hN : N = 0
  · change (p : ℤ) ^ N ∣ _
    simp [hN]
  have hNpos : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN
  let q : ℤ := (p : ℤ) ^ N
  have hpq : (p : ℤ) ∣ q := by
    simpa only [pow_one] using pow_dvd_pow (p : ℤ) hNpos
  let x : Fin s → Fin (n + 2) → ℤ := fun i j => u i * z i j.succ
  have hx (i : Fin s) (j : Fin (n + 2)) : (p : ℤ) ∣ x i j - a j := by
    have he : x i j - a j =
        u i * (z i j.succ - a j * z i 0) + a j * (u i * z i 0 - 1) := by
      dsimp [x]
      ring
    rw [he]
    exact dvd_add (dvd_mul_of_dvd_right (hres i j) _)
      (dvd_mul_of_dvd_right (hpq.trans (hu i)) _)
  have hxf (i : Fin s) : q ∣ eval (x i) (affineChart (n + 2) f) := by
    have h := projective_hypersurface_chart_eval_congr (z i) (hu i) f hfhom
    simpa only [hz, mul_zero, sub_zero] using h
  let A := Matrix.of fun i j : Fin s => eval (x i) (affineChart (n + 2) (F j))
  let D := Matrix.of fun i j : Fin s => u i ^ deg j * eval (z i) (F j)
  have hA : q ∣ A.det :=
    hypersurface_residue_pow_dvd_det_mod (affineChart (n + 2) f) a hf hμ x hx hxf
      (fun j => affineChart (n + 2) (F j))
  have hAD : q ∣ A.det - D.det := by
    apply Matrix.dvd_det_sub_det_of_dvd_sub
    intro i j
    exact projective_hypersurface_chart_eval_congr (z i) (hu i) (F j) (hF j)
  simpa only [sub_sub_cancel] using dvd_sub hA hAD

/-- Inverse pivot coordinates exist because the chosen chart contains the
residue point. -/
theorem exists_mixed_degree_projective_chart_det_divisor
    {p n μ s d : ℕ} [Fact p.Prime]
    (f : MvPolynomial (Fin (n + 3)) ℤ) (hfhom : f.IsHomogeneous d)
    (F : Fin s → MvPolynomial (Fin (n + 3)) ℤ) (deg : Fin s → ℕ)
    (hF : ∀ j, (F j).IsHomogeneous (deg j))
    (z : Fin s → Fin (n + 3) → ℤ) (a : Fin (n + 2) → ℤ)
    (hf : map (Int.castRingHom (ZMod p)) (originShift a (affineChart (n + 2) f)) ∈
      idealOfVars (Fin (n + 2)) (ZMod p) ^ μ)
    (hμ : homogeneousComponent μ
      (map (Int.castRingHom (ZMod p)) (originShift a (affineChart (n + 2) f))) ≠ 0)
    (hunit : ∀ i, IsCoprime (p : ℤ) (z i 0))
    (hres : ∀ i j, (p : ℤ) ∣ z i j.succ - a j * z i 0)
    (hz : ∀ i, eval (z i) f = 0) :
    ∃ u : Fin s → ℤ,
      (∀ i, (p : ℤ) ^ hypersurfaceMultiplicityExponent (n + 1) μ s ∣
        u i * z i 0 - 1) ∧
      (p : ℤ) ^ hypersurfaceMultiplicityExponent (n + 1) μ s ∣
        (Matrix.of fun i j => u i ^ deg j * eval (z i) (F j)).det := by
  have hex (i : Fin s) := exists_integer_inverse_of_isCoprime
    (show IsCoprime ((p : ℤ) ^ hypersurfaceMultiplicityExponent (n + 1) μ s)
      (z i 0) from (hunit i).pow_left)
  choose u hu _ using hex
  exact ⟨u, hu, mixed_degree_projective_chart_det_divisibility
    f hfhom F deg hF z a hf hμ hres hz u hu⟩

end
end CCDN
