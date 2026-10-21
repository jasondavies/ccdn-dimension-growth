module

public import CCDN.Determinant.SmoothHypersurfaceCongruence
public import CCDN.Algebra.ProjectiveHypersurfaceLocal
import all ArithmeticHeights.BombieriVaaler

/-! Smooth projective congruence classes give simultaneous divisors
for homogeneous evaluation matrices. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

theorem smooth_projective_hypersurface_congruence_minorGcd {p n s N d M : ℕ}
    [Fact p.Prime] (f : MvPolynomial (Fin (n + 3)) ℤ) (hf : f.IsHomogeneous d)
    (F : Fin N → MvPolynomial (Fin (n + 3)) ℤ) (hF : ∀ j, (F j).IsHomogeneous M)
    (z : Fin s → IntPoint (n + 3)) (k : Fin (n + 3)) (a : Fin (n + 2) → ℤ)
    (ha : eval₂ (Int.castRingHom (ZMod p)) (fun j => (a j : ZMod p))
      (projectiveHypersurfaceChart k f) = 0)
    (hs : ∃ j, eval (fun i => (a i : ZMod p)) (pderiv j
      (map (Int.castRingHom (ZMod p)) (projectiveHypersurfaceChart k f))) ≠ 0)
    (hunit : ∀ i, IsCoprime (p : ℤ) (z i k))
    (hres : ∀ i j, (p : ℤ) ∣ z i (Equiv.swap 0 k j.succ) - a j * z i k)
    (hz : ∀ i, eval (z i) f = 0) :
    (p : ℤ) ^ hypersurfaceMultiplicityExponent (n + 1) 1 s ∣
      Int.Matrix.minorGcd (Matrix.of fun i j => eval (z i) (F j)) := by
  classical
  obtain ⟨hpow, hcomp⟩ := smooth_hypersurface_origin_order
    (projectiveHypersurfaceChart k f) a ha hs
  unfold Int.Matrix.minorGcd
  apply Finset.dvd_gcd
  intro S _
  rw [Matrix.plucker_row_eq_det_submatrix]
  exact projective_hypersurface_local_det_divisibility f hf _
    (fun j => hF _) z k a hpow hcomp hunit hres hz

end
end CCDN
