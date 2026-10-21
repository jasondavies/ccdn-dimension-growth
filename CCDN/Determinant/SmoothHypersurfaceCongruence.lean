module

public import CCDN.Determinant.HypersurfaceResidue
public import CCDN.Determinant.PlaneMultiplicitySmooth
public import CCDN.Analysis.PrimeProduct
public import CCDN.Determinant.BlockDeterminant
import all ArithmeticHeights.BombieriVaaler

/-! At a nonsingular reduced point the translated hypersurface
equation has multiplicity one. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- At a nonsingular reduced point the translated equation has
multiplicity one. -/
theorem smooth_hypersurface_origin_order {p : ℕ} [Fact p.Prime] {σ : Type*}
    (f : MvPolynomial σ ℤ) (a : σ → ℤ)
    (ha : eval₂ (Int.castRingHom (ZMod p)) (fun j => (a j : ZMod p)) f = 0)
    (hs : ∃ j, eval (fun i => (a i : ZMod p))
      (pderiv j (map (Int.castRingHom (ZMod p)) f)) ≠ 0) :
    map (Int.castRingHom (ZMod p)) (originShift a f) ∈ idealOfVars σ (ZMod p) ^ 1 ∧
    homogeneousComponent 1 (map (Int.castRingHom (ZMod p)) (originShift a f)) ≠ 0 := by
  have hf : map (Int.castRingHom (ZMod p)) f ≠ 0 := by
    intro hz
    obtain ⟨j, hj⟩ := hs
    exact hj (by simp [hz])
  obtain ⟨μ, hμ, _, hpow, hcomp⟩ := exists_hypersurface_reduction_multiplicity f a hf ha
  have he : μ = 1 := by
    rw [originShift_map] at hpow
    exact origin_order_eq_one_of_smooth _ _ hμ hpow hs
  subst μ
  exact ⟨hpow, hcomp⟩

end
end CCDN
