module

public import CCDN.HypersurfaceResidue
public import CCDN.PlaneMultiplicitySmooth
public import CCDN.PrimeProduct
public import CCDN.BlockDeterminant
import all ArithmeticHeights.BombieriVaaler

/-! Simultaneous congruence divisors for smooth hypersurface points.
These are the local divisors needed for a congruence-refined auxiliary. -/

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

/-- Exact-zero evaluation determinants in a single smooth residue class
have the dimension-sharp multiplicity-one divisor. -/
theorem smooth_hypersurface_congruence_det {p n s : ℕ} [Fact p.Prime]
    (f : MvPolynomial (Fin (n + 2)) ℤ) (a : Fin (n + 2) → ℤ)
    (ha : eval₂ (Int.castRingHom (ZMod p)) (fun j => (a j : ZMod p)) f = 0)
    (hs : ∃ j, eval (fun i => (a i : ZMod p))
      (pderiv j (map (Int.castRingHom (ZMod p)) f)) ≠ 0)
    (x : Fin s → Fin (n + 2) → ℤ) (hx : ∀ i j, (p : ℤ) ∣ x i j - a j)
    (hzero : ∀ i, eval (x i) f = 0)
    (F : Fin s → MvPolynomial (Fin (n + 2)) ℤ) :
    (p : ℤ) ^ hypersurfaceMultiplicityExponent (n + 1) 1 s ∣
      (Matrix.of fun i j => eval (x i) (F j)).det := by
  obtain ⟨hpow, hcomp⟩ := smooth_hypersurface_origin_order f a ha hs
  exact hypersurface_residue_pow_dvd_det_mod f a hpow hcomp x hx
    (fun i => by rw [hzero]; exact dvd_zero _) F

/-- All maximal minors share the smooth congruence divisor. -/
theorem smooth_hypersurface_congruence_minorGcd {p n s N : ℕ} [Fact p.Prime]
    (f : MvPolynomial (Fin (n + 2)) ℤ) (a : Fin (n + 2) → ℤ)
    (ha : eval₂ (Int.castRingHom (ZMod p)) (fun j => (a j : ZMod p)) f = 0)
    (hs : ∃ j, eval (fun i => (a i : ZMod p))
      (pderiv j (map (Int.castRingHom (ZMod p)) f)) ≠ 0)
    (x : Fin s → Fin (n + 2) → ℤ) (hx : ∀ i j, (p : ℤ) ∣ x i j - a j)
    (hzero : ∀ i, eval (x i) f = 0)
    (F : Fin N → MvPolynomial (Fin (n + 2)) ℤ) :
    (p : ℤ) ^ hypersurfaceMultiplicityExponent (n + 1) 1 s ∣
      Int.Matrix.minorGcd (Matrix.of fun i j => eval (x i) (F j)) := by
  classical
  unfold Int.Matrix.minorGcd
  apply Finset.dvd_gcd
  intro S _
  rw [Matrix.plucker_row_eq_det_submatrix]
  exact smooth_hypersurface_congruence_det f a ha hs x hx hzero _

/-- Congruence conditions at distinct primes multiply. The final exponent
is that of one smooth residue class, and no point-count hypothesis occurs. -/
theorem smooth_hypersurface_congruence_product {n s N : ℕ}
    (f : MvPolynomial (Fin (n + 2)) ℤ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (a : ℕ → Fin (n + 2) → ℤ)
    (ha : ∀ p ∈ P, eval₂ (Int.castRingHom (ZMod p)) (fun j => (a p j : ZMod p)) f = 0)
    (hs : ∀ p ∈ P, ∃ j, eval (fun i => (a p i : ZMod p))
      (pderiv j (map (Int.castRingHom (ZMod p)) f)) ≠ 0)
    (x : Fin s → Fin (n + 2) → ℤ)
    (hx : ∀ p ∈ P, ∀ i j, (p : ℤ) ∣ x i j - a p j)
    (hzero : ∀ i, eval (x i) f = 0)
    (F : Fin N → MvPolynomial (Fin (n + 2)) ℤ) :
    (∏ p ∈ P, (p : ℤ)) ^ hypersurfaceMultiplicityExponent (n + 1) 1 s ∣
      Int.Matrix.minorGcd (Matrix.of fun i j => eval (x i) (F j)) := by
  rw [← Finset.prod_pow]
  apply prime_power_product_dvd P (fun _ => hypersurfaceMultiplicityExponent (n + 1) 1 s) _ hP
  intro p hp
  let : Fact p.Prime := ⟨hP p hp⟩
  exact smooth_hypersurface_congruence_minorGcd f (a p) (ha p hp) (hs p hp) x
    (hx p hp) hzero F

end
end CCDN
