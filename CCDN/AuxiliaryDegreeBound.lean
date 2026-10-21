module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Named quantities in the determinant and auxiliary-polynomial bounds for a
hypersurface of degree `d` in `ℙ^(n+2)`, and the bracket `auxDegreeBound` of the
coefficient-sensitive auxiliary theorem (CCDN Theorem 3.1.1). -/

@[expose] public section
namespace CCDN
noncomputable section

/-- The root `d ^ (1 / (n + 1))` of the degree. -/
abbrev degreeRoot (n d : ℕ) : ℝ := (d : ℝ) ^ (1 / (n + 1 : ℝ))

/-- The root `((n + 1)!) ^ (1 / (n + 1))`. -/
abbrev factorialRoot (n : ℕ) : ℝ := ((n + 1).factorial : ℝ) ^ (1 / (n + 1 : ℝ))

/-- The coefficient-height exponent `1 / ((n + 1) d d ^ (1 / (n + 1)))`. -/
abbrev heightExponent (n d : ℕ) : ℝ := 1 / ((n + 1 : ℝ) * d * degreeRoot n d)

/-- The radius exponent `(n + 2) / ((n + 1) d ^ (1 / (n + 1)))`. -/
abbrev boxExponent (n d : ℕ) : ℝ := (n + 2 : ℝ) / ((n + 1 : ℝ) * degreeRoot n d)

/-- The bad-prime factor `exp (∑ p ∈ bad, log p / p)` of a finite set of primes. -/
abbrev primeSetFactor (bad : Finset ℕ) : ℝ := Real.exp (∑ p ∈ bad, Real.log p / p)

/-- The bracket of the coefficient-sensitive auxiliary degree bound,
`d^(4 - 1/(n+1)) b B^boxExponent / H^heightExponent + d^(1 - 1/(n+1)) log B + d^(4 - 1/(n+1))`,
for points of height at most `B` on an equation with coefficient height `H` and
bad-prime factor `b`. -/
def auxDegreeBound (n d : ℕ) (B b H : ℝ) : ℝ :=
  (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) * b * B ^ boxExponent n d / H ^ heightExponent n d +
    (d : ℝ) ^ (1 - 1 / (n + 1 : ℝ)) * Real.log B + (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ))

lemma one_le_four_sub_inv (n : ℕ) : (1 : ℝ) ≤ 4 - 1 / (n + 1 : ℝ) := by
  have h := (div_le_one (by positivity : (0 : ℝ) < n + 1)).mpr
    (show 1 ≤ (n + 1 : ℝ) by have := Nat.cast_nonneg (α := ℝ) n; linarith)
  linarith

/-- `d ≤ d ^ (4 - 1 / (n + 1))` for a positive degree. -/
lemma le_rpow_four_sub_inv {n d : ℕ} (hd : 0 < d) :
    (d : ℝ) ≤ (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hd1 (one_le_four_sub_inv n)

lemma auxDegreeBound_nonneg {n d : ℕ} {B b H : ℝ} (hB : 1 ≤ B) (hb : 0 ≤ b) (hH : 0 ≤ H) :
    0 ≤ auxDegreeBound n d B b H := by
  unfold auxDegreeBound
  have := Real.log_nonneg hB
  have : (0 : ℝ) ≤ B := by linarith
  positivity

end
end CCDN
