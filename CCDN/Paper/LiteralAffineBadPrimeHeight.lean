/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.AuxiliaryPolynomial.LiteralAffineBadPrimes
public import CCDN.Height.IntegerCoefficientHeight
/-! Corollary 3.2.3 for the literal affine bad-prime factor of Definition
3.2.1, including degree drops which preserve irreducibility.
Here "literal" means the paper's Definition 3.2.1 applied verbatim to the affine
polynomial (`literalAffineBadPrimeFactor`, see `LiteralAffineBadPrimes`), as opposed to
`hypersurfaceBadPrimeFactor`, which also counts primes at which the degree drops. -/

@[expose] public section
namespace CCDN
noncomputable section

/-- The height estimate concerns the literal factor itself, for every
integer polynomial and any coefficient bound H at least one. -/
theorem literalAffineBadPrimeFactor_le_max {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) ℤ) (H : ℝ) (hH : 1 ≤ H)
    (hcoeff : CoefficientHeightLE f H) :
    literalAffineBadPrimeFactor f ≤
      (2 * Real.exp (2 * mertensError + 1) * hypersurfaceHeightConstant (n + 1)) *
        max (Real.log H / (f.totalDegree : ℝ) ^ 2) 1 :=
  (literalAffineBadPrimeFactor_le_inclusive f).trans
    (hypersurfaceBadPrimeFactor_le_max f H hH hcoeff)

end
end CCDN
