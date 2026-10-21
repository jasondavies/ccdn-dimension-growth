/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Auxiliary.HypersurfaceBadPrimeComparison
public import CCDN.Auxiliary.AffineChartPrimeDeterminant
import CCDN.Auxiliary.AffineChartGlobalDeterminant
/-! The normalized no-auxiliary comparison for a finite prime set outside which
every large prime is an affine-chart good prime. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The comparison retaining the charge of a finite prime set `bad` outside which
every prime above `27 d ^ 4` is an affine-chart good prime. -/
theorem affine_chart_auxiliaryRankComparison {n d t : ℕ}
    (order : MonomialOrder (Fin (n + 3))) (f : MvPolynomial (Fin (n + 3)) ℤ)
    (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) (hd : 0 < d)
    (z : Fin t → IntPoint (n + 3)) (hprim : ∀ i, Finset.univ.gcd (z i) = 1)
    (hz : ∀ i, eval (z i) f = 0) (bad : Finset ℕ)
    (hgood : ∀ (p : ℕ) [Fact p.Prime], p ∉ bad → 27 * (d : ℝ) ^ 4 < p →
      AffineChartGoodPrime f z p) :
    AuxiliaryRankComparison order f d z bad :=
  auxiliaryRankComparison_of_determinant_lower order f hf hf0 hd z hz bad
    fun _ _ _ a F hs hF hi => affine_chart_determinant_log_lower_at_rank hs f hf hd F hF
      (z ∘ a) (fun i => hprim (a i)) (fun i => hz (a i)) hi bad fun p _ hp hcut =>
        have h := hgood p (Finset.mem_sdiff.mp hp).2 hcut
        ⟨h.1, fun i => h.2 (a i)⟩

end
end CCDN
