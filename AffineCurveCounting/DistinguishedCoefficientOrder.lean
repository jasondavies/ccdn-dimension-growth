module

public import AffineCurveCounting.HomogeneousLeadingCoefficient

/-! A monomial order that puts a chosen pure coordinate power first. This
lets the positioned estimates use the paper's actual distinguished coefficient. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial
open scoped MonomialOrder

/-- Lexicographic order after interchanging the selected variable with variable zero. -/
def distinguishedCoefficientOrder {n : ℕ} (i : Fin (n + 1)) :
    MonomialOrder (Fin (n + 1)) where
  syn := MonomialOrder.lex.syn
  toSyn := (Finsupp.domCongr (Equiv.swap i 0)).trans MonomialOrder.lex.toSyn
  toSyn_monotone := by
    intro a b hab
    apply MonomialOrder.lex.toSyn_monotone
    intro j
    exact hab ((Equiv.swap i 0).symm j)

lemma distinguishedCoefficientOrder_le_pure {n d : ℕ} (i : Fin (n + 1))
    (m : Fin (n + 1) →₀ ℕ) (hm : m.sum (fun _ e => e) ≤ d) :
    m ≼[distinguishedCoefficientOrder i] Finsupp.single i d := by
  have hs : (Finsupp.equivMapDomain (Equiv.swap i 0) m).sum (fun _ e => e) =
      m.sum (fun _ e => e) := by
    simp [Finsupp.sum, Finsupp.equivMapDomain, Finset.sum_map]
  have hh := exponent_le_pure_first (Finsupp.equivMapDomain (Equiv.swap i 0) m)
    (hs.trans_le hm)
  change MonomialOrder.lex.toSyn (Finsupp.equivMapDomain (Equiv.swap i 0) m) ≤
    MonomialOrder.lex.toSyn (Finsupp.equivMapDomain (Equiv.swap i 0) (Finsupp.single i d))
  simpa only [Finsupp.equivMapDomain_single, Equiv.swap_apply_left] using hh

/-- A nonzero coefficient of the selected pure power is the leading coefficient
for an actual monomial order; no coordinate change of the equation is required. -/
lemma distinguishedCoefficientOrder_leadingCoeff {R : Type*} [CommRing R] {n d : ℕ}
    (i : Fin (n + 1)) (f : MvPolynomial (Fin (n + 1)) R) (hd : f.totalDegree ≤ d)
    (hc : f.coeff (Finsupp.single i d) ≠ 0) :
    (distinguishedCoefficientOrder i).leadingCoeff f = f.coeff (Finsupp.single i d) := by
  have he : (distinguishedCoefficientOrder i).degree f = Finsupp.single i d := by
    apply (distinguishedCoefficientOrder i).toSyn.injective
    apply le_antisymm
    · apply MonomialOrder.degree_le_iff.mpr
      intro m hm
      exact distinguishedCoefficientOrder_le_pure i m ((le_totalDegree hm).trans hd)
    · exact (distinguishedCoefficientOrder i).le_degree (mem_support_iff.mpr hc)
  change f.coeff ((distinguishedCoefficientOrder i).degree f) = _
  rw [he]

end
end AffineCurveCounting
