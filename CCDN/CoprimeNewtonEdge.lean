module

public import CCDN.WeightedPolynomialTop
public import Mathlib.Data.Nat.ModEq

/-! A coprime Newton edge forces irreducibility over every field.
The proof uses the absence of two distinct monomials of equal weight
below the weight of the edge, rather than a supplied Newton-polytope theorem. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Finset Classical

def coprimeEdgeWeight (d e : ℕ) : Fin 2 → ℕ := fun i => if i = 0 then e else d

lemma coprimeEdgeWeight_pos {d e : ℕ} (hd : 0 < d) (he : 0 < e) (i : Fin 2) :
    0 < coprimeEdgeWeight d e i := by
  unfold coprimeEdgeWeight
  split_ifs <;> assumption

lemma coprimeEdgeWeight_apply (d e : ℕ) (m : Fin 2 →₀ ℕ) :
    Finsupp.weight (coprimeEdgeWeight d e) m = e * m 0 + d * m 1 := by
  simp [Finsupp.weight_apply, Finsupp.sum_fintype, Fin.sum_univ_two,
    coprimeEdgeWeight, mul_comm]

lemma coprime_weight_eq_below_edge {d e : ℕ} (hd : 0 < d) (_he : 0 < e)
    (hcop : d.Coprime e) {m n : Fin 2 →₀ ℕ}
    (hweight : Finsupp.weight (coprimeEdgeWeight d e) m =
      Finsupp.weight (coprimeEdgeWeight d e) n)
    (hsmall : Finsupp.weight (coprimeEdgeWeight d e) m < d * e) : m = n := by
  rw [coprimeEdgeWeight_apply, coprimeEdgeWeight_apply] at hweight
  rw [coprimeEdgeWeight_apply] at hsmall
  have hm0 : m 0 < d := by nlinarith
  have hn0 : n 0 < d := by nlinarith
  have hmod : Nat.ModEq d (e * m 0) (e * n 0) := by
    change (e * m 0) % d = (e * n 0) % d
    have hh := congrArg (fun x : ℕ => x % d) hweight
    simpa only [Nat.add_mod, Nat.mul_mod_right, Nat.add_zero, Nat.mod_mod] using hh
  have heq0 := Nat.ModEq.cancel_left_of_coprime hcop hmod
  change m 0 % d = n 0 % d at heq0
  rw [Nat.mod_eq_of_lt hm0, Nat.mod_eq_of_lt hn0] at heq0
  have heq1 : m 1 = n 1 := by nlinarith
  ext i
  fin_cases i <;> assumption

lemma weighted_top_monomial_of_below_coprime_edge {K : Type*} [Field K]
    {d e : ℕ} (hd : 0 < d) (he : 0 < e) (hcop : d.Coprime e)
    (f : MvPolynomial (Fin 2) K) (hf : f ≠ 0)
    (hlt : f.weightedTotalDegree (coprimeEdgeWeight d e) < d * e) :
    ∃ m a, weightedHomogeneousComponent (coprimeEdgeWeight d e)
      (f.weightedTotalDegree (coprimeEdgeWeight d e)) f = monomial m a := by
  let w := coprimeEdgeWeight d e
  let top := weightedHomogeneousComponent w (f.weightedTotalDegree w) f
  have htop : top ≠ 0 := weighted_top_component_ne_zero w f hf
  obtain ⟨m, hm⟩ := support_nonempty.mpr htop
  have hhom : top.IsWeightedHomogeneous w (f.weightedTotalDegree w) :=
    weightedHomogeneousComponent_isWeightedHomogeneous _ _
  have hmweight := hhom (mem_support_iff.mp hm)
  refine ⟨m, top.coeff m, eq_monomial_of_support_subset_singleton ?_⟩
  intro n hn
  have hnweight := hhom (mem_support_iff.mp hn)
  exact coprime_weight_eq_below_edge hd he hcop (hnweight.trans hmweight.symm)
    (hnweight ▸ hlt)

/-- Nonzero coefficients at the ends of a coprime edge, with no monomial
above that edge, imply irreducibility in arbitrary characteristic. -/
theorem coprime_newton_edge_irreducible {K : Type*} [Field K]
    (f : MvPolynomial (Fin 2) K) {d e : ℕ}
    (hd : 0 < d) (he : 0 < e) (hcop : d.Coprime e)
    (hdegree : f.weightedTotalDegree (coprimeEdgeWeight d e) = d * e)
    (hx : f.coeff (Finsupp.single 0 d) ≠ 0)
    (hy : f.coeff (Finsupp.single 1 e) ≠ 0) : Irreducible f := by
  let w := coprimeEdgeWeight d e
  have hf : f ≠ 0 := by intro hz; simp [hz] at hx
  have hedge : Finsupp.single (0 : Fin 2) d ≠ Finsupp.single 1 e := by
    intro hh
    have h := congrArg (fun m : Fin 2 →₀ ℕ => m 0) hh
    simp at h
    omega
  have htopx : (weightedHomogeneousComponent w (f.weightedTotalDegree w) f).coeff
      (Finsupp.single 0 d) ≠ 0 := by
    simpa [coeff_weightedHomogeneousComponent, w, hdegree, coprimeEdgeWeight,
      Finsupp.weight_apply, mul_comm] using hx
  have htopy : (weightedHomogeneousComponent w (f.weightedTotalDegree w) f).coeff
      (Finsupp.single 1 e) ≠ 0 := by
    simpa [coeff_weightedHomogeneousComponent, w, hdegree, coprimeEdgeWeight,
      Finsupp.weight_apply, mul_comm] using hy
  refine ⟨?_, ?_⟩
  · intro hu
    have hc := totalDegree_eq_zero_iff_eq_C.mp (isUnit_iff_totalDegree_of_isReduced.mp hu).2
    have hz : f.coeff (Finsupp.single 0 d) = 0 := by
      rw [hc, coeff_C]
      exact ite_eq_right (Ne.symm (Finsupp.single_ne_zero.mpr hd.ne'))
    exact hx hz
  · intro g h hprod
    have hg : g ≠ 0 := by intro hz; exact hf (by rw [hprod, hz, zero_mul])
    have hh : h ≠ 0 := by intro hz; exact hf (by rw [hprod, hz, mul_zero])
    by_cases hgdegree : g.weightedTotalDegree w = 0
    · exact Or.inl (weightedTotalDegree_zero_isUnit w (coprimeEdgeWeight_pos hd he) g hg hgdegree)
    by_cases hhdegree : h.weightedTotalDegree w = 0
    · exact Or.inr (weightedTotalDegree_zero_isUnit w (coprimeEdgeWeight_pos hd he) h hh hhdegree)
    have hsum : g.weightedTotalDegree w + h.weightedTotalDegree w = d * e := by
      rw [← weightedTotalDegree_mul_of_ne_zero w hg hh, ← hprod]
      exact hdegree
    obtain ⟨m, a, hgm⟩ := weighted_top_monomial_of_below_coprime_edge hd he hcop g hg (by change g.weightedTotalDegree w < d * e; omega)
    obtain ⟨n, b, hhn⟩ := weighted_top_monomial_of_below_coprime_edge hd he hcop h hh (by change h.weightedTotalDegree w < d * e; omega)
    have hmono : weightedHomogeneousComponent w (f.weightedTotalDegree w) f =
        monomial (m + n) (a * b) := by
      rw [hprod, weighted_top_component_mul, hgm, hhn, monomial_mul_monomial]
    rw [hmono, coeff_monomial] at htopx htopy
    have hxedge : m + n = Finsupp.single 0 d := by
      by_contra hn
      simp only [ite_eq_right hn, ne_eq, not_true_eq_false] at htopx
    have hyedge : m + n = Finsupp.single 1 e := by
      by_contra hn
      simp only [ite_eq_right hn, ne_eq, not_true_eq_false] at htopy
    exact False.elim (hedge (hxedge.symm.trans hyedge))

end
end CCDN
