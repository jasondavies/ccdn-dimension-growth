module

public import CCDN.ClosedFormScaling

/-! Reducibility forces rank drop in the characteristic-zero coefficient
 matrix, including every repeated-factor multiplicity. -/

@[expose] public section
namespace CCDN
noncomputable section
open Polynomial

/-- A nontrivial coprime product gives two independent bounded closed forms,
and hence the required matrix rank drop. -/
theorem closedForm_rank_drop_of_coprime_factors_charZero
    {F : Type*} [Field F] [CharZero F] (d : ℕ) (hd : 0 < d)
    (g h : F[X][X]) (hg : Irreducible g) (hgm : g.Monic)
    (hh : h ≠ 0) (hhpos : 0 < h.natDegree)
    (hcop : IsCoprime (g.map (algebraMap F[X] (RatFunc F)))
      (h.map (algebraMap F[X] (RatFunc F))))
    (hdeg : (g * h).natDegree = d) (htotal : bivariateTotalDegree (g * h) ≤ d) :
    (closedFormCoefficientMatrix d (g * h)).rank + 2 ≤ 2 * d ^ 2 := by
  let φ := algebraMap F[X] (RatFunc F)
  have hinj := RatFunc.algebraMap_injective F
  have hgpos := hgm.natDegree_pos_of_not_isUnit hg.not_isUnit
  have hgnat : (g.map φ).natDegree = g.natDegree := natDegree_map_eq_of_injective hinj _
  have hhnat : (h.map φ).natDegree = h.natDegree := natDegree_map_eq_of_injective hinj _
  have hgR : Irreducible (g.map φ) := hgm.irreducible_iff_irreducible_map_fraction_map.mp hg
  have hgg : IsCoprime (g.map φ) (g.map φ).derivative :=
    hgR.separable
  have hh' : (h.map φ).derivative ≠ 0 :=
    Polynomial.derivative_ne_zero.mpr (Nat.ne_of_gt (hhnat ▸ hhpos))
  have hgd : 0 < bivariateTotalDegree g := hgpos.trans_le (bivariate_natDegree_le_totalDegree g)
  obtain ⟨hpgrid, hqgrid⟩ := bivariate_factor_form_in_grid d g h hg.ne_zero hh hgd htotal
  apply closedForm_rank_drop_of_extra_form d hd (g * h)
    (h * g.derivative) (h * (bivariateCoefficientDerivative F) g) htotal
    (Polynomial.derivative_ne_zero.mpr (Nat.ne_of_gt (hdeg ▸ hd))) hpgrid hqgrid
  · have he := bivariate_factor_closed_form g h
    change _ - _ - _ + _ = (0 : F[X][X])
    linear_combination he
  · intro a he
    apply factor_numerator_not_scalar_gradient (g.map φ) (h.map φ)
      (natDegree_pos_iff_degree_pos.mp (hgnat ▸ hgpos)) hcop hgg hh' (algebraMap F (RatFunc F) a)
    simpa only [Polynomial.map_mul, Polynomial.map_C, derivative_map, derivative_mul, Polynomial.map_add,
      RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C, φ] using congrArg (Polynomial.map φ) he

/-- Repeated irreducible factors of every multiplicity at least two likewise
force rank drop; the whole equation need not be squarefree. -/
theorem closedForm_rank_drop_of_repeated_factor_charZero
    {F : Type*} [Field F] [CharZero F] (d k : ℕ) (hd : 0 < d)
    (g h : F[X][X]) (hg : Irreducible g) (hgm : g.Monic) (hh : h ≠ 0)
    (hcop : IsCoprime (g.map (algebraMap F[X] (RatFunc F)))
      (h.map (algebraMap F[X] (RatFunc F))))
    (hdeg : (g ^ (k + 2) * h).natDegree = d)
    (htotal : bivariateTotalDegree (g ^ (k + 2) * h) ≤ d) :
    (closedFormCoefficientMatrix d (g ^ (k + 2) * h)).rank + 2 ≤ 2 * d ^ 2 := by
  let φ := algebraMap F[X] (RatFunc F)
  have hinj := RatFunc.algebraMap_injective F
  have hgpos := hgm.natDegree_pos_of_not_isUnit hg.not_isUnit
  have hgnat : (g.map φ).natDegree = g.natDegree := natDegree_map_eq_of_injective hinj _
  have hgR : Irreducible (g.map φ) := hgm.irreducible_iff_irreducible_map_fraction_map.mp hg
  have hgg : IsCoprime (g.map φ) (g.map φ).derivative :=
    hgR.separable
  have hgd : 0 < bivariateTotalDegree g := hgpos.trans_le (bivariate_natDegree_le_totalDegree g)
  obtain ⟨hpgrid, hqgrid⟩ := bivariate_power_factor_form_in_grid d k g h hg.ne_zero hh hgd htotal
  apply closedForm_rank_drop_of_extra_form d hd (g ^ (k + 2) * h)
    (g ^ k * h * g.derivative) (g ^ k * h * (bivariateCoefficientDerivative F) g) htotal
    (Polynomial.derivative_ne_zero.mpr (Nat.ne_of_gt (hdeg ▸ hd))) hpgrid hqgrid
  · have he := bivariate_power_factor_closed_form g h k
    change _ - _ - _ + _ = (0 : F[X][X])
    linear_combination he
  · intro a he
    apply power_factor_numerator_not_scalar_gradient (g.map φ) (h.map φ) k
      (natDegree_pos_iff_degree_pos.mp (hgnat ▸ hgpos)) hcop hgg (algebraMap F (RatFunc F) a)
    have hp : (g.map φ) ^ (k + 2) * h.map φ = (g ^ (k + 2) * h).map φ := by simp
    rw [hp, Polynomial.derivative_map (g ^ (k + 2) * h) φ]
    simpa only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, derivative_map,
      RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C, φ] using congrArg (Polynomial.map φ) he

/-- A reducible normalized equation of total degree at most d, with outer
degree d in characteristic zero, has coefficient-matrix kernel dimension
at least two. Both squarefree and repeated-factor cases are covered. -/
theorem closedForm_rank_drop_of_not_irreducible_charZero
    {F : Type*} [Field F] [CharZero F] (d : ℕ) (hd : 0 < d)
    (f : F[X][X]) (hf : f.Monic) (hred : ¬Irreducible f)
    (hdeg : f.natDegree = d) (htotal : bivariateTotalDegree f ≤ d) :
    (closedFormCoefficientMatrix d f).rank + 2 ≤ 2 * d ^ 2 := by
  have hfu : ¬IsUnit f := not_isUnit_of_natDegree_pos f (hdeg ▸ hd)
  obtain ⟨g, h, m, hg, hgm, hhm, hm, he, hcop⟩ :=
    exists_monic_bivariate_primary_factor f hf hfu
  by_cases hm1 : m = 1
  · have he' : f = g * h := by simpa only [hm1, pow_one] using he
    have hhu : ¬IsUnit h := by
      intro hhU
      apply hred
      rw [he']
      exact (associated_mul_unit_left g h hhU).irreducible_iff.mpr hg
    rw [he'] at hdeg htotal ⊢
    exact closedForm_rank_drop_of_coprime_factors_charZero d hd g h hg hgm hhm.ne_zero
      (hhm.natDegree_pos_of_not_isUnit hhu) hcop hdeg htotal
  · have hm2 : m = (m - 2) + 2 := by omega
    rw [hm2] at he
    rw [he] at hdeg htotal ⊢
    exact closedForm_rank_drop_of_repeated_factor_charZero d (m - 2) hd g h hg hgm
      hhm.ne_zero hcop hdeg htotal

/-- The characteristic-zero reducibility criterion likewise only needs a nonzero
constant outer leading coefficient. -/
theorem closedForm_rank_drop_of_constant_leading_charZero
    {F : Type*} [Field F] [CharZero F] (d : ℕ) (hd : 0 < d)
    (a : F) (ha : a ≠ 0) (f : F[X][X])
    (hl : f.leadingCoeff = C a) (hred : ¬Irreducible f)
    (hdeg : f.natDegree = d) (htotal : bivariateTotalDegree f ≤ d) :
    (closedFormCoefficientMatrix d f).rank + 2 ≤ 2 * d ^ 2 := by
  have hm := bivariate_monic_normalize a ha f hl
  have hi : ¬Irreducible (a⁻¹ • f) := fun h =>
    hred ((bivariate_irreducible_smul_iff a⁻¹ (inv_ne_zero ha) f).mp h)
  have hr := closedForm_rank_drop_of_not_irreducible_charZero d hd (a⁻¹ • f) hm hi
    ((natDegree_smul f (inv_ne_zero ha)).trans hdeg)
    ((bivariateTotalDegree_smul_le _ _).trans htotal)
  rw [closedForm_rank_smul _ (inv_ne_zero ha)] at hr
  exact hr

end
end CCDN
