module

public import CCDN.GenericPlaneSmoothness
public import CCDN.SmoothPlaneMinor

/-! A nonzero polynomial determinant in the generic slope parameters. For a
positioned irreducible equation with a smooth origin, the minor is constructed
over the parameter polynomial ring, by descent from its fraction field. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

lemma genericPlaneMap_totalDegree_le {K F σ : Type*} [Field K] [Field F]
    [Algebra K F] [Algebra (MvPolynomial σ K) F]
    (f : MvPolynomial (Option σ) K) :
    (genericPlaneMap K F σ f).totalDegree ≤ f.totalDegree := by
  apply linear_eval₂_totalDegree_le _ _ _ f
  intro i
  cases i with
  | none => simp
  | some i => exact (totalDegree_mul _ _).trans (by simp)

/-- In characteristic greater than 2*d^2, a positioned irreducible hypersurface
with a smooth origin supplies a nonzero minor polynomial in its plane slopes. -/
theorem exists_genericPlane_minor
    {K σ : Type*} [Field K] {p : ℕ} [CharP K p]
    (d : ℕ) (hd : 0 < d) (f : MvPolynomial (Option σ) K) (hf : Irreducible f)
    (hm : (optionEquivLeft K σ f).Monic)
    (hdeg : (optionEquivLeft K σ f).natDegree = d)
    (htotal : f.totalDegree ≤ d) (hchar : 2 * d ^ 2 < p)
    (hz : eval (0 : Option σ → K) f = 0)
    (hs : eval (0 : Option σ → K) (pderiv none f) ≠ 0) :
    ∃ (a : Fin (2 * d ^ 2 - 1) → ℕ × ℕ)
      (c : Fin (2 * d ^ 2 - 1) → ClosedFormColumns d),
      Function.Injective a ∧ Function.Injective c ∧
      ((closedFormCoefficientMatrix d (genericPlanePolynomial f)).submatrix a c).det ≠ 0 := by
  let R := MvPolynomial σ K
  let F := FractionRing R
  let φ : R →+* F := algebraMap R F
  let g := genericPlaneMap K F σ f
  have : CharP F p := charP_of_injective_algebraMap (algebraMap K F).injective p
  have hx : 0 < (optionEquivLeft K σ f).natDegree := hdeg ▸ hd
  have hpos : 0 < f.totalDegree := by
    rw [natDegree_optionEquivLeft] at hx
    exact hx.trans_le (degreeOf_le_totalDegree f none)
  have hgi : Irreducible g := genericPlaneMap_irreducible f hf hpos hm hx
  have hgz : eval (0 : Fin 2 → F) g = 0 := by
    rw [genericPlaneMap_eval_zero, hz, map_zero]
  have hgs : eval (0 : Fin 2 → F) (pderiv 0 g) ≠ 0 := by
    rw [genericPlaneMap_pderiv, genericPlaneMap_eval_zero]
    exact (map_ne_zero (algebraMap K F)).mpr hs
  have hgm : (bivariatePolynomialEquiv F g).Monic := by
    rw [genericPlaneMap_bivariate]
    exact bivariateMap_monic φ (genericPlanePolynomial_monic f hm)
  have hgd : (bivariatePolynomialEquiv F g).natDegree = d := by
    rw [genericPlaneMap_bivariate, bivariateMap_natDegree_of_monic φ
      (genericPlanePolynomial_monic f hm), genericPlanePolynomial_natDegree f hm, hdeg]
  have hgt : g.totalDegree ≤ d := (genericPlaneMap_totalDegree_le f).trans htotal
  obtain ⟨a, c, ha, hc, hdet⟩ := exists_closedForm_minor_of_smooth_plane_point
    (p := p) d hd g hgi (0 : Fin 2 → F) 0 hgz hgs hgm hgd hgt hchar
  refine ⟨a, c, ha, hc, ?_⟩
  intro he
  apply hdet
  rw [genericPlaneMap_bivariate, ← closedForm_minor_map, he, map_zero]

end
end CCDN
