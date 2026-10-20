module

public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Data.Multiset.Powerset

/-! A degree-only bound for the actual intermediate fields of a finite
separable extension. Monic divisors are encoded by root submultisets in
an algebraic closure, so their number is at most two to the degree. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open Module Polynomial IntermediateField

theorem monic_divisors_card_le_two_pow_natDegree
    {K : Type*} [Field K] (f : K[X]) (hf : f ≠ 0) :
    Nat.card {g : K[X] // g.Monic ∧ g ∣ f} ≤ 2 ^ f.natDegree := by
  classical
  let L := AlgebraicClosure K
  let ι := algebraMap K L
  let P := ((f.map ι).roots.powerset).toFinset
  let e : {g : K[X] // g.Monic ∧ g ∣ f} → ↥P := fun g =>
    ⟨(g.1.map ι).roots, by
      apply Multiset.mem_toFinset.mpr
      apply Multiset.mem_powerset.mpr
      exact Polynomial.roots.le_of_dvd (Polynomial.map_ne_zero hf)
        (Polynomial.map_dvd ι g.2.2)⟩
  have he : Function.Injective e := by
    intro g h hgh
    have hr : (g.1.map ι).roots = (h.1.map ι).roots := congrArg Subtype.val hgh
    apply Subtype.ext
    apply Polynomial.map_injective ι ι.injective
    rw [(IsAlgClosed.splits (g.1.map ι)).eq_prod_roots_of_monic (g.2.1.map ι),
      (IsAlgClosed.splits (h.1.map ι)).eq_prod_roots_of_monic (h.2.1.map ι), hr]
  calc
    Nat.card {g : K[X] // g.Monic ∧ g ∣ f} ≤ Nat.card ↥P :=
      Nat.card_le_card_of_injective e he
    _ = P.card := by simp
    _ ≤ (f.map ι).roots.powerset.card := Multiset.toFinset_card_le _
    _ = 2 ^ (f.map ι).roots.card := Multiset.card_powerset _
    _ ≤ 2 ^ f.natDegree :=
      Nat.pow_le_pow_right (by omega) (Polynomial.card_roots_map_le_natDegree _)

/-- The number of actual intermediate fields depends only on the extension
degree, without a chosen normal closure or Galois-group estimate. -/
theorem intermediateField_card_le_two_pow_finrank
    (F E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E] :
    Nat.card (IntermediateField F E) ≤ 2 ^ Module.finrank F E := by
  classical
  obtain ⟨α, hα⟩ := Field.exists_primitive_element F E
  let f : E[X] := (minpoly F α).map (algebraMap F E)
  let G := {g : E[X] // g.Monic ∧ g ∣ f}
  let : Fintype G := fintypeSubtypeMonicDvd f
    (Polynomial.map_ne_zero (minpoly.ne_zero_of_finite F α))
  let g : IntermediateField F E → G := fun K =>
    ⟨(minpoly K α).map (algebraMap K E), (minpoly.monic (.of_finite K α)).map _, by
      convert Polynomial.map_dvd (algebraMap K E) (minpoly.dvd_map_of_isScalarTower F K α)
      rw [Polynomial.map_map]
      rfl⟩
  have hg : Function.Injective g := by
    intro K K' heq
    have heq' := congrArg Subtype.val heq
    dsimp [g] at heq'
    apply_fun fun p : E[X] => adjoin F (p.coeffs : Set E) at heq'
    simpa only [adjoin_minpoly_coeff_of_exists_primitive_element F hα] using heq'
  have hdeg : f.natDegree = Module.finrank F E := by
    rw [Polynomial.natDegree_map]
    exact (Field.primitive_element_iff_minpoly_natDegree_eq F α).mp hα
  exact (Nat.card_le_card_of_injective g hg).trans
    (hdeg ▸ monic_divisors_card_le_two_pow_natDegree f
      (Polynomial.map_ne_zero (minpoly.ne_zero_of_finite F α)))

end
end AffineCurveCounting
