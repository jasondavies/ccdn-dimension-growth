module

public import CCDN.AffineChartPositionedAuxiliary
public import CCDN.HypersurfaceAbsoluteAuxiliary
public import CCDN.AffineTranslation

/-! Coefficient-sensitive auxiliary equations with affine-chart good primes.
The positioning transformation fixes the homogenizing coordinate, so the
literal affine good-prime condition survives the coordinate change. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The affine-chart version of the absolutely irreducible auxiliary theorem.
The constant depends only on the dimension. The excluded-prime set must satisfy the
displayed good-reduction and unit-chart conditions. -/
theorem affine_chart_absolute_auxiliary_degree
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] {n d t : ℕ}
    (f : MvPolynomial (Fin (n + 3)) ℤ) (hf : f.IsHomogeneous d) (hd : 0 < d)
    (hir : Irreducible (map (Int.castRingHom K) f))
    (z : Fin t → IntPoint (n + 3)) (hprim : ∀ i, Finset.univ.gcd (z i) = 1)
    (hz : ∀ i, eval (z i) f = 0)
    (bad : Finset ℕ)
    (hgood : ∀ (p : ℕ) [Fact p.Prime], p ∉ bad → 27 * (d : ℝ) ^ 4 < p →
      Irreducible (map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))
        (map (Int.castRingHom (ZMod p)) (affineChart (n + 2) f))) ∧
      ∀ i, IsCoprime (p : ℤ) (z i 0))
    {B : ℝ} (hB : 1 ≤ B) (hbox : ∀ i j, |(z i j : ℝ)| ≤ B) :
    ∃ M : ℕ,
      (M : ℝ) ≤ hypersurfaceAbsoluteAuxiliaryConstant n *
        ((d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) * Real.exp (∑ p ∈ bad, Real.log p / p) *
            B ^ ((n + 2 : ℝ) / ((n + 1 : ℝ) * (d : ℝ) ^ (1 / (n + 1 : ℝ)))) /
              (integerCoefficientHeight f : ℝ) ^ (1 / ((n + 1 : ℝ) * d * (d : ℝ) ^ (1 / (n + 1 : ℝ)))) +
          (d : ℝ) ^ (1 - 1 / (n + 1 : ℝ)) * Real.log B + (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ))) ∧
      ∃ g : MvPolynomial (Fin (n + 3)) ℤ, g ≠ 0 ∧ g.IsHomogeneous M ∧
        (∀ i, eval (z i) g = 0) ∧ ¬ f ∣ g := by
  have hf0 : f ≠ 0 := by intro h; exact hir.ne_zero (by rw [h, map_zero])
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hnR : (n : ℝ) + 1 + 1 = n + 2 := by ring
  obtain ⟨a, H, ha, hH, hcf, hcg, hpos⟩ := exists_hypersurface_coefficient_position
    (r := n + 1) (by omega) hd f hf hf0
  let model := homogeneousTranslation ℤ a f
  have hmhom : model.IsHomogeneous d := homogeneousTranslation_homogeneous a hf
  have hmir : Irreducible (map (Int.castRingHom K) model) := by
    dsimp only [model]
    rw [homogeneousTranslation_map]
    exact (MulEquiv.irreducible_iff (f := homogeneousTranslation K ((Int.castRingHom K) ∘ a))).mpr hir
  let w := fun i => homogeneousPointTranslation (-a) (z i)
  have hwp : ∀ i, Finset.univ.gcd (w i) = 1 := by
    intro i
    exact (homogeneousPointTranslation_gcd (-a) (z i)).trans (hprim i)
  have hwz : ∀ i, eval (w i) model = 0 := by
    intro i
    rw [homogeneousTranslation_eval]
    change eval (homogeneousPointTranslation a (homogeneousPointTranslation (-a) (z i))) f = 0
    have he := homogeneousPointTranslation_inverse (-a) (z i)
    simp only [neg_neg] at he
    rw [he, hz i]
  let R := ((d : ℝ) + 1) * B
  have hR : 1 ≤ R := one_le_mul_of_one_le_of_one_le (by linarith) hB
  have hwbox : ∀ i j, |(w i j : ℝ)| ≤ R :=
    fun i j => homogeneousPointTranslation_box hB a ha (z i) (hbox i) j
  have hposition : Real.log H ≤ Real.log |((MonomialOrder.lex.leadingCoeff model : ℤ) : ℝ)| +
      hypersurfaceAuxiliaryPositionConstant n * d * (d : ℝ) ^ (1 / (n + 1 : ℝ)) := by
    simpa only [hypersurfaceAuxiliaryPositionConstant, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, hnR]
      using hpos
  have hmodelgood : ∀ (p : ℕ) [Fact p.Prime], p ∉ bad → 27 * (d : ℝ) ^ 4 < p →
      Irreducible (map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))
        (map (Int.castRingHom (ZMod p)) (affineChart (n + 2) model))) ∧
      ∀ i, IsCoprime (p : ℤ) (w i 0) := by
    intro p hp hpnot hcut
    obtain ⟨hi, hu⟩ := hgood p hpnot hcut
    constructor
    · simpa only [model, affineChart_homogeneousTranslation, affineTranslation_map,
        affineTranslation_irreducible_iff] using hi
    · simpa only [w, homogeneousPointTranslation, Fin.cons_zero] using hu
  obtain ⟨M, hbound, g, hg0, hgh, hgz, hgnd⟩ := affine_chart_positioned_auxiliary_degree
    MonomialOrder.lex model hmhom hd hmir H hH hcg w hwp hwz bad hmodelgood hR hwbox
    (hypersurfaceAuxiliaryPositionConstant n)
    (by unfold hypersurfaceAuxiliaryPositionConstant; positivity) hposition
  refine ⟨M, ?_, ?_⟩
  · let h := (integerCoefficientHeight f : ℝ)
    have hh0 : 0 < h := by dsimp only [h]; exact_mod_cast integerCoefficientHeight_pos f hf0
    have hhH : h ≤ H := integerCoefficientHeight_le f (by linarith) hcf
    let D := (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ))
    let b := Real.exp (∑ p ∈ bad, Real.log p / p)
    let α := (n + 2 : ℝ) / ((n + 1 : ℝ) * (d : ℝ) ^ (1 / (n + 1 : ℝ)))
    let q := 1 / ((n + 1 : ℝ) * d * (d : ℝ) ^ (1 / (n + 1 : ℝ)))
    let Q := D * b * B ^ α / h ^ q
    let l := (d : ℝ) ^ (1 - 1 / (n + 1 : ℝ)) * Real.log B
    let E := Real.exp ((n + 2 : ℝ) ^ 2 / (n + 1 : ℝ))
    let C := hypersurfacePositionedAuxiliaryConstant n (hypersurfaceAuxiliaryPositionConstant n)
    have hD : 0 ≤ D := by dsimp [D]; positivity
    have hb : 0 ≤ b := (Real.exp_pos _).le
    have hQ : 0 ≤ Q := by dsimp [Q]; positivity
    have hl : 0 ≤ l := mul_nonneg (Real.rpow_nonneg hd0.le _) (Real.log_nonneg hB)
    have hE : 0 ≤ E := (Real.exp_pos _).le
    have hC : 0 ≤ C := by dsimp [C, hypersurfacePositionedAuxiliaryConstant]; positivity
    have hfactor : ((d : ℝ) + 1) ^ α ≤ E := by
      simpa only [α, E, Nat.cast_add, Nat.cast_one, hnR] using
        auxiliary_box_rpow_factor (r := n + 1) (by omega) hd
    have hRpow : R ^ α ≤ E * B ^ α := by
      rw [show R = ((d : ℝ) + 1) * B from rfl, Real.mul_rpow (by positivity) (by linarith)]
      exact mul_le_mul_of_nonneg_right hfactor (Real.rpow_nonneg (by linarith) _)
    have hQ' : D * b * R ^ α / H ^ q ≤ E * Q := by
      calc
        _ ≤ D * b * R ^ α / h ^ q := div_le_div_of_nonneg_left (by positivity)
          (by positivity) (Real.rpow_le_rpow hh0.le hhH (by dsimp [q]; positivity))
        _ ≤ D * b * (E * B ^ α) / h ^ q :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hRpow (mul_nonneg hD hb)) (by positivity)
        _ = _ := by dsimp [Q]; ring
    have hlogcost : (d : ℝ) ^ (1 - 1 / (n + 1 : ℝ)) * Real.log ((d : ℝ) + 1) ≤ (n + 2 : ℝ) * d := by
      simpa only [Nat.cast_add, Nat.cast_one, hnR] using auxiliary_box_log_cost (r := n + 1) (by omega) hd
    have hexp : (1 : ℝ) ≤ 4 - 1 / (n + 1 : ℝ) := by
      have hh := (div_le_one (by positivity : (0 : ℝ) < n + 1)).mpr
        (show 1 ≤ (n + 1 : ℝ) by linarith)
      linarith
    have hdD : (d : ℝ) ≤ D := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hd1 hexp
    have hl' : (d : ℝ) ^ (1 - 1 / (n + 1 : ℝ)) * Real.log R ≤ l + (n + 2 : ℝ) * D := by
      dsimp only [R, l]
      rw [Real.log_mul (by positivity) (by linarith), mul_add]
      have hh := mul_le_mul_of_nonneg_left hdD (show 0 ≤ (n + 2 : ℝ) by positivity)
      linarith
    have htotal : D * b * R ^ α / H ^ q +
        (d : ℝ) ^ (1 - 1 / (n + 1 : ℝ)) * Real.log R + D ≤
        (E + (n + 3 : ℝ)) * (Q + l + D) := by
      have h1 := mul_nonneg (show 0 ≤ (n + 3 : ℝ) by positivity) hQ
      have h2 := mul_nonneg (show 0 ≤ E + (n + 2 : ℝ) by positivity) hl
      have h3 := mul_nonneg hE hD
      nlinarith
    change (M : ℝ) ≤ C * (D * b * R ^ α / H ^ q + _ + D) at hbound
    change (M : ℝ) ≤ (C * (E + (n + 3 : ℝ))) * (Q + l + D)
    exact hbound.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left htotal hC)
  · refine ⟨homogeneousTranslation ℤ (-a) g, ?_, homogeneousTranslation_homogeneous (-a) hgh, ?_, ?_⟩
    · exact (homogeneousTranslation ℤ (-a)).injective.ne (by simpa using hg0)
    · intro i
      rw [homogeneousTranslation_eval]
      exact hgz i
    · intro hdvd
      apply hgnd
      have hh := map_dvd (homogeneousTranslation ℤ a).toRingHom hdvd
      change model ∣ homogeneousTranslation ℤ a (homogeneousTranslation ℤ (-a) g) at hh
      have he : homogeneousTranslation ℤ a (homogeneousTranslation ℤ (-a) g) = g :=
        (homogeneousTranslation ℤ a).apply_symm_apply g
      rwa [he] at hh

end
end CCDN
