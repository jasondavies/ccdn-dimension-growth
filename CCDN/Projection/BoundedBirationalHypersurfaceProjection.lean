/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Projection.BoundedIntegerNormalization
public import CCDN.Algebra.PolynomialPredicates
import CCDN.Height.LinearParameterPrimitive
import CCDN.Hilbert.HilbertLinearCoordinates
import CCDN.Hilbert.PrincipalHilbertPolynomial
import CCDN.Projection.HilbertProjectionDegree
import CCDN.Projection.HomogeneousFiniteProjectionDegree
import CCDN.Projection.HomogeneousProjectionEquation
/-! A bounded integer linear finite birational projection of a
homogeneous prime quotient to a hypersurface of exactly the same degree. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

def integerBirationalProjectionHeight (n d : ℕ) : ℕ :=
  max (integerNormalizationHeight n d) ((n * d ^ 2 + 1) ^ n)

/-- A bounded primitive augmentation of the constructed normalization
produces a homogeneous irreducible equation of exactly the original degree. -/
theorem exists_bounded_birational_hypersurface_projection
    (m k : ℕ) (I : Ideal (MvPolynomial (Fin (m + 1 + k)) ℚ)) [I.IsPrime]
    (hI : IsHomogeneousIdeal I)
    (d : ℕ) (hdimdeg : HasProjectiveDimensionDegree I m d) :
    ∃ b : Fin (m + 2) → Fin (m + 1 + k) → ℤ,
      (∀ i j, |b i j| ≤ integerBirationalProjectionHeight (m + 1 + k) d) ∧
      (projectionCoordinateMap I
        (fun i : Fin (m + 1) => integerLinearForm (b i.succ))).IsIntegral ∧
      Function.Injective (projectionCoordinateMap I
        (fun i : Fin (m + 1) => integerLinearForm (b i.succ))) ∧
      (projectionCoordinateMap I (fun i => integerLinearForm (b i))).IsIntegral ∧
      IntermediateField.adjoin ℚ
        (Set.range (fun i => algebraMap (MvPolynomial (Fin (m + 1 + k)) ℚ ⧸ I)
          (FractionRing (MvPolynomial (Fin (m + 1 + k)) ℚ ⧸ I))
          ((Ideal.Quotient.mk I) (integerLinearForm (b i))))) = ⊤ ∧
      ∃ f : MvPolynomial (Fin (m + 2)) ℚ,
        Irreducible f ∧ f.IsHomogeneous d ∧ f.totalDegree = d ∧
        RingHom.ker (projectionCoordinateMap I (fun i => integerLinearForm (b i))) =
          Ideal.span {f} := by
  classical
  obtain ⟨hdim, hdegree⟩ := hdimdeg
  let n := m + 1 + k
  let A := MvPolynomial (Fin n) ℚ ⧸ I
  let F := FractionRing A
  obtain ⟨a, ha, hinta, hinja⟩ :=
    exists_bounded_integer_normalization m k I d ⟨hdim, hdegree⟩
  let l : Fin (m + 1) → MvPolynomial (Fin n) ℚ := fun i => integerLinearForm (a i)
  obtain ⟨t, ht, hfield⟩ := exists_bounded_linear_parameter_primitive (F := F)
    I l (fun i => integerLinearForm_degree (a i)) hinja d ⟨hdim, hdegree⟩
  let b : Fin (m + 2) → Fin n → ℤ :=
    Fin.cases (fun j => (t : ℤ) ^ j.val) a
  let l' : Fin (m + 2) → MvPolynomial (Fin n) ℚ := fun i => integerLinearForm (b i)
  have hl' : l' = Fin.cases (momentCoordinate ℚ n t) l := by
    funext i
    refine Fin.cases ?_ (fun _ => rfl) i
    simp only [l', b, Fin.cases_zero, integerLinearForm, momentCoordinate, Int.cast_pow,
      Int.cast_natCast]
  have hfield' : IntermediateField.adjoin ℚ
      (Set.range (fun i => algebraMap A F ((Ideal.Quotient.mk I) (l' i)))) = ⊤ := by
    rwa [hl']
  let ψ := projectionCoordinateMap I l'
  have heq : ψ.comp (rename Fin.succ) = projectionCoordinateMap I l := by
    ext i
    simp only [AlgHom.comp_apply, rename_X, projectionCoordinateMap, aeval_X,
      Ideal.Quotient.mkₐ_eq_mk]
    change (Ideal.Quotient.mk I) (aeval l' (X i.succ)) = (Ideal.Quotient.mk I) (l i)
    rw [aeval_X]
    rfl
  have hint : ψ.IsIntegral := by
    apply RingHom.IsIntegral.tower_top (rename Fin.succ).toRingHom ψ.toRingHom
    change (ψ.comp (rename Fin.succ)).IsIntegral
    rwa [heq]
  have hAI : AlgebraicIndependent ℚ (fun i : Fin (m + 1) => ψ (X i.succ)) := by
    have hi : AlgebraicIndependent ℚ (fun i => (Ideal.Quotient.mk I) (l i)) := by
      change Function.Injective (aeval (fun i => (Ideal.Quotient.mk I) (l i)))
      rw [← projectionCoordinateMap_eq_aeval]
      exact hinja
    convert hi using 1
    funext i
    change (Ideal.Quotient.mk I) (aeval l' (X i.succ)) = (Ideal.Quotient.mk I) (l i)
    rw [aeval_X]
    rfl
  obtain ⟨f, hf, hfpos, _, hker⟩ := exists_hypersurface_projection_equation_degree_le
    I l' (fun i => integerLinearForm_degree (b i)) d ⟨hdim, hdegree⟩
    (fun i => X i.succ) (fun _ => by simp) hAI
  have hlhom (i) : (l' i).IsHomogeneous 1 := integerLinearForm_isHomogeneous (b i)
  have hlead := homogeneous_finite_birational_projection_leadingCoeff_eq
    (F := F) I hI l' hlhom hint hfield'
  rw [hker, principal_filteredHilbertPolynomial_leadingCoeff f hf.ne_zero hfpos,
    hdegree] at hlead
  have hfdeg : f.totalDegree = d := by
    have hh := (div_left_inj' (by positivity : ((m + 1).factorial : ℚ) ≠ 0)).mp hlead
    exact_mod_cast hh
  have hfhom : f.IsHomogeneous d := by
    rw [← hfdeg]
    exact homogeneous_projection_equation I hI l' hlhom f hf.ne_zero hker
  refine ⟨b, ?_, hinta, hinja, hint, hfield', f, hf, hfhom, hfdeg, hker⟩
  intro i j
  refine Fin.cases ?_ (fun s => ?_) i
  · change |(t : ℤ) ^ j.val| ≤ _
    rw [abs_pow, abs_of_nonneg (Nat.cast_nonneg t)]
    have hp : t ^ j.val ≤ (n * d ^ 2 + 1) ^ n := by
      calc
        _ ≤ (n * d ^ 2 + 1) ^ j.val :=
          Nat.pow_le_pow_left (ht.trans (Nat.le_succ _)) _
        _ ≤ _ := Nat.pow_le_pow_right (by omega) (Nat.le_of_lt j.isLt)
    exact_mod_cast hp.trans (le_max_right (integerNormalizationHeight n d) _)
  · exact (ha s j).trans (by
      exact_mod_cast le_max_left (integerNormalizationHeight n d) ((n * d ^ 2 + 1) ^ n))

/-- The same construction without fixing an additive presentation of the
ambient number of variables. -/
theorem exists_bounded_birational_hypersurface_projection_of_le
    (m n : ℕ) (hmn : m + 1 ≤ n)
    (I : Ideal (MvPolynomial (Fin n) ℚ)) [I.IsPrime]
    (hI : IsHomogeneousIdeal I)
    (d : ℕ) (hdimdeg : HasProjectiveDimensionDegree I m d) :
    ∃ b : Fin (m + 2) → Fin n → ℤ,
      (∀ i j, |b i j| ≤ integerBirationalProjectionHeight n d) ∧
      (projectionCoordinateMap I
        (fun i : Fin (m + 1) => integerLinearForm (b i.succ))).IsIntegral ∧
      Function.Injective (projectionCoordinateMap I
        (fun i : Fin (m + 1) => integerLinearForm (b i.succ))) ∧
      (projectionCoordinateMap I (fun i => integerLinearForm (b i))).IsIntegral ∧
      IntermediateField.adjoin ℚ
        (Set.range (fun i => algebraMap (MvPolynomial (Fin n) ℚ ⧸ I)
          (FractionRing (MvPolynomial (Fin n) ℚ ⧸ I))
          ((Ideal.Quotient.mk I) (integerLinearForm (b i))))) = ⊤ ∧
      ∃ f : MvPolynomial (Fin (m + 2)) ℚ,
        Irreducible f ∧ f.IsHomogeneous d ∧ f.totalDegree = d ∧
        RingHom.ker (projectionCoordinateMap I (fun i => integerLinearForm (b i))) =
          Ideal.span {f} := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  exact exists_bounded_birational_hypersurface_projection m k I hI d hdimdeg

section

/-! The constructed projection has a coefficient bound polynomial in
the degree, with exponent and constant depending only on ambient
dimension. -/

def birationalProjectionHeightConstant (n : ℕ) : ℕ :=
  n.factorial * 2 ^ n + (n + 1) ^ n

lemma birationalProjectionHeightConstant_pos (n : ℕ) :
    0 < birationalProjectionHeightConstant n := by
  dsimp [birationalProjectionHeightConstant]
  positivity

theorem integerBirationalProjectionHeight_le (n d : ℕ) (hd : 1 ≤ d) :
    integerBirationalProjectionHeight n d ≤
      birationalProjectionHeightConstant n * d ^ (2 * n) := by
  have hpow : 1 ≤ d ^ 2 := Nat.one_le_pow _ _ hd
  have hfirst : integerNormalizationHeight n d ≤
      (n.factorial * 2 ^ n) * d ^ (2 * n) := by
    dsimp only [integerNormalizationHeight]
    calc
      _ ≤ n.factorial * (2 * d) ^ n :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
      _ = (n.factorial * 2 ^ n) * d ^ n := by rw [Nat.mul_pow, Nat.mul_assoc]
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hd (by omega))
  have hsecond : (n * d ^ 2 + 1) ^ n ≤ (n + 1) ^ n * d ^ (2 * n) := by
    calc
      _ ≤ ((n + 1) * d ^ 2) ^ n :=
        Nat.pow_le_pow_left (by nlinarith) _
      _ = _ := by rw [Nat.mul_pow, ← pow_mul]
  apply max_le
  · exact hfirst.trans (Nat.mul_le_mul_right _ (Nat.le_add_right _ _))
  · exact hsecond.trans (Nat.mul_le_mul_right _ (Nat.le_add_left _ _))

end

end
end CCDN
