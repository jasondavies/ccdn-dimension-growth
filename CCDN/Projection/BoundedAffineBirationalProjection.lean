/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Projection.BoundedBirationalHypersurfaceProjection
import CCDN.Height.LinearParameterPrimitive
import CCDN.Hilbert.HilbertLinearCoordinates
import CCDN.Projection.HilbertProjectionDegree
/-! A bounded finite birational affine projection constructed from a
normalization that remains finite at infinity. The degree-preservation step
is supplied separately by comparison of the projective closures. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

theorem exists_bounded_affine_birational_projection
    (m k : ℕ) (I : Ideal (MvPolynomial (Fin (m + 1 + k)) ℚ)) [I.IsPrime]
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
      (projectionCoordinateMap (projectiveClosureIdeal I)
        (closureProjectionCoordinates (fun i => integerLinearForm (b i)))).IsIntegral ∧
      ∃ f : MvPolynomial (Fin (m + 2)) ℚ,
        Irreducible f ∧ 0 < f.totalDegree ∧ f.totalDegree ≤ d ∧
        RingHom.ker (projectionCoordinateMap I (fun i => integerLinearForm (b i))) =
          Ideal.span {f} := by
  classical
  let n := m + 1 + k
  let A := MvPolynomial (Fin n) ℚ ⧸ I
  let F := FractionRing A
  obtain ⟨a, ha, hinta, hinja, hcone⟩ :=
    exists_bounded_integer_closure_normalization m k I d hdimdeg
  let l : Fin (m + 1) → MvPolynomial (Fin n) ℚ := fun i => integerLinearForm (a i)
  obtain ⟨t, ht, hfield⟩ := exists_bounded_linear_parameter_primitive (F := F)
    I l (fun i => linearForm_totalDegree_le _) hinja d hdimdeg
  let b : Fin (m + 2) → Fin n → ℤ :=
    Fin.cases (fun j => (t : ℤ) ^ j.val) a
  let l' : Fin (m + 2) → MvPolynomial (Fin n) ℚ := fun i => integerLinearForm (b i)
  have hl' : l' = Fin.cases (momentCoordinate ℚ n t) l := by
    funext i
    refine Fin.cases ?_ (fun _ => rfl) i
    simp only [l', b, Fin.cases_zero, integerLinearForm, linearForm, momentCoordinate, Int.cast_pow,
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
  obtain ⟨f, hf, hfpos, hfd, hker⟩ := exists_hypersurface_projection_equation_degree_le
    I l' (fun i => linearForm_totalDegree_le _) d hdimdeg
    (fun i => X i.succ) (fun _ => by simp) hAI
  have hcone' : (projectionCoordinateMap (projectiveClosureIdeal I)
      (closureProjectionCoordinates l')).IsIntegral := by
    let ι : Fin (m + 2) → Fin (m + 3) := Fin.cases 0 (fun i => i.succ.succ)
    let ψcone := projectionCoordinateMap (projectiveClosureIdeal I)
      (closureProjectionCoordinates l')
    have heqcone : ψcone.comp (rename ι) =
        projectionCoordinateMap (projectiveClosureIdeal I) (closureProjectionCoordinates l) := by
      ext i
      refine Fin.cases ?_ (fun j => ?_) i <;>
        simp [ψcone, projectionCoordinateMap, closureProjectionCoordinates, ι, l', b, l]
    apply RingHom.IsIntegral.tower_top (rename ι).toRingHom ψcone.toRingHom
    change (ψcone.comp (rename ι)).IsIntegral
    rwa [heqcone]
  refine ⟨b, ?_, hinta, hinja, hint, hfield', hcone', f, hf, hfpos, hfd, hker⟩
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

end
end CCDN
