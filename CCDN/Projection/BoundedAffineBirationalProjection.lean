/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Projection.BoundedBirationalHypersurfaceProjection
import CCDN.Projection.LinearParameterPrimitive
import CCDN.Projection.LeadingCoordinateExtension
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
    ∃ (b : Fin (m + 2) → Fin (m + 1 + k) → ℤ) (f : MvPolynomial (Fin (m + 2)) ℚ),
      (∀ i j, |b i j| ≤ integerBirationalProjectionHeight (m + 1 + k) d) ∧
      IsNoetherNormalization I (fun i : Fin (m + 1) => integerLinearForm (b i.succ)) ∧
      IsBirationalProjection I (fun i => integerLinearForm (b i)) f ∧
      (projectionCoordinateMap (projectiveClosureIdeal I)
        (closureProjectionCoordinates (fun i => integerLinearForm (b i)))).IsIntegral ∧
      0 < f.totalDegree ∧ f.totalDegree ≤ d := by
  classical
  let n := m + 1 + k
  let F := FractionRing (MvPolynomial (Fin n) ℚ ⧸ I)
  obtain ⟨a, ha, hinta, hinja, hcone⟩ :=
    exists_bounded_integer_closure_normalization m k I d hdimdeg
  let l : Fin (m + 1) → MvPolynomial (Fin n) ℚ := fun i => integerLinearForm (a i)
  obtain ⟨t, ht, hfield⟩ := exists_bounded_linear_parameter_primitive (F := F)
    I l (fun i => linearForm_totalDegree_le _) hinja d hdimdeg
  let b : Fin (m + 2) → Fin n → ℤ := Fin.cases (fun j => (t : ℤ) ^ j.val) a
  let l' : Fin (m + 2) → MvPolynomial (Fin n) ℚ := fun i => integerLinearForm (b i)
  have hfield' : IntermediateField.adjoin ℚ (Set.range (fun i =>
      algebraMap _ F ((Ideal.Quotient.mk I) (l' i)))) = ⊤ := by
    have hl : l' = Fin.cases (momentCoordinate ℚ n t) (fun i => integerLinearForm (a i)) :=
      integerLinearForm_moment_cons t a
    rwa [hl]
  obtain ⟨f, hf, hfpos, hfd, hker⟩ := exists_extended_projection_equation_degree_le
    I l' (fun i => linearForm_totalDegree_le _) hinja d hdimdeg
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
  exact ⟨b, f, moment_cons_abs_le_integerBirationalProjectionHeight ht a ha, ⟨hinta, hinja⟩,
    ⟨⟨hfield', hf, hker⟩, projectionCoordinateMap_isIntegral_of_tail I l' hinta⟩, hcone', hfpos,
    hfd⟩

end
end CCDN
