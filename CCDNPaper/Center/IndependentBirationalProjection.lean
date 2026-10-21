/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Projection.BoundedBirationalHypersurfaceProjection
import CCDN.Projection.LeadingCoordinateExtension
import CCDNPaper.Center.IndependentProjectionRows

/-! The bounded homogeneous birational projection can always be chosen
with independent ambient rows, including degree one. If its primitive row
is redundant, the normalization rows already generate the function field;
a standard unit row outside their span replaces it at no height cost. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Replacing the first row of an integer matrix by the `j`-th standard unit row gives
linearly independent rows when the remaining rows are independent and the unit row lies
outside their span. -/
private theorem unit_row_cons_linearIndependent {m n : ℕ} (b : Fin (m + 1) → Fin n → ℤ) (j : Fin n)
    (htail : LinearIndependent ℚ (fun i => fun k => (b i k : ℚ)))
    (hj : (fun k => if k = j then (1 : ℚ) else 0) ∉
      Submodule.span ℚ (Set.range (fun i => fun k => (b i k : ℚ)))) :
    LinearIndependent ℚ (fun i => fun k =>
      ((Fin.cases (fun k => if k = j then 1 else 0) b : Fin (m + 2) → Fin n → ℤ) i k : ℚ)) := by
  have hrows : (fun i => fun k =>
      ((Fin.cases (fun k => if k = j then 1 else 0) b : Fin (m + 2) → Fin n → ℤ) i k : ℚ)) =
      Fin.cons (fun k => if k = j then (1 : ℚ) else 0) (fun i => fun k => (b i k : ℚ)) := by
    funext i
    refine Fin.cases ?_ (fun _ => rfl) i
    funext k
    simp only [Fin.cases_zero, Fin.cons_zero]
    split_ifs <;> norm_num
  rw [hrows]
  exact htail.finCons hj

/-- Replacing the first row of an integer matrix by a standard unit row keeps every entry
within any bound `H ≥ 1` satisfied by the remaining rows. -/
private theorem unit_row_cons_abs_le {m n : ℕ} {H : ℤ} (hH : 1 ≤ H) (b : Fin (m + 1) → Fin n → ℤ)
    (hb : ∀ i k, |b i k| ≤ H) (j : Fin n) (i : Fin (m + 2)) (k : Fin n) :
    |(Fin.cases (fun k => if k = j then 1 else 0) b : Fin (m + 2) → Fin n → ℤ) i k| ≤ H := by
  refine Fin.cases ?_ (fun s => hb s k) i
  change |if k = j then (1 : ℤ) else 0| ≤ _
  split_ifs
  · simpa using hH
  · simpa using zero_le_one.trans hH

/-- If the first row of `b` lies in the span of the remaining rows, then any `c` with the same
remaining rows generates the same function field: when the linear forms of `b` generate the
function field of `I`, so do those of `c`. -/
private theorem adjoin_integerLinearForm_eq_top_of_first_mem_span {m n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) ℚ)) [I.IsPrime] (b c : Fin (m + 2) → Fin n → ℤ)
    (hbc : ∀ i : Fin (m + 1), c i.succ = b i.succ)
    (hdep : (fun j => (b 0 j : ℚ)) ∈ Submodule.span ℚ
      (Set.range (fun i : Fin (m + 1) => fun j => (b i.succ j : ℚ))))
    (hfield : IntermediateField.adjoin ℚ
      (Set.range (fun i => algebraMap (MvPolynomial (Fin n) ℚ ⧸ I)
        (FractionRing (MvPolynomial (Fin n) ℚ ⧸ I))
        ((Ideal.Quotient.mk I) (integerLinearForm (b i))))) = ⊤) :
    IntermediateField.adjoin ℚ
      (Set.range (fun i => algebraMap (MvPolynomial (Fin n) ℚ ⧸ I)
        (FractionRing (MvPolynomial (Fin n) ℚ ⧸ I))
        ((Ideal.Quotient.mk I) (integerLinearForm (c i))))) = ⊤ := by
  let A := MvPolynomial (Fin n) ℚ ⧸ I
  let F := FractionRing A
  let L : (Fin n → ℚ) →ₗ[ℚ] F :=
    (IsScalarTower.toAlgHom ℚ A F).toLinearMap.comp
      ((Ideal.Quotient.mkₐ ℚ I).toLinearMap.comp (linearFormLinearMap ℚ (Fin n)))
  have hL (v : Fin n → ℤ) : L (fun k => (v k : ℚ)) =
      algebraMap A F ((Ideal.Quotient.mk I) (integerLinearForm v)) := rfl
  have hfieldtail : IntermediateField.adjoin ℚ
      (Set.range (fun i : Fin (m + 1) => algebraMap A F
        ((Ideal.Quotient.mk I) (integerLinearForm (b i.succ))))) = ⊤ := by
    have he := adjoin_linear_images_eq_tail_of_first_mem_span
      (fun i => fun k => (b i k : ℚ)) L hdep
    simp only [hL] at he
    rw [← he]
    exact hfield
  apply top_unique
  rw [← hfieldtail]
  apply IntermediateField.adjoin_le_iff.mpr
  rintro _ ⟨i, rfl⟩
  refine IntermediateField.subset_adjoin ℚ _ ⟨i.succ, ?_⟩
  simp only [hbc i]
  rfl

/-- The bounded finite birational hypersurface projection, with
full row rank in every degree whenever the ambient vector dimension allows
m+2 independent rows. It keeps the row height bound, the finite normalization,
birationality and the irreducible degree-d equation. -/
theorem exists_independent_bounded_birational_hypersurface_projection
    (m n : ℕ) (hmn : m + 2 ≤ n)
    (I : Ideal (MvPolynomial (Fin n) ℚ)) [I.IsPrime]
    (hI : IsHomogeneousIdeal I)
    (d : ℕ) (hdimdeg : HasProjectiveDimensionDegree I m d) :
    ∃ (b : Fin (m + 2) → Fin n → ℤ) (f : MvPolynomial (Fin (m + 2)) ℚ),
      (∀ i j, |b i j| ≤ integerBirationalProjectionHeight n d) ∧
      LinearIndependent ℚ (fun i => fun j => (b i j : ℚ)) ∧
      IsNoetherNormalization I (fun i : Fin (m + 1) => integerLinearForm (b i.succ)) ∧
      IsBirationalProjection I (fun i => integerLinearForm (b i)) f ∧
      f.IsHomogeneous d ∧ f.totalDegree = d := by
  classical
  obtain ⟨b, f, hb, hN, hP, hfhom, hfdeg⟩ :=
    exists_bounded_birational_hypersurface_projection_of_le m n (by omega) I hI d hdimdeg
  by_cases hli : LinearIndependent ℚ (fun i => fun j => (b i j : ℚ))
  · exact ⟨b, f, hb, hli, hN, hP, hfhom, hfdeg⟩
  have htail : LinearIndependent ℚ
      (fun i : Fin (m + 1) => fun j => (b i.succ j : ℚ)) :=
    integer_rows_linearIndependent_of_projection_injective I (fun i => b i.succ) hN.injective
  have hdep : (fun j => (b 0 j : ℚ)) ∈ Submodule.span ℚ
      (Set.range (fun i : Fin (m + 1) => fun j => (b i.succ j : ℚ))) := by
    by_contra hn
    exact hli (linearIndependent_finSucc.mpr ⟨htail, hn⟩)
  obtain ⟨j, hj⟩ := exists_standard_row_not_mem_span _ htail (by omega)
  let c : Fin (m + 2) → Fin n → ℤ :=
    Fin.cases (fun k => if k = j then 1 else 0) (fun i => b i.succ)
  have hfieldc := adjoin_integerLinearForm_eq_top_of_first_mem_span I b c (fun _ => rfl) hdep
    hP.birational
  obtain ⟨g, hg, hghom, hgdeg, _, hkg⟩ := exists_homogeneous_extended_projection_equation
    (F := FractionRing (MvPolynomial (Fin n) ℚ ⧸ I)) I hI
    (fun i => integerLinearForm (c i)) (fun i => linearForm_isHomogeneous _)
    hN.integral hN.injective hfieldc d hdimdeg
  exact ⟨c, g, unit_row_cons_abs_le
      (by exact_mod_cast integerBirationalProjectionHeight_one_le n d) _ (fun s => hb s.succ) j,
    unit_row_cons_linearIndependent _ j htail hj, hN,
    ⟨⟨hfieldc, hg, hkg⟩, projectionCoordinateMap_isIntegral_of_tail I _ hN.integral⟩, hghom,
    hgdeg⟩

end
end CCDN
