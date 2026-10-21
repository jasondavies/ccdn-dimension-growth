module

public import CCDN.Center.IndependentProjectionRows
public import CCDN.Algebra.PolynomialPredicates
/-! The bounded homogeneous birational projection can always be chosen
with independent ambient rows, including degree one. If its primitive row
is redundant, the normalization rows already generate the function field;
a standard unit row outside their span replaces it at no height cost. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The bounded finite birational hypersurface projection, with
full row rank in every degree whenever the ambient vector dimension allows
m+2 independent rows. It keeps the row height bound, the finite normalization,
birationality and the irreducible degree-d equation. -/
theorem exists_independent_bounded_birational_hypersurface_projection
    (m n : ℕ) (hmn : m + 2 ≤ n)
    (I : Ideal (MvPolynomial (Fin n) ℚ)) [I.IsPrime]
    (hI : IsHomogeneousIdeal I)
    (d : ℕ) (hdimdeg : HasProjectiveDimensionDegree I m d) :
    ∃ b : Fin (m + 2) → Fin n → ℤ,
      (∀ i j, |b i j| ≤ integerBirationalProjectionHeight n d) ∧
      LinearIndependent ℚ (fun i => fun j => (b i j : ℚ)) ∧
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
  classical
  obtain ⟨hdim, hdegree⟩ := hdimdeg
  obtain ⟨b, hb, hinta, hinja, hint, hfield, f, hf, hfhom, hfdeg, hker⟩ :=
    exists_bounded_birational_hypersurface_projection_of_le m n (by omega) I hI d ⟨hdim, hdegree⟩
  by_cases hli : LinearIndependent ℚ (fun i => fun j => (b i j : ℚ))
  · exact ⟨b, hb, hli, hinta, hinja, hint, hfield, f, hf, hfhom, hfdeg, hker⟩
  have htail : LinearIndependent ℚ
      (fun i : Fin (m + 1) => fun j => (b i.succ j : ℚ)) :=
    integer_rows_linearIndependent_of_projection_injective I (fun i => b i.succ) hinja
  have hdep : (fun j => (b 0 j : ℚ)) ∈ Submodule.span ℚ
      (Set.range (fun i : Fin (m + 1) => fun j => (b i.succ j : ℚ))) := by
    by_contra hn
    exact hli (linearIndependent_finSucc.mpr ⟨htail, hn⟩)
  obtain ⟨j, hj⟩ := exists_standard_row_not_mem_span
    (fun i : Fin (m + 1) => fun k => (b i.succ k : ℚ)) htail (by omega)
  let c : Fin (m + 2) → Fin n → ℤ :=
    Fin.cases (fun k => if k = j then 1 else 0) (fun i => b i.succ)
  have hcrows : (fun i => fun k => (c i k : ℚ)) =
      Fin.cons (fun k => if k = j then (1 : ℚ) else 0)
        (fun i : Fin (m + 1) => fun k => (b i.succ k : ℚ)) := by
    funext i
    refine Fin.cases ?_ (fun _ => rfl) i
    funext k
    simp only [c, Fin.cases_zero, Fin.cons_zero]
    split_ifs <;> norm_num
  have hcli : LinearIndependent ℚ (fun i => fun k => (c i k : ℚ)) := by
    rw [hcrows]
    exact htail.finCons hj
  have hH : (1 : ℤ) ≤ integerBirationalProjectionHeight n d := by
    exact_mod_cast (Nat.succ_le_of_lt (integerNormalizationHeight_pos n d)).trans
      (le_max_left (integerNormalizationHeight n d) ((n * d ^ 2 + 1) ^ n))
  have hcb : ∀ i k, |c i k| ≤ integerBirationalProjectionHeight n d := by
    intro i k
    refine Fin.cases ?_ (fun s => hb s.succ k) i
    change |if k = j then (1 : ℤ) else 0| ≤ _
    split_ifs
    · simpa using hH
    · simp
  let A := MvPolynomial (Fin n) ℚ ⧸ I
  let F := FractionRing A
  let L : (Fin n → ℚ) →ₗ[ℚ] F :=
    (IsScalarTower.toAlgHom ℚ A F).toLinearMap.comp
      ((Ideal.Quotient.mkₐ ℚ I).toLinearMap.comp (rationalRowLinearForm n))
  have hL (v : Fin n → ℤ) : L (fun k => (v k : ℚ)) =
      algebraMap A F ((Ideal.Quotient.mk I) (integerLinearForm v)) := by
    change algebraMap A F ((Ideal.Quotient.mk I)
      (rationalRowLinearForm n (fun k => (v k : ℚ)))) = _
    rw [rationalRowLinearForm_integer]
  have hfieldtail : IntermediateField.adjoin ℚ
      (Set.range (fun i : Fin (m + 1) => algebraMap A F
        ((Ideal.Quotient.mk I) (integerLinearForm (b i.succ))))) = ⊤ := by
    have he := adjoin_linear_images_eq_tail_of_first_mem_span
      (fun i => fun k => (b i k : ℚ)) L hdep
    simp only [hL] at he
    rw [← he]
    exact hfield
  let l : Fin (m + 2) → MvPolynomial (Fin n) ℚ := fun i => integerLinearForm (c i)
  have hfieldc : IntermediateField.adjoin ℚ
      (Set.range (fun i => algebraMap A F ((Ideal.Quotient.mk I) (l i)))) = ⊤ := by
    apply top_unique
    rw [← hfieldtail]
    apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨i, rfl⟩
    exact IntermediateField.subset_adjoin ℚ _ (Set.mem_range_self i.succ)
  let ψ := projectionCoordinateMap I l
  have heq : ψ.comp (rename Fin.succ) = projectionCoordinateMap I
      (fun i : Fin (m + 1) => integerLinearForm (b i.succ)) := by
    ext i
    simp only [AlgHom.comp_apply, rename_X, projectionCoordinateMap, aeval_X,
      Ideal.Quotient.mkₐ_eq_mk]
    change (Ideal.Quotient.mk I) (aeval l (X i.succ)) =
      (Ideal.Quotient.mk I) (integerLinearForm (b i.succ))
    rw [aeval_X]
    rfl
  have hintc : ψ.IsIntegral := by
    apply RingHom.IsIntegral.tower_top (rename Fin.succ).toRingHom ψ.toRingHom
    change (ψ.comp (rename Fin.succ)).IsIntegral
    rwa [heq]
  have hAI : AlgebraicIndependent ℚ (fun i : Fin (m + 1) => ψ (X i.succ)) := by
    have hi : AlgebraicIndependent ℚ
        (fun i : Fin (m + 1) => (Ideal.Quotient.mk I) (integerLinearForm (b i.succ))) := by
      change Function.Injective (aeval
        (fun i : Fin (m + 1) => (Ideal.Quotient.mk I) (integerLinearForm (b i.succ))))
      rw [← projectionCoordinateMap_eq_aeval]
      exact hinja
    convert hi using 1
    funext i
    change (Ideal.Quotient.mk I) (aeval l (X i.succ)) =
      (Ideal.Quotient.mk I) (integerLinearForm (b i.succ))
    rw [aeval_X]
    rfl
  obtain ⟨g, hg, hgpos, _, hkg⟩ := exists_hypersurface_projection_equation_degree_le
    I l (fun i => integerLinearForm_degree (c i)) d ⟨hdim, hdegree⟩
    (fun i => X i.succ) (fun _ => by simp) hAI
  have hlhom (i) : (l i).IsHomogeneous 1 := integerLinearForm_isHomogeneous (c i)
  have hlead := homogeneous_finite_birational_projection_leadingCoeff_eq
    (F := F) I hI l hlhom hintc hfieldc
  rw [hkg, principal_filteredHilbertPolynomial_leadingCoeff g hg.ne_zero hgpos,
    hdegree] at hlead
  have hgdeg : g.totalDegree = d := by
    have hh := (div_left_inj' (by positivity : ((m + 1).factorial : ℚ) ≠ 0)).mp hlead
    exact_mod_cast hh
  have hghom : g.IsHomogeneous d := by
    rw [← hgdeg]
    exact homogeneous_projection_equation I hI l hlhom g hg.ne_zero hkg
  exact ⟨c, hcb, hcli, hinta, hinja, hintc, hfieldc, g, hg, hghom, hgdeg, hkg⟩

end
end CCDN
