module

public import AffineCurveCounting.ProjectiveClosureProjection
public import AffineCurveCounting.ProjectiveClosureDegree
public import AffineCurveCounting.ReconstructionFunctionField

/-! A linear affine projection generating the actual function field also
generates the function field of the cone over its projective closure when
the homogenizing coordinate is retained. Rational reconstruction on the
standard chart proves this without an assumed compactification map. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

theorem closure_projection_generates_functionField
    {K : Type*} [Field K] {m n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (a : Fin m → MvPolynomial (Fin n) K)
    (ha : ∀ i, (a i).IsHomogeneous 1)
    (hgen : IntermediateField.adjoin K
      (Set.range (fun i => algebraMap (MvPolynomial (Fin n) K ⧸ I)
        (FractionRing (MvPolynomial (Fin n) K ⧸ I))
        ((Ideal.Quotient.mk I) (a i)))) = ⊤) :
    IntermediateField.adjoin K
      (Set.range (fun i => algebraMap
        (MvPolynomial (Fin (n + 1)) K ⧸ projectiveClosureIdeal I)
        (FractionRing (MvPolynomial (Fin (n + 1)) K ⧸ projectiveClosureIdeal I))
        ((Ideal.Quotient.mk (projectiveClosureIdeal I))
          (closureProjectionCoordinates a i)))) = ⊤ := by
  let A := MvPolynomial (Fin n) K ⧸ I
  let φ := IsScalarTower.toAlgHom K A (FractionRing A)
  obtain ⟨Q, P, hQ, hP⟩ := exists_curve_reconstruction_identities
    I φ (IsFractionRing.injective A (FractionRing A)) a hgen
  let J := projectiveClosureIdeal I
  let B := MvPolynomial (Fin (n + 1)) K ⧸ J
  let F := FractionRing B
  let q := IsScalarTower.toAlgHom K B F
  let θ := q.comp (Ideal.Quotient.mkₐ K J)
  let ψ := projectiveChartCoordinateMap J q
  let E := IntermediateField.adjoin K
    (Set.range (fun i => θ (closureProjectionCoordinates a i)))
  have hker : RingHom.ker ψ = I := projectiveClosureIdeal_chart I
  have h0 : θ (X 0) ≠ 0 := by
    intro h
    apply projectiveClosureIdeal_not_X_zero I
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    exact (IsFractionRing.injective B F)
      (by change θ (X 0) = q 0; simpa only [map_zero] using h)
  have h0E : θ (X 0) ∈ E :=
    IntermediateField.subset_adjoin K _ ⟨0, rfl⟩
  have haE (i : Fin m) : ψ (a i) ∈ E := by
    have hh := projectiveChartCoordinateMap_chart J q h0
      (rename Fin.succ (a i)) (ha i).rename_isHomogeneous
    rw [affineChart_rename_succ, pow_one] at hh
    change ψ (a i) = (θ (X 0))⁻¹ * θ (rename Fin.succ (a i)) at hh
    rw [hh]
    exact E.mul_mem (E.inv_mem h0E)
      (IntermediateField.subset_adjoin K _ ⟨i.succ, rfl⟩)
  have heval (p : MvPolynomial (Fin m) K) : ψ (aeval a p) ∈ E := by
    induction p using MvPolynomial.induction_on with
    | C c =>
        rw [aeval_C]
        change ψ (algebraMap K (MvPolynomial (Fin n) K) c) ∈ E
        rw [AlgHom.commutes]
        exact E.algebraMap_mem c
    | add p r hp hr => rw [map_add, map_add]; exact E.add_mem hp hr
    | mul_X p i hp => rw [map_mul, aeval_X, map_mul]; exact E.mul_mem hp (haE i)
  have hQne : ψ (aeval a Q) ≠ 0 := by
    intro h
    apply hQ
    rw [← hker]
    exact h
  have hchart (i : Fin n) : ψ (X i) ∈ E := by
    have hh : aeval a Q * X i - aeval a (P i) ∈ RingHom.ker ψ := by
      rw [hker]
      exact hP i
    change ψ (aeval a Q * X i - aeval a (P i)) = 0 at hh
    rw [map_sub, map_mul, sub_eq_zero] at hh
    have he : ψ (X i) = ψ (aeval a (P i)) / ψ (aeval a Q) := by
      apply (eq_div_iff hQne).mpr
      exact (mul_comm _ _).trans hh
    rw [he]
    exact E.div_mem (heval (P i)) (heval Q)
  have hcoord (i : Fin (n + 1)) : θ (X i) ∈ E := by
    refine Fin.cases h0E (fun j => ?_) i
    have he : ψ (X j) = θ (X j.succ) / θ (X 0) := by
      simp only [ψ, projectiveChartCoordinateMap, aeval_X]
      rfl
    have hj : θ (X j.succ) = ψ (X j) * θ (X 0) := by
      rw [he, div_mul_cancel₀ _ h0]
    rw [hj]
    exact E.mul_mem (hchart j) h0E
  have hpoly (p : MvPolynomial (Fin (n + 1)) K) : θ p ∈ E := by
    induction p using MvPolynomial.induction_on with
    | C c =>
        change θ (algebraMap K (MvPolynomial (Fin (n + 1)) K) c) ∈ E
        rw [AlgHom.commutes]
        exact E.algebraMap_mem c
    | add p r hp hr => rw [map_add]; exact E.add_mem hp hr
    | mul_X p i hp => rw [map_mul]; exact E.mul_mem hp (hcoord i)
  change E = ⊤
  apply top_unique
  intro x _
  obtain ⟨r, s, _, rfl⟩ := IsFractionRing.div_surjective B x
  apply E.div_mem
  · obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective r
    exact hpoly p
  · obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective s
    exact hpoly p

end
end AffineCurveCounting
