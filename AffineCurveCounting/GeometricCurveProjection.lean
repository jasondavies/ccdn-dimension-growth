module

public import AffineCurveCounting.ProjectionScalarExtension
public import AffineCurveCounting.BoundedDegreePreservingProjection
public import AffineCurveCounting.ReconstructionFunctionField

/-! The constructed bounded plane projection of a geometrically integral
curve is geometrically integral, birational and degree-preserving. Its
point-count error is at most d(d-1), with no geometric or fiber premises. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

theorem exists_geometrically_integral_curve_projection
    {K L : Type*} [Field K] [CharZero K] [Field L] [Algebra K L] {n : ℕ}
    [DecidableEq (Fin 2 → K)]
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    [(I.map (map (algebraMap K L))).IsPrime]
    (d : ℕ) (hd : 0 < d)
    (hdegree : ∃ N : ℕ, ∃ c : ℤ, ∀ M ≥ N,
      (Module.finrank K (filteredCoordinateSpace I M) : ℤ) = (d : ℤ) * M + c) :
    ∃ (k₀ k₁ : ℕ) (f : MvPolynomial (Fin 2) K),
      k₀ ≤ n ^ 2 * d ∧ k₁ ≤ n * d ^ 2 ∧ Irreducible f ∧
      Irreducible (map (algebraMap K L) f) ∧ f.totalDegree = d ∧
      let a := ![momentCoordinate K n k₀, momentCoordinate K n k₁]
      (∀ g, aeval a g ∈ I ↔ f ∣ g) ∧
      IntermediateField.adjoin K
        (Set.range (fun i => algebraMap (MvPolynomial (Fin n) K ⧸ I)
          (FractionRing (MvPolynomial (Fin n) K ⧸ I))
          ((Ideal.Quotient.mk I) (a i)))) = ⊤ ∧
      aeval a (pderiv 1 f) ∉ I ∧
      (∃ P : Fin n → MvPolynomial (Fin 2) K, ∀ i,
        (P i).totalDegree ≤ d ∧
        aeval a (pderiv 1 f) * X i - aeval a (P i) ∈ I) ∧
      ∀ S : Finset (Fin n → K), (∀ z ∈ S, ∀ g ∈ I, eval z g = 0) →
        S.card ≤ (S.image (fun z i => eval z (a i))).card + d * (d - 1) := by
  classical
  obtain ⟨k₀, k₁, f, hk₀, hk₁, hf, hfd, hu, hker⟩ :=
    exists_bounded_degree_preserving_projection I d hd hdegree
  let a := ![momentCoordinate K n k₀, momentCoordinate K n k₁]
  have ha (i : Fin 2) : (a i).totalDegree ≤ 1 := by
    fin_cases i <;> exact momentCoordinate_degree _ _ _
  have hker' : RingHom.ker (projectionCoordinateMap I a) = Ideal.span {f} := by
    ext g
    rw [mem_projectionCoordinateMap_ker, Ideal.mem_span_singleton]
    exact hker g
  have hgeom := projection_equation_irreducible_map (L := L) I a f hf.ne_zero hker'
  obtain ⟨hQ, _, P, hP⟩ := degree_preserving_projection_reconstruction
    I a ha d hdegree hu f hf.ne_zero hfd hker
  refine ⟨k₀, k₁, f, hk₀, hk₁, hf, hgeom, hfd, hker,
    reconstruction_generates_functionField I a (pderiv 1 f) P hQ (fun i => (hP i).2),
    hQ, ⟨P, hP⟩, ?_⟩
  exact degree_preserving_projection_card_le I a ha d hdegree hu f hf.ne_zero hfd hker

end
end AffineCurveCounting
