module

public import AffineCurveCounting.OriginProjectivePoint

/-! The strict degree bound in the literal CCDN Lemma 5.2 fails at
dimension zero and degree one. A point in P² is a geometrically integral
degree-one variety; its point centers cannot include that point. Any
nonempty set of good centers therefore has a nonempty proper complement,
which cannot be cut out by polynomials of degree strictly below one. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

/-- Actual maximal minors for the one-row matrix representing a point center. -/
def pointCenterPluckerCoordinates {K : Type*} [Field K] {n : ℕ}
    (p : Projectivization K (Fin (n + 1) → K)) : (Fin 1 ↪ Fin (n + 1)) → K :=
  fun c => Matrix.det (Matrix.submatrix (fun (_ : Fin 1) j => p.rep j) id c)

lemma pointCenterPluckerCoordinates_apply {K : Type*} [Field K] {n : ℕ}
    (p : Projectivization K (Fin (n + 1) → K)) (c : Fin 1 ↪ Fin (n + 1)) :
    pointCenterPluckerCoordinates p c = p.rep (c 0) := by
  simp only [pointCenterPluckerCoordinates, Matrix.det_fin_one]
  rfl

lemma totalDegree_zero_eval_constant {K σ : Type*} [Field K]
    (f : MvPolynomial σ K) (hf : f.totalDegree = 0) (a b : σ → K) :
    eval a f = eval b f := by
  rw [(totalDegree_eq_zero_iff_eq_C).mp hf]
  simp only [eval_C]

/-- Even an arbitrary (possibly infinite) family of equations of degree
below one cannot cut out a nonempty proper projective locus. -/
theorem no_constant_equations_for_proper_good_centers {K : Type*} [Field K] {n : ℕ}
    (G : Set (Projectivization K (Fin (n + 1) → K)))
    (hG : G.Nonempty) (q : Projectivization K (Fin (n + 1) → K)) (hq : q ∉ G) :
    ¬ ∃ S : Set (MvPolynomial (Fin (n + 1)) K),
      (∀ f ∈ S, f.totalDegree < 1) ∧
      ∀ p, p ∉ G ↔ ∀ f ∈ S, p ∈ projectiveZeroLocus f := by
  rintro ⟨S,hdeg,hcut⟩
  obtain ⟨p,hp⟩ := hG
  have hqzero := (hcut q).mp hq
  apply ((hcut p).mpr ?_) hp
  intro f hf
  change eval p.rep f = 0
  rw [totalDegree_zero_eval_constant f (by have := hdeg f hf; omega) p.rep q.rep]
  exact hqzero f hf

/-- An actual homogeneous geometrically prime ideal of projective dimension
zero and degree one contradicts Lemma 5.2's strict numerical bound. Every
nonempty good-center locus obeying the necessary center-disjointness
condition fails the asserted defining-equation bound. For point centers
in P², the Plucker coordinates are the original projective coordinates. -/
theorem zero_dimensional_center_degree_bound_obstruction :
    ∃ I : Ideal (CoordinatePolynomial 3), I.IsPrime ∧
      (∀ f ∈ I, ∀ N, homogeneousComponent N f ∈ I) ∧
      (I.map (map (algebraMap ℚ (AlgebraicClosure ℚ)))).IsPrime ∧
      (filteredHilbertPolynomial I).natDegree = 1 ∧
      (filteredHilbertPolynomial I).leadingCoeff = 1 ∧
      ∀ G : Set (ProjectivePoint 2), G.Nonempty →
        (∀ p ∈ G, p ∉ projectiveIdealZeroLocus I) →
        ¬ ∃ S : Set (CoordinatePolynomial 3),
          (∀ f ∈ S, f.totalDegree < (0 + 1) ^ 2 * 1 ^ 2) ∧
          ∀ p, p ∉ G ↔ ∀ f ∈ S, p ∈ projectiveZeroLocus f := by
  refine ⟨originProjectiveIdeal ℚ 2, inferInstance,
    projectiveClosureIdeal_homogeneous _,
    originProjectiveIdeal_geometrically_prime 2,
    (originProjectiveIdeal_hilbert_parameters 2).1,
    (originProjectiveIdeal_hilbert_parameters 2).2, ?_⟩
  intro G hG hdisjoint
  let q : ProjectivePoint 2 := affineProjectivePoint (0 : Fin 2 → ℚ)
  have hq : q ∉ G := by
    intro h
    exact hdisjoint q h ((originProjectiveIdeal_chart_point 0).mpr rfl)
  exact no_constant_equations_for_proper_good_centers G hG q hq

/-- The same obstruction in the actual maximal-minor coordinates used for
the Plucker embedding, without identifying its coordinate index with Fin 3. -/
theorem zero_dimensional_plucker_degree_bound_obstruction :
    ∃ I : Ideal (CoordinatePolynomial 3), I.IsPrime ∧
      (∀ f ∈ I, ∀ N, homogeneousComponent N f ∈ I) ∧
      (I.map (map (algebraMap ℚ (AlgebraicClosure ℚ)))).IsPrime ∧
      (filteredHilbertPolynomial I).natDegree = 1 ∧
      (filteredHilbertPolynomial I).leadingCoeff = 1 ∧
      ∀ G : Set (ProjectivePoint 2), G.Nonempty →
        (∀ p ∈ G, p ∉ projectiveIdealZeroLocus I) →
        ¬ ∃ S : Set (MvPolynomial (Fin 1 ↪ Fin 3) ℚ),
          (∀ f ∈ S, f.totalDegree < (0 + 1) ^ 2 * 1 ^ 2) ∧
          ∀ p, p ∉ G ↔ ∀ f ∈ S, eval (pointCenterPluckerCoordinates p) f = 0 := by
  refine ⟨originProjectiveIdeal ℚ 2, inferInstance,
    projectiveClosureIdeal_homogeneous _,
    originProjectiveIdeal_geometrically_prime 2,
    (originProjectiveIdeal_hilbert_parameters 2).1,
    (originProjectiveIdeal_hilbert_parameters 2).2, ?_⟩
  intro G hG hdisjoint S
  obtain ⟨p,hp⟩ := hG
  let q : ProjectivePoint 2 := affineProjectivePoint (0 : Fin 2 → ℚ)
  have hq : q ∉ G := by
    intro h
    exact hdisjoint q h ((originProjectiveIdeal_chart_point 0).mpr rfl)
  obtain ⟨S,hdeg,hcut⟩ := S
  apply ((hcut p).mpr ?_) hp
  intro f hf
  rw [totalDegree_zero_eval_constant f (by have := hdeg f hf; norm_num at this; omega)
    (pointCenterPluckerCoordinates p) (pointCenterPluckerCoordinates q)]
  exact (hcut q).mp hq f hf

end
end AffineCurveCounting
