module

public import AffineCurveCounting.UniversalHyperplaneRestriction
public import Mathlib.RingTheory.Polynomial.Ideal
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

/-! The actual homogeneous intersection ideal of a hypersurface and a
hyperplane, and its graph-coordinate presentation. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

lemma graphHyperplaneRestriction_surjective {K σ : Type*}
    [CommRing K] [Fintype σ] (a : σ → K) :
    Function.Surjective (graphHyperplaneRestriction a) := by
  have he : (graphHyperplaneRestriction a).comp (rename (R := K) some) =
      AlgHom.id K (MvPolynomial σ K) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [graphHyperplaneRestriction]
  intro f
  exact ⟨rename some f, AlgHom.congr_fun he f⟩

lemma graphHyperplaneRestriction_ker {K σ : Type*}
    [CommRing K] [Fintype σ] (a : σ → K) :
    RingHom.ker (graphHyperplaneRestriction a).toRingHom =
      Ideal.span {X none - ∑ j, C (a j) * X (some j)} := by
  classical
  let L : MvPolynomial σ K := ∑ j, C (a j) * X j
  have he : (graphHyperplaneRestriction a).toRingHom =
      (Polynomial.evalRingHom L).comp (optionEquivLeft K σ).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [graphHyperplaneRestriction]
    · intro i
      cases i <;> simp [graphHyperplaneRestriction, L]
  rw [he, ← RingHom.comap_ker, Polynomial.ker_evalRingHom]
  change Ideal.comap (optionEquivLeft K σ).toRingEquiv _ = _
  rw [← Ideal.map_symm (optionEquivLeft K σ).toRingEquiv, Ideal.map_span, Set.image_singleton]
  change Ideal.span {(optionEquivLeft K σ).symm (Polynomial.X - Polynomial.C L)} = _
  congr 2
  simp [L, map_sum, map_mul]

lemma graphHyperplaneRestriction_comap_span {K σ : Type*}
    [CommRing K] [Fintype σ] (a : σ → K) (f : MvPolynomial (Option σ) K) :
    (Ideal.span {graphHyperplaneRestriction a f}).comap
        (graphHyperplaneRestriction a).toRingHom =
      Ideal.span {f, X none - ∑ j, C (a j) * X (some j)} := by
  have he := Ideal.comap_map_of_surjective (graphHyperplaneRestriction a).toRingHom
    (graphHyperplaneRestriction_surjective a) (Ideal.span {f})
  rw [Ideal.map_span, Set.image_singleton, ← RingHom.ker_eq_comap_bot,
    graphHyperplaneRestriction_ker, ← Ideal.span_union, Set.singleton_union] at he
  exact he

lemma homogeneous_linear_span_isPrime {K σ : Type*} [Field K]
    (f : MvPolynomial σ K) (hf : f.IsHomogeneous 1) :
    (Ideal.span {f}).IsPrime := by
  by_cases hf0 : f = 0
  · subst f
    simpa only [Ideal.span_singleton_zero] using
      (inferInstance : (⊥ : Ideal (MvPolynomial σ K)).IsPrime)
  · have hir : Irreducible f := irreducible_of_totalDegree_eq_one (hf.totalDegree hf0) (by
      intro c hc
      apply isUnit_iff_ne_zero.mpr
      intro hc0
      subst c
      apply hf0
      ext m
      simpa using hc m)
    exact (Ideal.span_singleton_prime hf0).mpr hir.prime

/-- The homogeneous linear equation with coefficient vector A. -/
def hyperplaneNormalPolynomial {K σ : Type*} [CommRing K] [Fintype σ]
    (A : σ → K) : MvPolynomial σ K := ∑ i, C (A i) * X i

lemma hyperplaneNormalPolynomial_homogeneous {K σ : Type*}
    [CommRing K] [Fintype σ] (A : σ → K) :
    (hyperplaneNormalPolynomial A).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ (fun _ _ => isHomogeneous_C_mul_X _ _)

lemma hyperplaneNormalPolynomial_graph {K σ : Type*}
    [Field K] [Fintype σ] (A : Option σ → K) (hA : A none ≠ 0) :
    hyperplaneNormalPolynomial A = C (A none) *
      (X none - ∑ j, C (-A (some j) / A none) * X (some j)) := by
  classical
  simp only [hyperplaneNormalPolynomial, Fintype.sum_option]
  rw [mul_sub, Finset.mul_sum]
  have he : ∀ j, C (A none) * (C (-A (some j) / A none) * X (some j)) =
      -(C (A (some j)) * X (some j)) := by
    intro j
    rw [← mul_assoc, ← map_mul]
    have hh : A none * (-A (some j) / A none) = -A (some j) := by field_simp
    rw [hh, map_neg, neg_mul]
  simp_rw [he]
  rw [Finset.sum_neg_distrib, sub_neg_eq_add]

lemma hyperplaneSectionIdeal_graph {K σ : Type*}
    [Field K] [Fintype σ] (A : Option σ → K) (hA : A none ≠ 0)
    (f : MvPolynomial (Option σ) K) :
    Ideal.span {f, hyperplaneNormalPolynomial A} =
      (Ideal.span {graphHyperplaneRestriction (fun i => -A (some i) / A none) f}).comap
        (graphHyperplaneRestriction (fun i => -A (some i) / A none)).toRingHom := by
  rw [graphHyperplaneRestriction_comap_span, hyperplaneNormalPolynomial_graph A hA,
    Ideal.span_insert, Ideal.span_insert,
    Ideal.span_singleton_mul_left_unit ((isUnit_iff_ne_zero.mpr hA).map C)]

lemma homogeneous_linear_hyperplane_section_isPrime_of_pivot {K σ : Type*}
    [Field K] [Fintype σ] (A : Option σ → K) (hA : A none ≠ 0)
    (f : MvPolynomial (Option σ) K) (hf : f.IsHomogeneous 1) :
    (Ideal.span {f, hyperplaneNormalPolynomial A}).IsPrime := by
  rw [hyperplaneSectionIdeal_graph A hA]
  let a := fun i => -A (some i) / A none
  let : (Ideal.span {graphHyperplaneRestriction a f}).IsPrime :=
    homogeneous_linear_span_isPrime _ (graphHyperplaneRestriction_homogeneous a hf)
  exact Ideal.comap_isPrime _ _

lemma hyperplaneNormalPolynomial_rename {K σ τ : Type*}
    [CommRing K] [Fintype σ] [Fintype τ] (e : σ ≃ τ) (A : σ → K) :
    rename e (hyperplaneNormalPolynomial A) = hyperplaneNormalPolynomial (A ∘ e.symm) := by
  classical
  simp only [hyperplaneNormalPolynomial, map_sum, map_mul, rename_C, rename_X]
  simpa only [Equiv.symm_apply_apply, Function.comp_apply] using
    e.sum_comp (fun j => C (A (e.symm j)) * X j)


/-- Every intersection of two homogeneous linear equations has an integral
coordinate ring, including coincident hyperplanes and zero equations. -/
theorem homogeneous_linear_hyperplane_section_isPrime {K σ : Type*}
    [Field K] [Fintype σ] (A : σ → K)
    (f : MvPolynomial σ K) (hf : f.IsHomogeneous 1) :
    (Ideal.span {f, hyperplaneNormalPolynomial A}).IsPrime := by
  classical
  by_cases hA : A = 0
  · subst A
    simpa [hyperplaneNormalPolynomial] using homogeneous_linear_span_isPrime f hf
  · obtain ⟨i, hi⟩ : ∃ i, A i ≠ 0 := by
      by_contra! h
      exact hA (funext h)
    let e : Option {j : σ // j ≠ i} ≃ σ := Equiv.optionSubtypeNe i
    let E := renameEquiv K e.symm
    have hmap : (Ideal.span {f, hyperplaneNormalPolynomial A}).map E =
        Ideal.span {rename e.symm f, hyperplaneNormalPolynomial (A ∘ e)} := by
      rw [Ideal.map_span, Set.image_pair]
      change Ideal.span {rename e.symm f, rename e.symm (hyperplaneNormalPolynomial A)} = _
      rw [hyperplaneNormalPolynomial_rename]
      rfl
    have hp : (Ideal.span {rename e.symm f,
        hyperplaneNormalPolynomial (A ∘ e)}).IsPrime :=
      homogeneous_linear_hyperplane_section_isPrime_of_pivot (A ∘ e)
        (by simpa [e] using hi) (rename e.symm f) hf.rename_isHomogeneous
    let I := Ideal.span {f, hyperplaneNormalPolynomial A}
    let : (I.map E).IsPrime := by change (Ideal.map E _).IsPrime; rw [hmap]; exact hp
    have hh := Ideal.comap_isPrime E (I.map E)
    rwa [Ideal.comap_map_of_bijective E E.bijective] at hh


end
end AffineCurveCounting
