module

public import CCDN.Surface.SurfaceSmallCurveCover
public import CCDN.Curve.AffineCurveHilbertPolynomial
/-! Splitting a surface section into bounded-degree geometric
curves, nongeometric exceptions, intermediate-degree curves and the
constructed congruence remainder. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Finset Classical

abbrev GeometricCurveIdeal (I : Ideal (CoordinatePolynomial 3)) : Prop :=
  (I.map (map (algebraMap ℚ (AlgebraicClosure ℚ)))).IsPrime

def smoothSurfaceLocus (f : CoordinatePolynomial 3) : Set (RatPoint 3) :=
  zeroLocus f \ singularHypersurfaceLocus f

lemma integer_smooth_surface_derivative
    (f : MvPolynomial (Fin 3) ℤ) (x : IntPoint 3)
    (hx : rationalPoint x ∈ smoothSurfaceLocus (map (Int.castRingHom ℚ) f)) :
    ∃ j, eval x (pderiv j f) ≠ 0 := by
  by_contra! h
  apply hx.2
  refine ⟨hx.1, ?_⟩
  intro j
  have hh := congrArg (Int.castRingHom ℚ) (h j)
  rw [map_eval, map_zero] at hh
  rw [pderiv_map]
  exact hh

theorem surface_smooth_outside_geometric_cover
    (f : MvPolynomial (Fin 3) ℤ)
    (hir : Irreducible (map (Int.castRingHom ℚ) f))
    {A B H L X : ℝ} (hA : 0 ≤ A) (hB : 1 ≤ B) (hH : 1 ≤ H) (hL : 1 ≤ L)
    (hcoeff : ∀ e, |(f.coeff e : ℝ)| ≤ H)
    (hderivative : 4 * Real.log ((f.totalDegree : ℝ) + 1) +
      Real.log H + f.totalDegree * Real.log B ≤ L)
    (hX : 1 < X) (hBX : B ^ (1 / Real.sqrt (f.totalDegree : ℝ)) ≤ X)
    (hXL : X ≤ Real.exp L) (F : SurfaceCongruenceFamily f B A)
    (S : Finset (Ideal (CoordinatePolynomial 3)))
    (δ : Ideal (CoordinatePolynomial 3) → ℕ) (D : ℕ)
    (hS : ∀ I ∈ S, I.IsPrime ∧ I.height = 2 ∧
      map (Int.castRingHom ℚ) f ∈ I ∧ map (Int.castRingHom ℚ) F.initial ∈ I ∧
      HasAffineCurveDegree I (δ I))
    (hcover : zeroLocus (map (Int.castRingHom ℚ) f) ∩
      zeroLocus (map (Int.castRingHom ℚ) F.initial) = ⋃ I ∈ S, idealZeroLocus I) :
    count (smoothSurfaceLocus (map (Int.castRingHom ℚ) f) \
      (⋃ I ∈ S.filter (fun I => δ I ≤ D ∧ GeometricCurveIdeal I), idealZeroLocus I)) B ≤
      count (⋃ I ∈ S.filter (fun I => δ I ≤ D ∧ ¬GeometricCurveIdeal I), idealZeroLocus I) B +
      count (⋃ I ∈ S.filter (fun I => D < δ I ∧ (δ I : ℝ) ≤
        2 * f.totalDegree * A * surfaceResidueLogBudget B L), idealZeroLocus I) B +
      count (surfaceResidueResidualLocus F S L X hL) B := by
  let bad := ⋃ I ∈ S.filter (fun I => δ I ≤ D ∧ ¬GeometricCurveIdeal I), idealZeroLocus I
  let medium := ⋃ I ∈ S.filter (fun I => D < δ I ∧ (δ I : ℝ) ≤
    2 * f.totalDegree * A * surfaceResidueLogBudget B L), idealZeroLocus I
  let residual := surfaceResidueResidualLocus F S L X hL
  have hpoint : integralPoints (smoothSurfaceLocus (map (Int.castRingHom ℚ) f) \
      (⋃ I ∈ S.filter (fun I => δ I ≤ D ∧ GeometricCurveIdeal I), idealZeroLocus I)) B ⊆
      integralPoints (bad ∪ medium ∪ residual) B := by
    intro x hx
    obtain ⟨hxB,hxsmooth,hxnot⟩ := mem_integralPoints.mp hx
    have hxf : eval x f = 0 := by
      apply (show Function.Injective (Int.castRingHom ℚ) from Int.cast_injective)
      rw [map_eval, map_zero]
      exact hxsmooth.1
    have hinit := F.initial_vanishes x hxB hxf
    have hxinit : rationalPoint x ∈ zeroLocus (map (Int.castRingHom ℚ) F.initial) := by
      have hh := congrArg (Int.castRingHom ℚ) hinit
      rw [map_eval, map_zero] at hh
      exact hh
    have hxcover : rationalPoint x ∈ ⋃ I ∈ S, idealZeroLocus I := by
      rw [← hcover]
      exact ⟨hxsmooth.1,hxinit⟩
    obtain ⟨I,hxI⟩ := Set.mem_iUnion.mp hxcover
    obtain ⟨hIS,hxI⟩ := Set.mem_iUnion.mp hxI
    apply mem_integralPoints.mpr
    refine ⟨hxB,?_⟩
    by_cases hsmall : δ I ≤ D
    · have hnon : ¬GeometricCurveIdeal I := by
        intro hgeo
        exact hxnot (Set.mem_iUnion.mpr ⟨I,Set.mem_iUnion.mpr
          ⟨mem_filter.mpr ⟨hIS,hsmall,hgeo⟩,hxI⟩⟩)
      exact Or.inl (Or.inl (Set.mem_iUnion.mpr ⟨I,Set.mem_iUnion.mpr
        ⟨mem_filter.mpr ⟨hIS,hsmall,hnon⟩,hxI⟩⟩))
    · by_cases hmedium : (δ I : ℝ) ≤ 2 * f.totalDegree * A * surfaceResidueLogBudget B L
      · exact Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨I,Set.mem_iUnion.mpr
          ⟨mem_filter.mpr ⟨hIS,by omega,hmedium⟩,hxI⟩⟩))
      · obtain ⟨hIp,hIheight,hfI,hinitI,hdeg⟩ := hS I hIS
        exact Or.inr (large_curve_point_mem_surfaceResidueResidualLocus f hir hA hB hH hL
          hcoeff hderivative hX hBX hXL F S I hIS hIp hIheight hfI hinitI hdeg
          (lt_of_not_ge hmedium) x hxB hxf hxI (integer_smooth_surface_derivative f x hxsmooth))
  exact (card_le_card hpoint).trans ((count_union_le (bad ∪ medium) residual B).trans
    (Nat.add_le_add_right (count_union_le bad medium B) _))

/-- Nongeometric bounded-degree curves contribute only their squared degrees. -/
theorem nongeometric_curve_union_count_le
    (S : Finset (Ideal (CoordinatePolynomial 3)))
    (δ : Ideal (CoordinatePolynomial 3) → ℕ) (D : ℕ)
    (hS : ∀ I ∈ S, I.IsPrime ∧ 0 < δ I ∧ HasAffineCurveDegree I (δ I))
    {B : ℝ} (hB : 0 ≤ B) :
    (count (⋃ I ∈ S.filter (fun I => δ I ≤ D ∧ ¬GeometricCurveIdeal I), idealZeroLocus I) B : ℝ) ≤
      (D : ℝ) * ∑ I ∈ S, (δ I : ℝ) := by
  calc
    _ ≤ ∑ I ∈ S.filter (fun I => δ I ≤ D ∧ ¬GeometricCurveIdeal I),
        (count (idealZeroLocus I) B : ℝ) := by
      exact_mod_cast count_biUnion_finset_le _ idealZeroLocus B
    _ ≤ ∑ I ∈ S.filter (fun I => δ I ≤ D ∧ ¬GeometricCurveIdeal I), (D : ℝ) * δ I := by
      apply sum_le_sum
      intro I hI
      obtain ⟨hIS,hδ,hnon⟩ := mem_filter.mp hI
      obtain ⟨hprime,hpos,hdeg⟩ := hS I hIS
      have : I.IsPrime := hprime
      have hh := nonabsolute_affine_curve_count_le_degree_sq (K := AlgebraicClosure ℚ)
        I (δ I) hpos hdeg hnon hB
      have hδR : (δ I : ℝ) ≤ D := by exact_mod_cast hδ
      exact hh.trans (by nlinarith [Nat.cast_nonneg (α := ℝ) (δ I)])
    _ ≤ ∑ I ∈ S, (D : ℝ) * δ I :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (by intros; positivity)
    _ = _ := (mul_sum _ _ _).symm

end
end CCDN
