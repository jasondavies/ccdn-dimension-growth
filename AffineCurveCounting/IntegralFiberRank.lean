module

public import AffineCurveCounting.IntegralProjectionFiberCount
public import AffineCurveCounting.BoundedLinearSeparation

/-! Sharp specialization-fiber bounds over a normal base. A single integral
linear combination separates a finite set of characteristic-zero points.
Its specialized monic minimal polynomial bounds the entire fiber by the
fraction-field rank, independently of the number of coordinates. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section

/-- Distinct specialization tuples are roots of one separating integral
element's minimal polynomial. Normality bounds its degree by the field rank. -/
theorem integral_coordinate_tuple_count_le_finrank
    (R A F E : Type*) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing A] [IsDomain A] [Field F] [Field E]
    [Algebra R A] [Algebra R F] [IsFractionRing R F]
    [Algebra R E] [Algebra A E] [Algebra F E]
    [IsScalarTower R A E] [IsScalarTower R F E]
    [FiniteDimensional F E]
    {k ι : Type*} [Field k] [CharZero k] [Algebra R k] [Fintype ι]
    (a : ι → A) (ha : ∀ i, IsIntegral R (a i))
    (s : Finset (ι → k))
    (hs : ∀ x ∈ s, ∃ φ : A →ₐ[R] k, ∀ i, φ (a i) = x i) :
    s.card ≤ Module.finrank F E := by
  classical
  let e := (Fintype.equivFin ι).symm
  let v : s → Fin (Fintype.card ι) → k := fun x j => x.val (e j)
  have hv : Function.Injective v := by
    intro x y h
    apply Subtype.ext
    funext i
    obtain ⟨j, rfl⟩ := e.surjective i
    exact congrFun h j
  obtain ⟨t, _, ht⟩ := exists_bounded_moment_separation v hv
  let b : A := ∑ j : Fin (Fintype.card ι), a (e j) * (t : A) ^ j.val
  let L : (ι → k) → k := fun x =>
    ∑ j : Fin (Fintype.card ι), x (e j) * (t : k) ^ j.val
  have hb : IsIntegral R b :=
    IsIntegral.sum _ (fun j _ => (ha (e j)).mul ((isIntegral_natCast t).pow j.val))
  have hL : Set.InjOn L s := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (ht (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy)
  let P := (minpoly R b).map (algebraMap R k)
  have hP : P.Monic := (minpoly.monic hb).map _
  have hroot : ∀ x ∈ s, L x ∈ P.roots := by
    intro x hx
    obtain ⟨φ, hφ⟩ := hs x hx
    have hφb : φ b = L x := by
      simp only [b, L, map_sum, map_mul, map_pow, map_natCast, hφ]
    apply Polynomial.mem_roots hP.ne_zero |>.mpr
    change P.eval (L x) = 0
    rw [← hφb]
    dsimp only [P]
    rw [Polynomial.eval_map_algebraMap, Polynomial.aeval_algHom_apply,
      minpoly.aeval, map_zero]
  have hsub : s.image L ⊆ P.roots.toFinset := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact Multiset.mem_toFinset.mpr (hroot x hx)
  calc
    s.card = (s.image L).card := (Finset.card_image_of_injOn hL).symm
    _ ≤ P.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ P.roots.card := Multiset.toFinset_card_le _
    _ ≤ P.natDegree := Polynomial.card_roots' _
    _ ≤ (minpoly R b).natDegree := Polynomial.natDegree_map_le
    _ ≤ Module.finrank F E :=
      integral_minpoly_natDegree_le_fraction_finrank R A F E b hb

open MvPolynomial

set_option synthInstance.maxHeartbeats 200000 in
/-- The sharp bound for an actual fiber of an integral polynomial projection.
All specialization maps are constructed from the stated coordinate equations. -/
theorem integral_projection_fiber_card_le_finrank
    {K σ τ : Type*} [Field K] [CharZero K] [Fintype σ]
    (I : Ideal (MvPolynomial σ K)) [I.IsPrime]
    (l : τ → MvPolynomial σ K)
    [Algebra (MvPolynomial τ K) (MvPolynomial σ K ⧸ I)]
    (hmap : algebraMap (MvPolynomial τ K) (MvPolynomial σ K ⧸ I) =
      (projectionCoordinateMap I l).toRingHom)
    (F E : Type*) [Field F] [Field E]
    [Algebra (MvPolynomial τ K) F] [IsFractionRing (MvPolynomial τ K) F]
    [Algebra (MvPolynomial τ K) E] [Algebra (MvPolynomial σ K ⧸ I) E]
    [Algebra F E]
    [IsScalarTower (MvPolynomial τ K) (MvPolynomial σ K ⧸ I) E]
    [IsScalarTower (MvPolynomial τ K) F E] [FiniteDimensional F E]
    (hint : (projectionCoordinateMap I l).IsIntegral)
    (z : τ → K) (s : Finset (σ → K))
    (hzero : ∀ x ∈ s, ∀ f ∈ I, eval x f = 0)
    (hproj : ∀ x ∈ s, ∀ i, eval x (l i) = z i) :
    s.card ≤ Module.finrank F E := by
  classical
  let R := MvPolynomial τ K
  let A := MvPolynomial σ K ⧸ I
  let b : σ → A := fun i => Ideal.Quotient.mk I (X i)
  let : Algebra R K := (aeval z).toRingHom.toAlgebra
  have hb (i) : IsIntegral R (b i) := by
    change (algebraMap R A).IsIntegralElem (b i)
    rw [hmap]
    exact hint (b i)
  apply integral_coordinate_tuple_count_le_finrank R A F E b hb s
  intro x hx
  let φ : A →ₐ[K] K := Ideal.Quotient.liftₐ I (aeval x) (fun f hf => hzero x hx f hf)
  have hφ (f : MvPolynomial σ K) :
      φ (Ideal.Quotient.mk I f) = eval x f := by
    exact congrArg (fun g : MvPolynomial σ K →ₐ[K] K => g f)
      (Ideal.Quotient.liftₐ_comp I (aeval x) (fun f hf => hzero x hx f hf))
  have hcomp : φ.comp (projectionCoordinateMap I l) = aeval z := by
    ext i
    simpa only [projectionCoordinateMap, AlgHom.comp_apply, aeval_X,
      Ideal.Quotient.mkₐ_eq_mk] using (hφ (l i)).trans (hproj x hx i)
  let ψ : A →ₐ[R] K :=
    { φ.toRingHom with
      commutes' := fun r => by
        change φ (algebraMap R A r) = (aeval z) r
        rw [hmap]
        exact congrArg (fun f : R →ₐ[K] K => f r) hcomp }
  refine ⟨ψ, ?_⟩
  intro i
  change φ (Ideal.Quotient.mk I (X i)) = x i
  simpa only [eval_X] using hφ (X i)

end
end AffineCurveCounting
