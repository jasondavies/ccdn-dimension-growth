module

public import CCDN.HypersurfaceTangentEquality
public import CCDN.LocalizationAdicLayer
public import CCDN.QuotientAdicLayer

/-! The local ring of a hypersurface at the origin and its exact Hilbert
function. Both the coordinate-ring quotient and the stalk localization
are constructions; their adic-layer identifications are proved. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial IsLocalRing

variable {K σ : Type*} [Field K]

lemma idealOfVars_eq_ker_constantCoeff :
    idealOfVars σ K = RingHom.ker (constantCoeff : MvPolynomial σ K →+* K) := by
  ext f
  rw [← pow_one (idealOfVars σ K), mem_pow_idealOfVars_iff']
  change (∀ e, Finsupp.degree e < 1 → f.coeff e = 0) ↔ f.coeff 0 = 0
  constructor
  · intro h
    exact h 0 (by simp)
  · intro h e he
    have he0 : e = 0 := (Finsupp.degree_eq_zero_iff e).mp (by omega)
    simpa only [he0] using h

lemma idealOfVars_isMaximal : (idealOfVars σ K).IsMaximal := by
  rw [idealOfVars_eq_ker_constantCoeff]
  exact RingHom.ker_isMaximal_of_surjective _ (fun c => ⟨C c, by simp⟩)

abbrev HypersurfaceCoordinateRing (f : MvPolynomial σ K) :=
  MvPolynomial σ K ⧸ Ideal.span {f}

def hypersurfaceOriginIdeal (f : MvPolynomial σ K) :
    Ideal (HypersurfaceCoordinateRing f) :=
  (idealOfVars σ K).map (Ideal.Quotient.mk (Ideal.span {f}))

lemma hypersurfaceOriginIdeal_isMaximal (f : MvPolynomial σ K)
    (hf : f ∈ idealOfVars σ K) : (hypersurfaceOriginIdeal f).IsMaximal := by
  let : (idealOfVars σ K).IsMaximal := idealOfVars_isMaximal
  apply Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
  rw [Ideal.mk_ker]
  apply Ideal.span_le.mpr
  rintro _ rfl
  exact hf

/-- The affine coordinate ring's origin-adic layer is the polynomial
truncation layer used to compute its Hilbert function. -/
def hypersurfaceCoordinateLayerEquiv (f : MvPolynomial σ K) (k : ℕ) :
    idealPowerLayer K (hypersurfaceOriginIdeal f) k ≃ₗ[K] originLayer f k :=
  quotientAdicLayerEquiv (Ideal.span {f}) (idealOfVars σ K) k

/-- The stalk of the hypersurface at its origin, expressed as the
localization of its coordinate ring at the origin maximal ideal. -/
abbrev HypersurfaceOriginStalk (f : MvPolynomial σ K)
    [Fact (f ∈ idealOfVars σ K)] :=
  letI := (hypersurfaceOriginIdeal_isMaximal f (Fact.out : f ∈ idealOfVars σ K)).isPrime
  Localization.AtPrime (hypersurfaceOriginIdeal f)

section Stalk

variable (f : MvPolynomial σ K) [Fact (f ∈ idealOfVars σ K)]

local instance : (hypersurfaceOriginIdeal f).IsMaximal :=
  hypersurfaceOriginIdeal_isMaximal f Fact.out

/-- The stalk layer is linearly equivalent to the explicitly
computed origin truncation layer. -/
def hypersurfaceStalkLayerEquiv (k : ℕ) :
    idealPowerLayer K (A := HypersurfaceOriginStalk f)
      (maximalIdeal (HypersurfaceOriginStalk f)) k ≃ₗ[K]
      originLayer f k :=
  (localizationAdicLayerEquiv (K := K) (S := HypersurfaceOriginStalk f)
    (hypersurfaceOriginIdeal f) k).symm.trans (hypersurfaceCoordinateLayerEquiv f k)

theorem hypersurfaceStalkLayer_finrank (k : ℕ) :
    Module.finrank K (idealPowerLayer K (A := HypersurfaceOriginStalk f)
      (maximalIdeal (HypersurfaceOriginStalk f)) k) =
      Module.finrank K (originLayer f k) :=
  (hypersurfaceStalkLayerEquiv f k).finrank_eq

end Stalk

/-- The exact binomial formula of CCDN Lemma 2.1 for the local ring,
with no tangent-cone or localization-isomorphism premise. -/
theorem hypersurfaceOriginStalk_hilbert_eq {n μ k : ℕ}
    (f : MvPolynomial (Fin (n + 1)) K) [Fact (f ∈ idealOfVars (Fin (n + 1)) K)]
    (hf : f ∈ idealOfVars (Fin (n + 1)) K ^ μ)
    (hμ : homogeneousComponent μ f ≠ 0) :
    Module.finrank K
      (idealPowerLayer K (A := HypersurfaceOriginStalk f)
        (maximalIdeal (HypersurfaceOriginStalk f)) k) =
      hypersurfaceLayerBound n μ k := by
  rw [hypersurfaceStalkLayer_finrank]
  exact originLayer_finrank_eq_hypersurfaceLayerBound f hf hμ

end
end CCDN
