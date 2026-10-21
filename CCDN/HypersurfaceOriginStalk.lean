module

public import CCDN.HypersurfaceTangentEquality
public import CCDN.LocalizationAdicLayer
public import CCDN.QuotientAdicLayer

/-! The coordinate ring of a hypersurface and its origin ideal. The
origin-adic layers of the coordinate ring are the polynomial
truncation layers. -/

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

/-- The affine coordinate ring's origin-adic layer is the polynomial
truncation layer used to compute its Hilbert function. -/
def hypersurfaceCoordinateLayerEquiv (f : MvPolynomial σ K) (k : ℕ) :
    idealPowerLayer K (hypersurfaceOriginIdeal f) k ≃ₗ[K] originLayer f k :=
  quotientAdicLayerEquiv (Ideal.span {f}) (idealOfVars σ K) k

end
end CCDN
