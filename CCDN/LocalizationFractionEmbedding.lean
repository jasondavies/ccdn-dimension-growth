module

public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.Localization.FractionRing

/-! A nonzero localization of a domain embeds compatibly in any
fraction field of that domain and has the same fraction field. -/

@[expose] public section
namespace CCDN
noncomputable section

lemma localization_denominator_ne_zero {R S : Type*}
    [CommRing R] [CommRing S] [Nontrivial S] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S] (y : M) : (y : R) ≠ 0 := by
  intro hy
  have h := (IsLocalization.map_units S y).ne_zero
  exact h (by rw [hy,map_zero])

def localizationFractionEmbedding {R S F : Type*}
    [CommRing R] [IsDomain R] [CommRing S] [Nontrivial S]
    [Field F] [Algebra R S] [Algebra R F]
    (M : Submonoid R) [IsLocalization M S] [IsFractionRing R F] : S →+* F :=
  IsLocalization.lift (fun y : M => isUnit_iff_ne_zero.mpr
    ((map_ne_zero_iff _ (IsFractionRing.injective R F)).mpr
      (localization_denominator_ne_zero (S := S) M y)))

@[simp] lemma localizationFractionEmbedding_algebraMap {R S F : Type*}
    [CommRing R] [IsDomain R] [CommRing S] [Nontrivial S]
    [Field F] [Algebra R S] [Algebra R F]
    (M : Submonoid R) [IsLocalization M S] [IsFractionRing R F] (x : R) :
    localizationFractionEmbedding (S := S) (F := F) M (algebraMap R S x) =
      algebraMap R F x := IsLocalization.lift_eq _ _

lemma localizationFractionEmbedding_comp {R S F : Type*}
    [CommRing R] [IsDomain R] [CommRing S] [Nontrivial S]
    [Field F] [Algebra R S] [Algebra R F]
    (M : Submonoid R) [IsLocalization M S] [IsFractionRing R F] :
    (localizationFractionEmbedding (S := S) (F := F) M).comp (algebraMap R S) =
      algebraMap R F := IsLocalization.lift_comp _

theorem localizationFractionEmbedding_isFractionRing {R S F : Type*}
    [CommRing R] [IsDomain R] [CommRing S] [Nontrivial S]
    [Field F] [Algebra R S] [Algebra R F]
    (M : Submonoid R) [IsLocalization M S] [IsFractionRing R F] :
    let : Algebra S F := (localizationFractionEmbedding (S := S) (F := F) M).toAlgebra
    IsFractionRing S F := by
  let : Algebra S F := (localizationFractionEmbedding (S := S) (F := F) M).toAlgebra
  let : IsScalarTower R S F := IsScalarTower.of_algebraMap_eq'
    (localizationFractionEmbedding_comp M).symm
  exact IsFractionRing.isFractionRing_of_isDomain_of_isLocalization M S F

end
end CCDN
