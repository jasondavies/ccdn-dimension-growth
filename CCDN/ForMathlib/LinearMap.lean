/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Rank–nullity for the restriction of a linear map to a subspace

## Main results

* `LinearMap.finrank_map_add_finrank_inf_ker`: for a finite-dimensional subspace `V`,
  `finrank (V.map φ) + finrank (V ⊓ ker φ) = finrank V`.
-/

@[expose] public section

namespace LinearMap

variable {K M W : Type*} [DivisionRing K] [AddCommGroup M] [Module K M] [AddCommGroup W]
  [Module K W]

/-- Rank–nullity for the restriction of a linear map to a finite-dimensional subspace. -/
theorem finrank_map_add_finrank_inf_ker (φ : M →ₗ[K] W) (V : Submodule K M)
    [FiniteDimensional K V] :
    Module.finrank K (V.map φ) + Module.finrank K ↥(V ⊓ ker φ) = Module.finrank K V := by
  have h := (φ.domRestrict V).finrank_range_add_finrank_ker
  rwa [range_domRestrict, ker_domRestrict, ← Submodule.finrank_map_subtype_eq V,
    Submodule.map_comap_subtype] at h

end LinearMap
