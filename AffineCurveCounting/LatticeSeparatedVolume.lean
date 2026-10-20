module

public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.MeasureTheory.Group.GeometryOfNumbers

/-! Blichfeldt's principle bounds the volume of a measurable set whose
distinct points never differ by a lattice vector. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open Module MeasureTheory
open scoped Pointwise

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem lattice_separated_measure_le
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    {S : Set E} (hS : MeasurableSet S)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x - y ∈ L → x = y) :
    μ.real S ≤ ZLattice.covolume L μ := by
  classical
  let b := Module.Free.chooseBasis ℤ L
  let F := ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ L)
  have hF : IsAddFundamentalDomain L F μ := ZLattice.isAddFundamentalDomain b μ
  have hle : μ S ≤ μ F := by
    by_contra! hlt
    let : MeasurableVAdd L E := inferInstanceAs (MeasurableVAdd L.toAddSubgroup E)
    let : VAddInvariantMeasure L E μ :=
      inferInstanceAs (VAddInvariantMeasure L.toAddSubgroup E μ)
    obtain ⟨a, b, hab, hdis⟩ :=
      exists_pair_mem_lattice_not_disjoint_vadd hF hS.nullMeasurableSet hlt
    obtain ⟨z, ⟨x, hx, hax⟩, y, hy, hby⟩ := Set.not_disjoint_iff.mp hdis
    change (a : E) + x = z at hax
    change (b : E) + y = z at hby
    have hdiff : x - y = (b : E) - a := by
      apply (sub_eq_sub_iff_add_eq_add).mpr
      exact (add_comm _ _).trans (hax.trans hby.symm)
    have hxy := hsep x hx y hy (hdiff ▸ L.sub_mem b.property a.property)
    apply hab
    apply Subtype.ext
    exact add_right_cancel (hax.trans (hby.symm.trans (congrArg ((b : E) + ·) hxy.symm)))
  rw [ZLattice.covolume_eq_measure_fundamentalDomain L μ hF]
  exact ENNReal.toReal_mono
    (ZSpan.fundamentalDomain_isBounded (b.ofZLatticeBasis ℝ L)).measure_lt_top.ne hle

end
end AffineCurveCounting
