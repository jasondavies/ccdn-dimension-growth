module

public import CCDN.Determinant.ResidueEliminantEvaluation
public import CCDN.Noether.DifferentialConstantRelation
/-! Constant residues in large positive characteristic. The nonzero
annihilating relation and its degree bound are constructed by a Sylvester
resultant. -/

@[expose] public section
namespace CCDN
noncomputable section
open Polynomial Differential
open scoped Differential

/-- The bounded-residue constant lemma used in the differential
irreducibility criterion. This is the needed irreducible case of Gao's
Lemma 2.4, proved directly by differentiating the constructed eliminant. -/
theorem simple_root_ratio_mem_base_of_differential_constant
    {F L : Type*} [Field F] [IsAlgClosed F] [Field L] [Algebra F L]
    [Differential L] {p : ℕ} [CharP L p]
    (hbase : ∀ a : F, (algebraMap F L a)′ = 0)
    (t β : L) (ht : t′ = 1) (f g : F[X][X])
    (hf : Irreducible (f.map (algebraMap F[X] (RatFunc F))))
    (hdeg : g.natDegree < f.natDegree) (D : ℕ)
    (hfD : ∀ i, (f.coeff i).natDegree ≤ D)
    (hgD : ∀ i, (g.coeff i).natDegree ≤ D)
    (hchar : (f.natDegree + (f.natDegree - 1)) * D < p)
    (hroot : (f.map (aeval t).toRingHom).eval β = 0)
    (hsimple : (f.map (aeval t).toRingHom).derivative.eval β ≠ 0)
    (hder : ((g.map (aeval t).toRingHom).eval β /
      (f.map (aeval t).toRingHom).derivative.eval β)′ = 0) :
    (g.map (aeval t).toRingHom).eval β /
      (f.map (aeval t).toRingHom).derivative.eval β ∈ (algebraMap F L).range := by
  by_cases hg : g = 0
  · simp only [hg, Polynomial.map_zero, eval_zero, zero_div]
    exact ⟨0, map_zero _⟩
  · exact differential_constant_mem_base_of_relation hbase t _ ht hder
      (residueEliminant f g) (residueEliminant_ne_zero f g hf hg hdeg)
      ((residueEliminant_natDegree_le f g D hfD hgD).trans_lt hchar)
      (residueEliminant_eval_ratio_eq_zero t β f g hdeg hroot hsimple)

end
end CCDN
