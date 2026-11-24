import LeanCH.BR.BRWeightedSDSubstitution
import LeanCH.BR.BRWeightedTightCut
import LeanCH.BR.BRCapstone

/-! The degree-free weighted obligation has the literal CH consumer.
No inhabitant of the universal obligation is asserted. -/
namespace LeanCH.BR.WeightedSD
open BRq2 BRq3 BR45 BRsub Compose.Boundary

theorem outW_unit (D : CH.Digraph) (V : Finset ℕ) (v : ℕ) :
    outW D V (fun _ => 1) v = (outN D V v).card := by
  rw [outW_eq_mass]
  simp [mass]

theorem inW_unit (D : CH.Digraph) (V : Finset ℕ) (v : ℕ) :
    inW D V (fun _ => 1) v = (inN D V v).card := by
  simpa only [inW, outW, inN, outN] using outW_unit (fun a b => D b a) V v

/-- Self-duality on the exact boundary host implies its full incoming regularity. -/
theorem incoming_regular {q s : ℕ} (hq : 0 < q) {D : CH.Digraph} {V : Finset ℕ}
    (hSD : SelfDual q D V) (hV : V.card = q * s + 1)
    (hm : ∀ v ∈ V, s ≤ (outN D V v).card) :
    ∀ v ∈ V, (inN D V v).card = s := by
  have hqQ : (0 : ℚ) < q := by exact_mod_cast hq
  have hr : ∀ v ∈ V, mass V (fun _ => 1) ≤ row q D V (fun _ => 1) v := by
    intro v hv
    have hdeg : (s : ℚ) ≤ (outN D V v).card := by exact_mod_cast hm v hv
    simp only [mass, Finset.sum_const, nsmul_eq_mul, mul_one, hV, row, outW_unit]
    push_cast
    nlinarith
  have hc := hSD (fun _ => 1) (fun _ _ => by norm_num) hr
  have hin : ∀ v ∈ V, (inN D V v).card ≤ s := by
    intro v hv
    have hh := hc v hv
    simp only [col, inW_unit, mass, Finset.sum_const, nsmul_eq_mul, mul_one, hV] at hh
    push_cast at hh
    have hh' : ((inN D V v).card : ℚ) ≤ s := by nlinarith
    exact_mod_cast hh'
  have hsum := Compose.ThinRigid.sum_out_eq_sum_in D V
  have hlo := Finset.sum_le_sum hm
  have hhi := Finset.sum_le_sum hin
  have heq : (∑ v ∈ V, (inN D V v).card) = ∑ _v ∈ V, s :=
    le_antisymm hhi (hsum ▸ hlo)
  exact (Finset.sum_eq_sum_iff_of_le hin).mp heq

def AllSelfDual : Prop :=
  ∀ q : ℕ, 0 < q → ∀ (D : CH.Digraph) (V : Finset ℕ), QFree D V q → SelfDual q D V

theorem boundaryRegular_of_allSelfDual (h : AllSelfDual) {q s : ℕ} (hq : 0 < q) :
    BoundaryRegular q s := by
  apply br_of_satQ
  intro D hf hm hsat
  exact incoming_regular hq (h q hq D _ hf) (by simp) hm

theorem caccettaHaggkvist_of_allSelfDual (h : AllSelfDual) : CH.CaccettaHaggkvistConjecture := by
  apply caccettaHaggkvist_of_boundaryRegular
  intro q s hq hs
  exact boundaryRegular_of_allSelfDual h hq

end LeanCH.BR.WeightedSD
