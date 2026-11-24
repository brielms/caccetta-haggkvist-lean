import LeanCH.BR.BRShortestCycle

/-! A supplied positive region walk, rather than a minimum-degree premise,
supplies an actual shortest support at that region's own cutoff. -/
namespace LeanCH.BR.WeightedSD
open Finset BRq2 BRq3 BR45 BRsGen

theorem region_closed_walk_shortest_support {D : CH.Digraph} {U : Finset ℕ}
    {q a m : ℕ} (hq : 1≤q) (hf : QFree D U q) (hm : 1≤m)
    (w : Walk D U a a m) :
    ∃ p M,q≤p ∧ QFree D U p ∧ M⊆U ∧ M.card=p+1 ∧
      OutEq 1 D M ∧ (∀v∈M,(inN D M v).card=1) ∧ M.card≤m := by
  classical
  have hex : ∃k,∃a,0<k ∧ Walk D U a a k := ⟨m,a,hm,w⟩
  obtain ⟨b,hk,wb⟩ := Nat.find_spec hex
  have hqk : q<Nat.find hex := by
    by_contra hn
    exact hf b _ hk (by omega) wb
  have hfree : QFree D U (Nat.find hex-1) := by
    intro v k hk hkle wk
    have hle := Nat.find_min' hex ⟨v,hk,wk⟩
    omega
  have ww : Walk D U b b ((Nat.find hex-1)+1) := by
    simpa only [Nat.sub_add_cancel (by omega : 1≤Nat.find hex)] using wb
  obtain ⟨M,hMU,hM,hminM⟩ := boundary_closed_walk_support hfree ww
  have hreg := dt_reg (by omega : 1≤Nat.find hex-1)
    (ball_q_one _ (by omega)) (hfree.mono_set hMU) hminM (by omega)
  have hbound := Nat.find_min' hex ⟨a,hm,w⟩
  exact ⟨Nat.find hex-1,M,by omega,hfree,hMU,hM,hreg.1,hreg.2,by omega⟩

end LeanCH.BR.WeightedSD
