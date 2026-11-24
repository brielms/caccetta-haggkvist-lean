import checkpoints.shen_extension.DotFourthPrefixQuadratic_20261118
import checkpoints.shen_extension.DotFourthSourceAdapters_20261118

/-!
Fourth-strip closure from the actual source packet and one joint clone-pair
completion. This is a separate theorem module, not the canonical capstone.
-/
namespace LeanCH.BR.DotFourthStripClosure
open BRq2 BRq3 BR45 BRsGen
open DotFourthPrefixQuadratic DotFourthSourceAdapters

/-- The full source at n=qs is excluded for s=a+7>=12, q=2s-6.
No flatness, exact degree, or clone certificate is assumed. -/
theorem fourth_strip_upper_false {a : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (ha : 5≤a) (hf : QFree D V (2*a+8))
    (hm : ∀ v ∈ V,a+7≤(outN D V v).card)
    (hne : V.Nonempty) (hn : V.card=(2*a+8)*(a+7)) : False := by
  obtain ⟨_,houter,u,hu,e,he,hR,hprev,hinner⟩ :=
    source_minimum_packet ha hf hm hne hn
  exact minimum_table_false ha he hf hm hn hu hR hprev hinner houter

/-- Arbitrary finite nonempty q-free hosts have order strictly greater than qs. -/
theorem order_fourth_strip_closed {a : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (ha : 5≤a) (hf : QFree D V (2*a+8))
    (hm : ∀ v ∈ V,a+7≤(outN D V v).card) (hne : V.Nonempty) :
    (2*a+8)*(a+7)<V.card := by
  have hl := ShenFourthStrip.order_to_top hf hm hne (by omega : 1≤a)
  by_contra! hn
  exact fourth_strip_upper_false ha hf hm hne (by omega)

/-- Public fourth-strip statement in the original finite-digraph API. -/
theorem cycle_fourth_strip_closed {s q n : ℕ} {D : CH.Digraph}
    (hs : 12≤s) (hq : q=2*s-6) (hn : 0<n) (hnq : n≤q*s)
    (hl : CH.Loopless D n) (hm : CH.MinOutdegreeAtLeast D n s) :
    CH.HasDirectedCycleAtMost D n q := by
  obtain ⟨a,ha⟩ : ∃ a,s=a+7 := ⟨s-7,by omega⟩
  subst s
  have hq' : q=2*a+8 := by omega
  rw [hq'] at hnq ⊢
  by_contra hh
  have ho := order_fourth_strip_closed (by omega : 5≤a) (qfree_of_noShort hl hh)
    (fun v hv => Compose.FloorSix.out_card hm (Finset.mem_range.mp hv))
    ⟨0,Finset.mem_range.mpr hn⟩
  rw [Finset.card_range] at ho
  omega

#print axioms fourth_strip_upper_false
#print axioms order_fourth_strip_closed
#print axioms cycle_fourth_strip_closed
end LeanCH.BR.DotFourthStripClosure
