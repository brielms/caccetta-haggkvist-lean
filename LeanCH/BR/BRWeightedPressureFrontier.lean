import LeanCH.BR.BRWeightedNativePressureReduction
import LeanCH.BR.CHCapstone

/-! Consume only proved boundary-regularity families. The order-only
endpoint q=2r-2 is deliberately retained. -/
namespace LeanCH.BR.WeightedSD
open Finset BRq2 BRq3 BR45 BRsub Compose.Boundary

private theorem restricted_edges_walk (D : CH.Digraph) (V : Finset ℕ)
    (a : ℕ) (L : List ℕ) (he : CH.EdgesFrom (BRsGen35.resD D V) a L) :
    Walk D V a (L.getLastD a) L.length := by
  induction L generalizing a with
  | nil => exact .refl a
  | cons b L ih =>
    obtain ⟨hab,hrest⟩ := he
    obtain ⟨_,hb,hab⟩ := BRsGen35.resD_eq.mp hab
    have hw := Walk.step hb hab (ih b hrest)
    cases L <;> simpa only [List.getLastD_cons, List.getLastD_nil, List.length_cons] using hw

theorem qfree_restriction_no_short {q : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V q) (n : ℕ) : ¬ CH.HasDirectedCycleAtMost (BRsGen35.resD D V) n q := by
  rintro ⟨L,hL,hlen⟩
  cases L with
  | nil => exact hL
  | cons a L =>
    obtain ⟨_,_,_,he,hclose⟩ := hL
    obtain ⟨_,ha,hclose⟩ := BRsGen35.resD_eq.mp hclose
    exact hf a (L.length+1) (by omega) hlen ((restricted_edges_walk D V a L he).snoc ha hclose)

/-- Arbitrary cutoff and degree. Looplessness is explicit because q may be zero. -/
theorem boundary_regular_out_on_set {q r : ℕ} (br : BoundaryRegular q r)
    {D : CH.Digraph} {V : Finset ℕ} (hf : QFree D V q)
    (hl : ∀ x∈V, ¬ D x x=true) (hn : V.card=q*r+1)
    (hm : ∀ x∈V, r≤(outN D V x).card) : OutEq r D V := by
  obtain ⟨n,hsub⟩ := BRsGen35.exists_range V
  have hloop : CH.Loopless (BRsGen35.resD D V) n := by
    intro x _
    apply Bool.eq_false_iff.mpr
    intro he
    obtain ⟨hx,_,hxx⟩ := BRsGen35.resD_eq.mp he
    exact hl x hx hxx
  have hout (x : ℕ) (hx : x∈V) :
      outN (BRsGen35.resD D V) V x=outN D V x := by
    ext y
    simp only [mem_outN,BRsGen35.resD_eq]
    tauto
  have hreg := StrictCap.induced_regular br hsub hn hloop (qfree_restriction_no_short hf n)
    (fun x hx => by change r≤(outN (BRsGen35.resD D V) V x).card; rw [hout x hx]; exact hm x hx)
  intro x hx
  have hh := hreg x hx
  change (outN (BRsGen35.resD D V) V x).card=r at hh
  rwa [hout x hx] at hh

theorem boundary_regular_no_excess {q r : ℕ} (hq : 1≤q) (br : BoundaryRegular q r)
    {D : CH.Digraph} {V : Finset ℕ} (hf : QFree D V q)
    (hn : V.card=q*r+1) (hm : ∀ x∈V, r≤(outN D V x).card)
    {h : ℕ} (hh : h∈V) (hex : r<(outN D V h).card) : False := by
  have he := boundary_regular_out_on_set br hf (fun x hx => loopfree hf hq hx) hn hm h hh
  omega

/-- A precise remaining parameter region, not a claim that its BR cases fail. -/
def NativePressureRegion (q r : ℕ) : Prop :=
  6≤r ∧ q≤2*r-2 ∧ (q=3 → 8≤r) ∧ ¬ (q=9 ∧ r=6)

theorem boundary_regular_outside_pressure_region {q r : ℕ} (hq : 3≤q) (hr : 2≤r)
    (hnot : ¬ NativePressureRegion q r) : BoundaryRegular q r := by
  by_cases hlow : r≤5
  · rcases (by omega : r=2 ∨ r=3 ∨ r=4 ∨ r=5) with rfl | rfl | rfl | rfl
    · exact BRq2.br_q_two q (by omega)
    · exact BRq3.br_q_three q (by omega)
    · by_cases he : q=3
      · subst q; exact BR34.br_four
      · exact BRq4.br_q_four q (by omega)
    · exact BRq5.br_q_five q (by omega)
  by_cases hhigh : 2*r-1≤q
  · exact BRsGen.br_in_window (by omega) hhigh
  by_cases hthree : q=3 ∧ r≤7
  · obtain ⟨rfl,hr7⟩ := hthree
    rcases (by omega : r=6 ∨ r=7) with rfl | rfl
    · exact BR36.br_six
    · exact BR37.br_seven
  have hnine : q=9 ∧ r=6 := by
    by_contra he
    apply hnot
    exact ⟨by omega,by omega,by omega,he⟩
  obtain ⟨rfl,rfl⟩ := hnine
  exact BRq6.br_nine_six

theorem single_excess_pressure_region {q r : ℕ} (hq : 3≤q) (hr : 2≤r)
    {D : CH.Digraph} {V : Finset ℕ} (hf : QFree D V q) (h : V)
    (hn : V.card=q*r+1) (hdh : (outN D V h).card=r+1)
    (hout : ∀ i : V, i≠h → (outN D V i).card=r) : NativePressureRegion q r := by
  by_contra hh
  apply boundary_regular_no_excess (by omega) (boundary_regular_outside_pressure_region hq hr hh)
    hf hn (fun x hx => ?_) h.property (by omega : r<(outN D V h).card)
  by_cases he : (⟨x,hx⟩ : V)=h
  · have he' : x=(h : ℕ) := congrArg Subtype.val he
    rw [he',hdh]; omega
  · rw [hout ⟨x,hx⟩ he]

/-- Actual unconditional narrowing under the same global induction scope.
The alternative with negative pressure is unchanged. -/
theorem strict_source_pressure_frontier {q : ℕ} (hq : 3≤q)
    {D : CH.Digraph} {V : Finset ℕ} (hsmall : SmallerSmallRow q V.card)
    (hf : QFree D V q) (hbad : ¬ SmallRow q D V) :
    ∃ E : CH.Digraph, QFree E V q ∧ ArcCritical q E V ∧ StrictPositiveRows q E V ∧
      ((∃ w∈V, 1+q*(outN E V w).card<V.card) ∨
        (Sat q E V ∧ ∃ r : ℕ, NativePressureRegion q r ∧ V.card=q*r+1 ∧ ∃ h g : V,
          (outN E V h).card=r+1 ∧ (∀ i : V, i≠h → (outN E V i).card=r) ∧
          (inN E V g).card=r+1 ∧ (∀ i : V, i≠g → (inN E V i).card=r))) := by
  obtain ⟨E,hEf,hEc,hEs,hneg | ⟨hsat,r,hr,hn,h,g,hdh,hout,hdg,hin⟩⟩ :=
    strict_source_pressure_reduction hq hsmall hf hbad
  · exact ⟨E,hEf,hEc,hEs,Or.inl hneg⟩
  · exact ⟨E,hEf,hEc,hEs,Or.inr ⟨hsat,r,
      single_excess_pressure_region hq hr hEf h hn hdh hout,hn,h,g,hdh,hout,hdg,hin⟩⟩

end LeanCH.BR.WeightedSD
