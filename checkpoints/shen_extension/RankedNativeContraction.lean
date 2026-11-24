import checkpoints.shen_extension.RankedUnitWindow
import checkpoints.shen_extension.MinimumOrderProfile

namespace LeanCH.BR.RankedNativeContraction
open Finset BRq2 BRq3 BR45 WeightedSD Closure

def shortRows (r : ℕ) (D : CH.Digraph) (U : Finset ℕ) :=
  U.filter (fun i=>(outN D U i).card<r)

/-- Delete a marked bank, reuse one of its vertices for the merge, keep
    all arcs on the retained carrier, and fill every row short by one. -/
theorem contract {q r : ℕ} {V W H : Finset ℕ} {D : CH.Digraph} {z : ℕ}
    (free : QFree D V q) (ws : W⊆V) (two : 2≤W.card) (zw : z∈W)
    (heads : H⊆V\W) (quota : r≤H.card)
    (one : ∀i∈V\W,r≤(outN D (V\W) i).card+1)
    (safe : ∀h∈H,∀i∈shortRows r D (V\W),i∉ball D (V\W) h (q-2)) :
    let U := V\W
    let C := insert z U
    let E := coreTwoSidedExtension D U (shortRows r D U) H z
    C.card<V.card ∧ QFree E C q ∧ (∀i∈C,r≤(outN E C i).card) ∧
      (∀i∈U,∀j∈U,E i j=D i j) := by
  intro U C E
  have zu : z∉U := fun hu=>(mem_sdiff.mp hu).2 zw
  have small : C.card<V.card := by
    have count := card_sdiff_add_card_eq_card ws
    change U.card+W.card=V.card at count
    dsimp only [C]
    rw [card_insert_of_notMem zu]
    omega
  have keep (i) (iu : i∈U) (j) (ju : j∈U) : E i j=D i j := by
    have iz : i≠z := fun h=>zu (h ▸ iu)
    have jz : j≠z := fun h=>zu (h ▸ ju)
    simp [E,coreTwoSidedExtension,coreOutgoingExtension,iu,ju,iz,jz]
  refine ⟨small,coreTwoSidedExtension_qfree zu (filter_subset _ _) (free.mono_set sdiff_subset)
    (fun h hh i ii k hk p=>safe h hh i ii (mem_ball.mpr ⟨(mem_filter.mp ii).1,k,hk,p⟩)),?_,keep⟩
  intro i ic
  rcases mem_insert.mp ic with rfl|iu
  · apply quota.trans (card_le_card _)
    intro j jh
    have ju : j∈U := heads jh
    exact mem_outN.mpr ⟨mem_insert_of_mem ju,by simp [E,coreTwoSidedExtension,coreOutgoingExtension,ju,jh]⟩
  · have old : outN D U i⊆outN E C i := by
      intro j jj
      obtain ⟨ju,ij⟩ := mem_outN.mp jj
      exact mem_outN.mpr ⟨mem_insert_of_mem ju,(keep i iu j ju).trans ij⟩
    by_cases enough : r≤(outN D U i).card
    · exact enough.trans (card_le_card old)
    · have sh : i∈shortRows r D U := mem_filter.mpr ⟨iu,Nat.lt_of_not_ge enough⟩
      have hit : z∈outN E C i := mem_outN.mpr ⟨mem_insert_self ..,by simp [E,coreTwoSidedExtension,sh]⟩
      have cap := card_le_card (insert_subset hit old)
      rw [card_insert_of_notMem (fun hz=>zu (outN_subset hz))] at cap
      exact (one i iu).trans cap

/-- A prefix avoiding all erased labels avoids each genuinely short row.
    The original minimum degree supplies the lost head witnessing shortness. -/
theorem interior_safe {q r : ℕ} {V W : Finset ℕ} {D : CH.Digraph} (hq : 2≤q)
    (ws : W⊆V) (deg : ∀i∈V,r≤(outN D V i).card) :
    let U := V\W
    ∀h∈FlatPeelReach.interior D V U (q-1),∀i∈shortRows r D U,i∉ball D U h (q-2) := by
  intro U h hh i ii ib
  obtain ⟨hv,stays⟩ := mem_filter.mp hh
  have hu := stays (self_mem_ball hv)
  obtain ⟨iu,lt⟩ := mem_filter.mp ii
  have rad : q-2+1=q-1 := by omega
  have avoid := (RankedHeadChoices.avoid_iff (k:=q-2) ws hu).mpr (by simpa only [rad] using stays)
  have no := avoid i ib
  have sub : outN D V i ⊆ outN D U i := by
    intro j jj
    obtain ⟨jv,ij⟩ := mem_outN.mp jj
    exact mem_outN.mpr ⟨mem_sdiff.mpr ⟨jv,fun jw=>no j jw ij⟩,ij⟩
  exact lt.not_ge ((deg i (mem_sdiff.mp iu).1).trans (card_le_card sub))

structure NativeWindow {q r} (X : ShenMinimumOrder.Source q r) : Prop where
  cap : ∀W⊆X.V,2≤W.card → (∀i∈X.V\W,r≤(outN X.D (X.V\W) i).card+1) →
    (FlatPeelReach.interior X.D X.V (X.V\W) (q-1)).card < r

@[aesop safe forward (immediate := [X,hq]) (rule_sets := [CHGraphFamilies])]
theorem least_window {q r} (X : ShenMinimumOrder.Source q r) (hq : 2≤q) : NativeWindow X := by
  refine ⟨fun W ws two one=>?_⟩
  by_contra! rich
  obtain ⟨z,zw⟩ := card_pos.mp (show 0<W.card by omega)
  let U := X.V\W
  let H := FlatPeelReach.interior X.D X.V U (q-1)
  have hs : H⊆U := fun h hh=>(mem_filter.mp hh).2 (self_mem_ball (mem_filter.mp hh).1)
  obtain ⟨sh,free,degree,_⟩ := contract X.free ws two zw hs rich one (interior_safe hq ws X.degree)
  exact sh.not_ge (X.least _ _ free degree (insert_nonempty z U))

/-- If enough starts avoid two given labels, the same native tight row has
    to hit both. Surplus at every common parent already funds the merge. -/
theorem tight_parent {q r} {X : ShenMinimumOrder.Source q r} (window : NativeWindow X)
    {a d : ℕ} (av : a∈X.V) (dv : d∈X.V) (ad : a≠d)
    (rich : r≤(FlatPeelReach.interior X.D X.V (X.V\{a,d}) (q-1)).card) :
    ∃ i∈X.V\{a,d},(outN X.D X.V i).card=r ∧ X.D i a=true ∧ X.D i d=true := by
  let U := X.V\{a,d}
  have sub := insert_subset av (singleton_subset_iff.mpr dv)
  have fail : ¬∀i∈U,r≤(outN X.D U i).card+1 :=
    fun one=>(window.cap {a,d} sub (by rw [card_pair ad]) one).not_ge rich
  push Not at fail
  obtain ⟨i,iu,short⟩ := fail
  have old := X.degree i (mem_sdiff.mp iu).1
  have native : outN X.D X.V i ⊆ (outN X.D U i) ∪ (outN X.D {a,d} i) := by
    intro j jj
    obtain ⟨jv,ij⟩ := mem_outN.mp jj
    by_cases cut : j∈({a,d}:Finset ℕ)
    · exact mem_union_right _ (mem_outN.mpr ⟨cut,ij⟩)
    · exact mem_union_left _ (mem_outN.mpr ⟨mem_sdiff.mpr ⟨jv,cut⟩,ij⟩)
  have cap := (card_le_card native).trans (card_union_le _ _)
  have maxTwo := card_le_card (outN_subset (D:=X.D) (W:={a,d}) (y:=i))
  rw [card_pair ad] at maxTwo
  have both : outN X.D {a,d} i = {a,d} :=
    eq_of_subset_of_card_le outN_subset (by rw [card_pair ad]; omega)
  have first := (mem_outN.mp (show a∈outN X.D {a,d} i by rw [both]; exact mem_insert_self ..)).2
  have second := (mem_outN.mp (show d∈outN X.D {a,d} i by rw [both]; exact mem_insert_of_mem (mem_singleton_self d))).2
  exact ⟨i,iu,by omega,first,second⟩

#print axioms contract
#print axioms tight_parent
#print axioms least_window
end LeanCH.BR.RankedNativeContraction
