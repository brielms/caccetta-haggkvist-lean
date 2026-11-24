import checkpoints.shen_extension.ReturnBankOrder

namespace LeanCH.BR.Closure.RootFirstArcReturns
open Finset BRq2 BRq3 BR45 DeficitLevels

/-- The labels left after deleting the root and all of its incoming neighbors. -/
def retained (D : CH.Digraph) (V : Finset ℕ) (h : ℕ) : Finset ℕ :=
  V \ insert h (inN D V h)

/-- First heads at the root that lead in one further step to an actual short row. -/
def firstArcs (D : CH.Digraph) (V : Finset ℕ) (h s : ℕ) : Finset ℕ := by
  classical
  let W := retained D V h
  exact (outN D V h).filter (fun a => ∃ z ∈ outN D W a, (outN D W z).card < s)

private theorem full_first_head {s} (S : Origin 3 s) {h a} (hv : h ∈ S.V)
    (ha : a ∈ outN S.G S.V h) :
    a ∈ retained S.G S.V h ∧ s ≤ (outN S.G (retained S.G S.V h) a).card := by
  obtain ⟨av,ea⟩ := mem_outN.mp ha
  have ah : a ≠ h := fun eq => loopfree S.free (by decide) hv (eq ▸ ea)
  have rev : S.G a h ≠ true := digonfree S.free (by decide) hv av ea
  have ai : a ∉ inN S.G S.V h := fun hit => rev (mem_inN.mp hit).2
  refine ⟨mem_sdiff.mpr ⟨av,by simp [ah,ai]⟩,(S.deg a av).trans (card_le_card ?_)⟩
  intro z hz
  obtain ⟨zv,az⟩ := mem_outN.mp hz
  have zh : z ≠ h := fun eq => rev (eq ▸ az)
  have zi : z ∉ inN S.G S.V h := fun hit =>
    S.free h 3 (by decide) (by decide) (.step av ea (.step zv az
      (.step hv (mem_inN.mp hit).2 (.refl h))))
  exact mem_outN.mpr ⟨mem_sdiff.mpr ⟨zv,by simp [zh,zi]⟩,az⟩

/-- Every head lost by a retained row was an incoming neighbor of the root. -/
theorem row_count {D : CH.Digraph} {V : Finset ℕ} {x h}
    (xw : x ∈ retained D V h) :
    (outN D (retained D V h) x).card + (outN D (inN D V h) x).card =
      (outN D V x).card := by
  have noRoot : D x h ≠ true := fun edge =>
    (mem_sdiff.mp xw).2 (mem_insert_of_mem (mem_inN.mpr ⟨(mem_sdiff.mp xw).1,edge⟩))
  have partition : outN D V x = outN D (retained D V h) x ∪ outN D (inN D V h) x := by
    ext z
    constructor
    · intro hz
      obtain ⟨zv,edge⟩ := mem_outN.mp hz
      by_cases zi : z ∈ inN D V h
      · exact mem_union_right _ (mem_outN.mpr ⟨zi,edge⟩)
      · have zh : z ≠ h := fun eq => noRoot (eq ▸ edge)
        exact mem_union_left _ (mem_outN.mpr ⟨mem_sdiff.mpr ⟨zv,by simp [zh,zi]⟩,edge⟩)
    · intro hz
      rcases mem_union.mp hz with zw|zi
      · exact mem_outN.mpr ⟨(mem_sdiff.mp (outN_subset zw)).1,(mem_outN.mp zw).2⟩
      · exact mem_outN.mpr ⟨(mem_inN.mp (outN_subset zi)).1,(mem_outN.mp zi).2⟩
  have disj : Disjoint (outN D (retained D V h) x) (outN D (inN D V h) x) :=
    disjoint_left.mpr (fun _ zw zi =>
      (mem_sdiff.mp (outN_subset zw)).2 (mem_insert_of_mem (outN_subset zi)))
  rw [partition,card_union_of_disjoint disj]

/-- Each counted first head lies on an original four-cycle. Its middle row loses
more heads into the incoming neighborhood than its original surplus. -/
theorem cycle_of_mem {s} (S : Origin 3 s) {h a} (hv : h ∈ S.V)
    (ha : a ∈ firstArcs S.G S.V h s) :
    ∃ z ∈ retained S.G S.V h \ outN S.G S.V h, ∃ b ∈ inN S.G S.V h,
      S.G h a = true ∧ S.G a z = true ∧ S.G z b = true ∧ S.G b h = true ∧
      (outN S.G S.V z).card - s < (outN S.G (inN S.G S.V h) z).card := by
  obtain ⟨ao,z,az,short⟩ := mem_filter.mp ha
  have zw := outN_subset az
  have zo : z ∉ outN S.G S.V h := fun zh => short.not_ge (full_first_head S hv zh).2
  have total := row_count zw
  have degree := S.deg z (mem_sdiff.mp zw).1
  have loss : (outN S.G S.V z).card - s < (outN S.G (inN S.G S.V h) z).card := by omega
  obtain ⟨b,bz⟩ := card_pos.mp (Nat.zero_lt_of_lt loss)
  have bi := outN_subset bz
  exact ⟨z,mem_sdiff.mpr ⟨zw,zo⟩,b,bi,(mem_outN.mp ao).2,(mem_outN.mp az).2,(mem_outN.mp bz).2,
    (mem_inN.mp bi).2,loss⟩

/-- At each original root, outdegree surplus and one third of the indegree
(rounded up) give a lower bound for the number of distinct first arcs. -/
theorem first_arc_bound {s} (S : Origin 3 s) {h} (hv : h ∈ S.V) :
    (outN S.G S.V h).card - s + ((inN S.G S.V h).card + 2) / 3 ≤
      (firstArcs S.G S.V h s).card := by
  classical
  let O := outN S.G S.V h
  let I := inN S.G S.V h
  let W := retained S.G S.V h
  let F := firstArcs S.G S.V h s
  let E := ReturnBankOrder.exits S.G W 3 s
  have wv : W ⊆ S.V := sdiff_subset
  have iv : I ⊆ S.V := filter_subset _ _
  have hi : h ∉ I := fun hit => loopfree S.free (by decide) hv (mem_inN.mp hit).2
  have size : W.card + (I.card+1) = S.V.card := by
    have eq := card_sdiff_add_card_eq_card (insert_subset hv iv)
    rwa [card_insert_of_notMem hi] at eq
  have cap (x) (hx : x ∈ W) : s ≤ (outN S.G W x).card + I.card := by
    have total := row_count hx
    have degree := S.deg x (wv hx)
    have lost : (outN S.G I x).card ≤ I.card := card_le_card outN_subset
    change (outN S.G W x).card + (outN S.G I x).card = _ at total
    omega
  have exitBound : I.card ≤ 3*(s-E.card) :=
    ReturnBankOrder.same_order S (by decide) wv (by omega) cap
  have ipos : 0 < I.card := by
    by_contra! zero
    have vpos := card_pos.mpr S.ne
    have order := S.order
    have odeg := S.deg h hv
    obtain ⟨a,ao⟩ := card_pos.mp (show 0 < (outN S.G S.V h).card by omega)
    have wne : W.Nonempty := ⟨a,(full_first_head S hv ao).1⟩
    have least := S.least S.G W (S.free.mono_set wv) (fun x hx => by have := cap x hx; omega) wne
    omega
  have good : O \ F ⊆ E := by
    intro a ha
    obtain ⟨ao,avoid⟩ := mem_sdiff.mp ha
    obtain ⟨aw,paid⟩ := full_first_head S hv ao
    apply ReturnBankOrder.triangle_exits.mpr
    refine ⟨aw,paid,?_⟩
    intro z az
    by_contra! short
    exact avoid (mem_filter.mpr ⟨ao,z,az,short⟩)
  have fsub : F ⊆ O := filter_subset _ _
  have split := card_sdiff_add_card_eq_card fsub
  have safeCard := card_le_card good
  have floor : s ≤ O.card := S.deg h hv
  change O.card - s + (I.card + 2) / 3 ≤ F.card
  omega

#print axioms cycle_of_mem
#print axioms first_arc_bound
end LeanCH.BR.Closure.RootFirstArcReturns
