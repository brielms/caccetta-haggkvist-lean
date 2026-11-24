import checkpoints.shen_extension.DeleteRepairUnlock

/-!
# Returning one original vertex through the actual current graph

The original G and current H are distinct. H is explicitly restricted to U;
its irrelevant values at the deleted vertex are never resurrected. Cut every
CURRENT Y-to-X arc, then restore the ORIGINAL X-to-v-to-Y star. This file has
no source rank, degree funding, edited-Source cast or convergence assumption.
-/
namespace LeanCH.BR.DotOriginalStarReturn
open LeanCH.BR.BRq2 LeanCH.BR.BRq3

noncomputable def parents (G : CH.Digraph) (U : Finset ℕ) (v : ℕ) : Finset ℕ :=
  U.filter (fun x => G x v = true)

/-- The current old part is restricted at BOTH ends to U. -/
noncomputable def star (H : CH.Digraph) (U X Y : Finset ℕ) (v : ℕ) : CH.Digraph := by
  classical
  exact fun a b => decide
    ((a ∈ U ∧ b ∈ U ∧ H a b = true ∧ (a ∉ Y ∨ b ∉ X)) ∨
      (a ∈ X ∧ b = v) ∨ (a = v ∧ b ∈ Y))

noncomputable def originalReturn (G H : CH.Digraph) (U : Finset ℕ) (v : ℕ) : CH.Digraph :=
  star H U (parents G U v) (outN G U v) v

@[simp] theorem star_edge {H : CH.Digraph} {U X Y : Finset ℕ} {v a b : ℕ} :
    star H U X Y v a b = true ↔
      (a ∈ U ∧ b ∈ U ∧ H a b = true ∧ (a ∉ Y ∨ b ∉ X)) ∨
      (a ∈ X ∧ b = v) ∨ (a = v ∧ b ∈ Y) := by
  classical
  simp [star]

theorem star_incoming {H : CH.Digraph} {U X Y : Finset ℕ} {v a : ℕ}
    (hv : v ∉ U) (hY : Y ⊆ U) : star H U X Y v a v = true ↔ a ∈ X := by
  have hnotY : v ∉ Y := fun hy => hv (hY hy)
  simp [star_edge, hv, hnotY]

theorem star_outgoing {H : CH.Digraph} {U X Y : Finset ℕ} {v b : ℕ}
    (hv : v ∉ U) (hX : X ⊆ U) : star H U X Y v v b = true ↔ b ∈ Y := by
  have hnotX : v ∉ X := fun hx => hv (hX hx)
  simp [star_edge, hv, hnotX]

theorem star_old_edge {H : CH.Digraph} {U X Y : Finset ℕ} {v a b : ℕ}
    (hv : v ∉ U) (ha : a ∈ U) (hb : b ∈ U) :
    star H U X Y v a b = true ↔ H a b = true ∧ (a ∉ Y ∨ b ∉ X) := by
  have hav : a ≠ v := fun he => hv (he ▸ ha)
  have hbv : b ≠ v := fun he => hv (he ▸ hb)
  simp [star_edge, ha, hb, hav, hbv]

/-- The elementary three-cycle adapter includes loops and digons explicitly. -/
theorem qfree_three_of_tests {D : CH.Digraph} {W : Finset ℕ}
    (loops : ∀ a ∈ W, D a a ≠ true)
    (digons : ∀ a ∈ W, ∀ b ∈ W, D a b = true → D b a = true → False)
    (triangles : ∀ a ∈ W, ∀ b ∈ W, ∀ c ∈ W,
      D a b = true → D b c = true → D c a = true → False) : QFree D W 3 := by
  intro a n hpos hbound walk
  have hn : n = 1 ∨ n = 2 ∨ n = 3 := by omega
  rcases hn with rfl | rfl | rfl
  · cases walk with
    | step hb hab rest =>
      cases rest
      exact loops a hb hab
  · cases walk with
    | step hb hab rest =>
      cases rest with
      | step hc hbc last =>
        cases last
        exact digons a hc _ hb hab hbc
  · cases walk with
    | step hb hab rest =>
      cases rest with
      | step hc hbc rest =>
        cases rest with
        | step hd hcd last =>
          cases last
          exact triangles a hd _ hb _ hc hab hbc hcd

/-- Safety needs the CURRENT old graph, disjoint banks and the complete cut.
No independent old-mask or separately safe-star composition is used. -/
theorem star_qfree {H : CH.Digraph} {U X Y : Finset ℕ} {v : ℕ}
    (hf : QFree H U 3) (hv : v ∉ U) (hX : X ⊆ U) (hY : Y ⊆ U)
    (disj : Disjoint X Y) : QFree (star H U X Y v) (insert v U) 3 := by
  apply qfree_three_of_tests
  · intro a ha edge
    by_cases hav : a = v
    · subst a
      exact hv (hY ((star_outgoing hv hX).mp edge))
    · have haU := (Finset.mem_insert.mp ha).resolve_left hav
      exact loopfree hf (by omega) haU ((star_old_edge hv haU haU).mp edge).1
  · intro a ha b hb hab hba
    by_cases hav : a = v
    · subst a
      exact Finset.disjoint_left.mp disj ((star_incoming hv hY).mp hba)
        ((star_outgoing hv hX).mp hab)
    by_cases hbv : b = v
    · subst b
      exact Finset.disjoint_left.mp disj ((star_incoming hv hY).mp hab)
        ((star_outgoing hv hX).mp hba)
    have haU := (Finset.mem_insert.mp ha).resolve_left hav
    have hbU := (Finset.mem_insert.mp hb).resolve_left hbv
    exact digonfree hf (by omega) haU hbU
      ((star_old_edge hv haU hbU).mp hab).1 ((star_old_edge hv hbU haU).mp hba).1
  · intro a ha b hb c hc hab hbc hca
    by_cases hav : a = v
    · subst a
      have hbY := (star_outgoing hv hX).mp hab
      have hcX := (star_incoming hv hY).mp hca
      rcases ((star_old_edge hv (hY hbY) (hX hcX)).mp hbc).2 with noY | noX
      · exact noY hbY
      · exact noX hcX
    by_cases hbv : b = v
    · subst b
      have hcY := (star_outgoing hv hX).mp hbc
      have haX := (star_incoming hv hY).mp hab
      rcases ((star_old_edge hv (hY hcY) (hX haX)).mp hca).2 with noY | noX
      · exact noY hcY
      · exact noX haX
    by_cases hcv : c = v
    · subst c
      have haY := (star_outgoing hv hX).mp hca
      have hbX := (star_incoming hv hY).mp hbc
      rcases ((star_old_edge hv (hY haY) (hX hbX)).mp hab).2 with noY | noX
      · exact noY haY
      · exact noX hbX
    have haU := (Finset.mem_insert.mp ha).resolve_left hav
    have hbU := (Finset.mem_insert.mp hb).resolve_left hbv
    have hcU := (Finset.mem_insert.mp hc).resolve_left hcv
    exact hf a 3 (by omega) (by omega)
      (.step hbU ((star_old_edge hv haU hbU).mp hab).1
        (.step hcU ((star_old_edge hv hbU hcU).mp hbc).1
          (.step haU ((star_old_edge hv hcU haU).mp hca).1 (.refl a))))

/-- Original no2 supplies disjoint X and Y, even though H need not be a G-subgraph. -/
theorem original_banks_disjoint {G : CH.Digraph} {V U : Finset ℕ} {v : ℕ}
    (hf : QFree G V 3) (hUV : U ⊆ V) (hv : v ∈ V) :
    Disjoint (parents G U v) (outN G U v) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨hxU,hxv⟩ := Finset.mem_filter.mp hx
  obtain ⟨_,hvx⟩ := mem_outN.mp hy
  exact digonfree hf (by omega) (hUV hxU) hv hxv hvx

/-- Every CURRENT cut edge has an original-star witness proving it NONORIGINAL. -/
theorem original_no_cross {G : CH.Digraph} {V U : Finset ℕ} {v y x : ℕ}
    (hf : QFree G V 3) (hUV : U ⊆ V) (hv : v ∈ V)
    (hy : y ∈ outN G U v) (hx : x ∈ parents G U v) : G y x ≠ true := by
  intro edge
  obtain ⟨hyU,hvy⟩ := mem_outN.mp hy
  obtain ⟨hxU,hxv⟩ := Finset.mem_filter.mp hx
  exact hf v 3 (by omega) (by omega)
    (.step (hUV hyU) hvy (.step (hUV hxU) edge (.step hv hxv (.refl v))))

/-- On an ORIGINAL live-to-live edge, RETURN changes nothing: a currently
retained original edge is not cut, and a currently missing one is not filled. -/
theorem original_old_edge_unchanged {G H : CH.Digraph} {V U : Finset ℕ} {v a b : ℕ}
    (original_free : QFree G V 3) (hUV : U ⊆ V) (hvV : v ∈ V) (hvU : v ∉ U)
    (ha : a ∈ U) (hb : b ∈ U) (old : G a b = true) :
    originalReturn G H U v a b = true ↔ H a b = true := by
  have guard : a ∉ outN G U v ∨ b ∉ parents G U v := by
    by_cases hay : a ∈ outN G U v
    · right
      intro hbx
      exact original_no_cross original_free hUV hvV hay hbx old
    · exact Or.inl hay
  change star H U (parents G U v) (outN G U v) v a b = true ↔ _
  rw [star_old_edge hvU ha hb]
  exact and_iff_left guard

/-- Necessary for ANY 3-free graph retaining both declared original star edges.
Thus an old Y-to-X blocker cannot be kept for this full-star edit family. -/
theorem full_star_forces_cross_cut {G E : CH.Digraph} {U : Finset ℕ} {v y x : ℕ}
    (free : QFree E (insert v U) 3) (hy : y ∈ outN G U v) (hx : x ∈ parents G U v)
    (out_star : E v y = true) (in_star : E x v = true) : E y x ≠ true := by
  intro kept
  exact free v 3 (by omega) (by omega)
    (.step (Finset.mem_insert.mpr (Or.inr (mem_outN.mp hy).1)) out_star
      (.step (Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mp hx).1)) kept
        (.step (Finset.mem_insert_self _ _) in_star (.refl v))))
/-- The unconditional q=3 safe successor has two DISTINCT graph inputs. -/
theorem original_return_qfree {G H : CH.Digraph} {V U : Finset ℕ} {v : ℕ}
    (original_free : QFree G V 3) (current_free : QFree H U 3)
    (hUV : U ⊆ V) (hvV : v ∈ V) (hvU : v ∉ U) :
    QFree (originalReturn G H U v) (insert v U) 3 :=
  star_qfree current_free hvU (Finset.filter_subset _ _) outN_subset
    (original_banks_disjoint original_free hUV hvV)

theorem star_row_mem {H : CH.Digraph} {U X Y : Finset ℕ} {v u z : ℕ}
    (hv : v ∉ U) (hu : u ∈ U) :
    z ∈ outN (star H U X Y v) (insert v U) u ↔
      (z ∈ outN H U u ∧ (u ∉ Y ∨ z ∉ X)) ∨ (u ∈ X ∧ z = v) := by
  have huv : u ≠ v := fun he => hv (he ▸ hu)
  constructor
  · intro hz
    rcases star_edge.mp (mem_outN.mp hz).2 with old | new | new
    · exact Or.inl ⟨mem_outN.mpr ⟨old.2.1,old.2.2.1⟩,old.2.2.2⟩
    · exact Or.inr new
    · exact (huv new.1).elim
  · rintro (⟨old,guard⟩ | ⟨hx,rfl⟩)
    · exact mem_outN.mpr ⟨Finset.mem_insert.mpr (Or.inr (mem_outN.mp old).1),
        star_edge.mpr (Or.inl ⟨hu,(mem_outN.mp old).1,(mem_outN.mp old).2,guard⟩)⟩
    · exact mem_outN.mpr ⟨Finset.mem_insert_self _ _,star_edge.mpr (Or.inr (Or.inl ⟨hx,rfl⟩))⟩

theorem restored_row {H : CH.Digraph} {U X Y : Finset ℕ} {v : ℕ}
    (hv : v ∉ U) (hX : X ⊆ U) (hY : Y ⊆ U) :
    outN (star H U X Y v) (insert v U) v = Y := by
  ext z
  rw [mem_outN, star_outgoing hv hX]
  constructor
  · exact And.right
  · intro hz
    exact ⟨Finset.mem_insert.mpr (Or.inr (hY hz)),hz⟩

theorem parent_row {H : CH.Digraph} {U X Y : Finset ℕ} {v x : ℕ}
    (hv : v ∉ U) (hX : X ⊆ U) (disj : Disjoint X Y) (hx : x ∈ X) :
    outN (star H U X Y v) (insert v U) x = insert v (outN H U x) := by
  have hnotY : x ∉ Y := Finset.disjoint_left.mp disj hx
  ext z
  rw [star_row_mem hv (hX hx)]
  simp [hx,hnotY,or_comm]

theorem head_row {H : CH.Digraph} {U X Y : Finset ℕ} {v y : ℕ}
    (hv : v ∉ U) (hY : Y ⊆ U) (disj : Disjoint X Y) (hy : y ∈ Y) :
    outN (star H U X Y v) (insert v U) y = outN H U y \ X := by
  have hnotX : y ∉ X := fun hx => Finset.disjoint_left.mp disj hx hy
  ext z
  rw [star_row_mem hv (hY hy)]
  simp [hy,hnotX]

theorem other_row {H : CH.Digraph} {U X Y : Finset ℕ} {v u : ℕ}
    (hv : v ∉ U) (hu : u ∈ U) (hx : u ∉ X) (hy : u ∉ Y) :
    outN (star H U X Y v) (insert v U) u = outN H U u := by
  ext z
  rw [star_row_mem hv hu]
  simp [hx,hy]

/-- Full physical row ledger; Y loses its actual current H heads in X. -/
theorem star_exact_debits {H : CH.Digraph} {U X Y : Finset ℕ} {v : ℕ}
    (hv : v ∉ U) (hX : X ⊆ U) (hY : Y ⊆ U) (disj : Disjoint X Y) :
    (outN (star H U X Y v) (insert v U) v).card = Y.card ∧
    (∀ x ∈ X, (outN (star H U X Y v) (insert v U) x).card = (outN H U x).card + 1) ∧
    (∀ y ∈ Y, (outN (star H U X Y v) (insert v U) y).card +
      (outN H U y ∩ X).card = (outN H U y).card) ∧
    ∀ u ∈ U, u ∉ X → u ∉ Y → outN (star H U X Y v) (insert v U) u = outN H U u := by
  refine ⟨congrArg Finset.card (restored_row hv hX hY),?_,?_,fun _ hu hx hy => other_row hv hu hx hy⟩
  · intro x hx
    rw [parent_row hv hX disj hx]
    exact Finset.card_insert_of_notMem (fun h => hv (outN_subset h))
  · intro y hy
    rw [head_row hv hY disj hy]
    exact Finset.card_sdiff_add_card_inter _ _

/-- Combined original/current interface: safety, nonoriginality of every cut,
and the full debit vector. Funding of old Y rows is NOT concluded. -/
theorem original_return_transition {G H : CH.Digraph} {V U : Finset ℕ} {v : ℕ}
    (original_free : QFree G V 3) (current_free : QFree H U 3)
    (hUV : U ⊆ V) (hvV : v ∈ V) (hvU : v ∉ U) :
    let X := parents G U v
    let Y := outN G U v
    QFree (originalReturn G H U v) (insert v U) 3 ∧
    (∀ y ∈ Y, ∀ x ∈ X, H y x = true → G y x ≠ true) ∧
    (outN (originalReturn G H U v) (insert v U) v).card = Y.card ∧
    (∀ x ∈ X, (outN (originalReturn G H U v) (insert v U) x).card = (outN H U x).card + 1) ∧
    (∀ y ∈ Y, (outN (originalReturn G H U v) (insert v U) y).card +
      (outN H U y ∩ X).card = (outN H U y).card) ∧
    ∀ u ∈ U, u ∉ X → u ∉ Y → outN (originalReturn G H U v) (insert v U) u = outN H U u := by
  refine ⟨original_return_qfree original_free current_free hUV hvV hvU,?_,?_⟩
  · intro y hy x hx _
    exact original_no_cross original_free hUV hvV hy hx
  · exact star_exact_debits hvU (Finset.filter_subset _ _) outN_subset
      (original_banks_disjoint original_free hUV hvV)

end LeanCH.BR.DotOriginalStarReturn
open LeanCH.BR.DotOriginalStarReturn in
#print axioms star_qfree
open LeanCH.BR.DotOriginalStarReturn in
#print axioms original_banks_disjoint
open LeanCH.BR.DotOriginalStarReturn in
#print axioms original_no_cross
open LeanCH.BR.DotOriginalStarReturn in
#print axioms original_old_edge_unchanged
open LeanCH.BR.DotOriginalStarReturn in
#print axioms full_star_forces_cross_cut
open LeanCH.BR.DotOriginalStarReturn in
#print axioms original_return_qfree
open LeanCH.BR.DotOriginalStarReturn in
#print axioms star_exact_debits
open LeanCH.BR.DotOriginalStarReturn in
#print axioms original_return_transition
