import checkpoints.shen_extension.TripleBankCuts

/-! The full menu for arbitrary cuts when new arcs can leave only one row. -/
namespace LeanCH.BR.TripleBank
open Finset BRq2 BRq3 BR45

def tightParents (D : CH.Digraph) (U : Finset ℕ) (c t : ℕ) : Finset ℕ :=
  (inN D U c).filter (fun w => (outN D U w).card ≤ t)

def fullMenu (D : CH.Digraph) (U : Finset ℕ) (c t : ℕ) : Finset ℕ :=
  ((U.erase c) \ outN D U c).filter (fun v =>
    t ≤ (outN D U v \ insert c (tightParents D U c t)).card)

/-- All affordable heads are attainable at once, even if an old arc into c
must be reversed. Every other row keeps at least the stipulated floor. -/
theorem attain_full_menu {D : CH.Digraph} {U : Finset ℕ} {c t : ℕ}
    (safe : QFree D U 3) (cu : c ∈ U)
    (others : ∀ v ∈ U, v ≠ c → t ≤ (outN D U v).card) :
    ∃ E : CH.Digraph, QFree E U 3 ∧
      outN E U c = outN D U c ∪ fullMenu D U c t ∧ ∀ a ∈ U, a ≠ c →
        outN E U a ⊆ outN D U a ∧ t ≤ (outN E U a).card := by
  classical
  let H := tightParents D U c t
  let M := fullMenu D U c t
  let E : CH.Digraph := fun a b =>
    if a = c then decide (D a b = true ∨ b ∈ M)
    else if a ∈ M then decide (D a b = true ∧ b ∉ insert c H)
    else if a ∈ H then D a b else decide (D a b = true ∧ b ≠ c)
  have inside {v} (vm : v ∈ M) : v ∈ U ∧ v ≠ c :=
    ⟨(mem_erase.mp (mem_sdiff.mp (mem_filter.mp vm).1).1).2,
      (mem_erase.mp (mem_sdiff.mp (mem_filter.mp vm).1).1).1⟩
  have cm : c ∉ M := fun h => (inside h).2 rfl
  have sub {a b} (ac : a ≠ c) (ed : E a b = true) : D a b = true := by
    by_cases am : a ∈ M <;> by_cases ah : a ∈ H <;> simp [E,ac,am,ah] at ed <;> tauto
  have split {a b} (ed : E a b = true) : D a b = true ∨ a = c ∧ b ∈ M := by
    by_cases ac : a = c
    · subst a; simpa [E] using ed
    · exact Or.inl (sub ac ed)
  have parents {w} (edge : E w c = true) : w ∈ H := by
    by_contra wh
    by_cases wc : w = c
    · subst w; simp [E,cm,loopfree safe (by decide) cu] at edge
    · by_cases wm : w ∈ M <;> simp [E,wc,wh,wm] at edge
  have clear {v b} (vm : v ∈ M) (blocked : b ∈ insert c H) : E v b ≠ true := by
    intro ed
    have h : decide (D v b = true ∧ b ∉ insert c H) = true := by
      simpa only [E,ite_eq_right (inside vm).2,ite_eq_left vm] using ed
    exact (of_decide_eq_true h).2 blocked
  have back {v w} (vm : v ∈ M) (vw : E v w = true) (wc : E w c = true) : False :=
    clear vm (mem_insert_of_mem (parents wc)) vw
  refine ⟨E,?_,?_,?_⟩
  · apply DotOriginalStarReturn.qfree_three_of_tests
    · intro a au aa
      rcases split aa with ed | ⟨rfl,am⟩
      · exact loopfree safe (by decide) au ed
      · exact cm am
    · intro a au b bu ab ba
      rcases split ab with old | ⟨rfl,bm⟩
      · rcases split ba with old' | ⟨rfl,am⟩
        · exact digonfree safe (by decide) au bu old old'
        · exact clear am (mem_insert_self _ _) ab
      · exact clear bm (mem_insert_self _ _) ba
    · intro a au b bu w wu ab bw wa
      rcases split ab with old | ⟨rfl,bm⟩
      · rcases split bw with old' | ⟨rfl,wm⟩
        · rcases split wa with old'' | ⟨rfl,am⟩
          · exact safe a 3 (by decide) (by decide)
              (.step bu old (.step wu old' (.step au old'' (.refl _))))
          · exact back am ab bw
        · exact back wm wa ab
      · exact back bm bw wa
  · ext v; simp only [E,mem_outN,ite_true,decide_eq_true_eq,mem_union]
    have := fun h : v ∈ M => (inside h).1
    change (_ ∧ (_ ∨ v ∈ M)) ↔ (_ ∧ _) ∨ v ∈ M
    tauto
  · intro a au ac
    refine ⟨fun v m => mem_outN.mpr ⟨(mem_outN.mp m).1,sub ac (mem_outN.mp m).2⟩,?_⟩
    by_cases am : a ∈ M
    · have row : outN E U a = outN D U a \ insert c H := by
        ext v; simp [E,ac,am,mem_outN,and_assoc]
      rw [row]; exact (mem_filter.mp am).2
    by_cases ah : a ∈ H
    · have row : outN E U a = outN D U a := by ext v; simp [E,ac,am,ah,mem_outN]
      rw [row]; exact others a au ac
    · have row : outN E U a = (outN D U a).erase c := by
        ext v; simp [E,ac,am,ah,mem_outN,and_comm,and_left_comm,and_assoc]
      rw [row]
      by_cases ed : c ∈ outN D U a
      · have slack : t < (outN D U a).card := by
          by_contra! tight
          exact ah (mem_filter.mpr ⟨mem_inN.mpr ⟨au,(mem_outN.mp ed).2⟩,tight⟩)
        rw [card_erase_of_mem ed]; omega
      · rw [erase_eq_of_notMem ed]; exact others a au ac

/-- A target outside the menu cannot be gained by any edit restricted to
one adding row, irrespective of how many old arcs it cuts. -/
theorem full_menu_necessary {D E : CH.Digraph} {U : Finset ℕ} {c t : ℕ}
    (old : QFree D U 3) (safe : QFree E U 3) (cu : c ∈ U)
    (limited : ∀ a ∈ U, a ≠ c → outN E U a ⊆ outN D U a ∧ t ≤ (outN E U a).card) :
    outN E U c \ outN D U c ⊆ fullMenu D U c t := by
  classical
  intro v vm
  obtain ⟨vc,missing⟩ := mem_sdiff.mp vm
  obtain ⟨vu,cv⟩ := mem_outN.mp vc
  have ne : v ≠ c := fun eq => loopfree safe (by decide) cu (eq ▸ cv)
  refine mem_filter.mpr ⟨mem_sdiff.mpr ⟨mem_erase.mpr ⟨ne,vu⟩,missing⟩,
    (limited v vu ne).2.trans (card_le_card ?_)⟩
  intro w vw
  refine mem_sdiff.mpr ⟨(limited v vu ne).1 vw,?_⟩
  intro wh
  rcases mem_insert.mp wh with rfl | tight
  · exact digonfree safe (by decide) cu vu cv (mem_outN.mp vw).2
  · obtain ⟨parent,cap⟩ := mem_filter.mp tight
    obtain ⟨wu,wc⟩ := mem_inN.mp parent
    have wn : w ≠ c := fun eq => loopfree old (by decide) cu (eq ▸ wc)
    have equal := eq_of_subset_of_card_le (limited w wu wn).1 (cap.trans (limited w wu wn).2)
    have kept : c ∈ outN E U w := equal ▸ mem_outN.mpr ⟨cu,wc⟩
    exact safe c 3 (by decide) (by decide)
      (.step vu cv (.step wu (mem_outN.mp vw).2 (.step cu (mem_outN.mp kept).2 (.refl _))))

/-- On a carrier forbidden by the lower quota, the full menu still leaves
the sole deficient row below quota. -/
theorem full_menu_obstruction {D : CH.Digraph} {U : Finset ℕ} {c t : ℕ}
    (safe : QFree D U 3) (cu : c ∈ U) (small : U.card ≤ 3*t)
    (none : BypassRepair.NoHost 3 t)
    (others : ∀ v ∈ U, v ≠ c → t ≤ (outN D U v).card) :
    (outN D U c).card + (fullMenu D U c t).card < t := by
  classical
  obtain ⟨E,ok,row,rest⟩ := attain_full_menu safe cu others
  have dis : Disjoint (outN D U c) (fullMenu D U c t) := disjoint_left.mpr
    (fun _ h m => (mem_sdiff.mp (mem_filter.mp m).1).2 h)
  by_contra! big
  apply none E U ⟨c,cu⟩ small ok
  intro a au
  by_cases ac : a = c
  · subst a; simpa only [row,card_union_of_disjoint dis] using big
  · exact (rest a au ac).2

#print axioms full_menu_obstruction
#print axioms attain_full_menu
#print axioms full_menu_necessary
end LeanCH.BR.TripleBank

