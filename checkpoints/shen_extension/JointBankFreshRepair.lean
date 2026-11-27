import checkpoints.shen_extension.JointBankPairLoad
import checkpoints.shen_extension.JointBankFreshDiamond
import checkpoints.shen_extension.dot_tensor_research.DotOriginalStarReturn_20261118

/-! Simultaneously restore a chosen set of short rows using a common fresh
target. Every cut is charged to the row where it is made. -/

namespace LeanCH.BR.JointFreshRepair
open Finset BRq2 BRq3 BR45 BypassBankReplay

/-- Delete the edge from the target to the exception, and the old edges
from its other successors into the selected rows. Add the selected shortcuts. -/
def edit (D : CH.Digraph) (J : Finset ℕ) (z e : ℕ) : CH.Digraph := fun a b =>
  decide ((a ∈ J ∧ b = z) ∨
    (D a b = true ∧ ¬ (a = z ∧ b = e) ∧ ¬ (D z a = true ∧ a ≠ e ∧ b ∈ J)))

/-- The remaining short rows are exactly the original short rows outside
`J`. All return paths through the exceptional successor are cut at the
target. Every other affected successor loses at most one outgoing arc. -/
theorem repair_rows {D : CH.Digraph} {U J : Finset ℕ} {z e t : ℕ}
    (free : QFree D U 3) (zU : z ∈ U)
    (fresh : ∀ c ∈ J, c ≠ z ∧ D c z ≠ true ∧ D z c ≠ true)
    (need : ∀ c ∈ J, t ≤ (outN D U c).card+1)
    (spareZ : t+1 ≤ (outN D U z).card)
    (spare : ∀ w ∈ outN D U z, t+1 ≤ (outN D U w).card)
    (cost : ∀ w ∈ outN D U z, w ≠ e → (outN D U w ∩ J).card ≤ 1) :
    QFree (edit D J z e) U 3 ∧
      U.filter (fun u => (outN (edit D J z e) U u).card < t) =
        U.filter (fun u => (outN D U u).card < t) \ J := by
  classical
  let E := edit D J z e
  have zero : D z z ≠ true := loopfree free (by decide) zU
  have zj : z ∉ J := fun h => (fresh z h).1 rfl
  have fromZ {b} (ed : E z b = true) : D z b = true ∧ b ≠ e := by
    simpa [E,edit,zj,zero] using ed
  have fromNext {w c} (zw : D z w = true) (we : w ≠ e) (cj : c ∈ J) :
      E w c ≠ true := by
    have cz := (fresh c cj).1
    simp [E,edit,cz,zw,we,cj]
  have split {a b} (ed : E a b = true) : D a b = true ∨ a ∈ J ∧ b = z := by
    rcases of_decide_eq_true ed with h | ⟨old,_,_⟩
    · exact Or.inr h
    · exact Or.inl old
  have back {c w} (cj : c ∈ J) (zw : E z w = true) (wc : E w c = true) : False :=
    fromNext (fromZ zw).1 (fromZ zw).2 cj wc
  constructor
  · apply DotOriginalStarReturn.qfree_three_of_tests
    · intro a au aa
      rcases split aa with h | ⟨aj,az⟩
      · exact loopfree free (by decide) au h
      · exact (fresh _ aj).1 az
    · intro a au b bu ab ba
      rcases split ab with old | ⟨aj,rfl⟩
      · rcases split ba with old' | ⟨bj,rfl⟩
        · exact digonfree free (by decide) au bu old old'
        · exact (fresh _ bj).2.2 old
      · exact (fresh _ aj).2.2 (fromZ ba).1
    · intro a au b bu c cu ab bc ca
      rcases split ab with old | ⟨aj,rfl⟩
      · rcases split bc with old' | ⟨bj,rfl⟩
        · rcases split ca with old'' | ⟨cj,rfl⟩
          · exact free a 3 (by decide) (by decide) (.step bu old (.step cu old' (.step au old'' (.refl _))))
          · exact back cj ab bc
        · exact back bj ca ab
      · exact back aj bc ca
  · have rows (u) : outN E U u =
        if u ∈ J then insert z (outN D U u) else
        if u = z then (outN D U u).erase e else
        if D z u = true ∧ u ≠ e then outN D U u \ J else outN D U u := by
      by_cases member : u ∈ J
      · obtain ⟨uz,_,zu⟩ := fresh u member
        ext b
        by_cases bz : b=z <;> simp [E,edit,mem_outN,member,uz,zu,bz,zU]
      · by_cases uz : u=z
        · subst u
          ext b
          simp [E,edit,mem_outN,member,zero,and_assoc,and_left_comm,and_comm]
        · ext b
          by_cases cut : D z u = true ∧ u ≠ e
          · simp [E,edit,mem_outN,member,uz,cut.1,cut.2,and_assoc]
          · simp [E,edit,mem_outN,member,uz,cut,← and_assoc]
    ext u
    by_cases uj : u ∈ J
    · obtain ⟨_,uz,_⟩ := fresh _ uj
      have new := rows u
      rw [ite_eq_left uj] at new
      have zoff : z ∉ outN D U u := fun h => uz (mem_outN.mp h).2
      have paid := need u uj
      have enough : t ≤ (outN E U u).card := by rw [new,card_insert_of_notMem zoff]; omega
      simp [E] at enough
      simp [uj,not_lt_of_ge enough]
    · by_cases uz : u=z
      · subst u
        have row := rows z
        rw [ite_eq_right zj,ite_eq_left rfl] at row
        have floor : t ≤ (outN E U z).card := by
          rw [row]
          by_cases hit : e ∈ outN D U z
          · rw [card_erase_of_mem hit]; omega
          · rw [erase_eq_of_notMem hit]; omega
        change _ ∈ U.filter (fun v => (outN E U v).card < t) ↔ _
        simp [zj,not_lt_of_ge floor,show ¬(outN D U z).card<t by omega]
      · by_cases active : D z u=true ∧ u≠e
        · by_cases uU : u ∈ U
          · have hit : u ∈ outN D U z := mem_outN.mpr ⟨uU,active.1⟩
            have paid := spare u hit
            have cut := cost u hit active.2
            have bill := card_sdiff_add_card_inter (outN D U u) J
            have floor : t ≤ (outN E U u).card := by
              rw [rows,ite_eq_right uj,ite_eq_right uz,ite_eq_left active]; omega
            change _ ∈ U.filter (fun v => (outN E U v).card < t) ↔ _
            simp [uj,not_lt_of_ge floor,show ¬(outN D U u).card<t by omega]
          · simp [uU]
        · have same := rows u
          rw [ite_eq_right uj,ite_eq_right uz,ite_eq_right active] at same
          change _ ∈ U.filter (fun v => (outN E U v).card < t) ↔ _
          simp [uj,same]

#print axioms repair_rows

/-- In the two-label deletion every successor of the common target misses
both deleted labels and so retains the full original degree. -/
theorem repair_deleted_pair {D : CH.Digraph} {V J : Finset ℕ} {s p h z e : ℕ}
    (free : QFree D V 3) (reg : OutEq s D V) (hs : 2 ≤ s) (pv : p ∈ V) (hv : h ∈ V)
    (ph : p ≠ h) (zv : z ∈ V) (pz : D p z=true) (hz : D h z=true)
    (selected : J ⊆ inN D V p ∩ inN D V h) (missing : ∀ c ∈ J, D c z ≠ true)
    (cost : ∀ w ∈ outN D (V \ {p,h}) z, w ≠ e →
        (outN D (V \ {p,h}) w ∩ J).card ≤ 1) :
    let U := V \ {p,h}
    QFree (edit D J z e) U 3 ∧
      U.filter (fun c => (outN (edit D J z e) U c).card < s-1) =
        (inN D V p ∩ inN D V h) \ J := by
  classical
  let B : Finset ℕ := {p,h}
  let U := V \ B
  have inside : B ⊆ V := insert_subset pv (singleton_subset_iff.mpr hv)
  have znp : z ≠ p := fun eq => loopfree free (by decide) pv (eq ▸ pz)
  have znh : z ≠ h := fun eq => loopfree free (by decide) hv (eq ▸ hz)
  have zu : z ∈ U := mem_sdiff.mpr ⟨zv,by simp [B,znp,znh]⟩
  have tri (a b c) (av : a ∈ V) (bv : b ∈ V) (cv : c ∈ V)
      (ab : D a b=true) (bc : D b c=true) : D c a ≠ true := by
    intro ca
    exact free a 3 (by decide) (by decide) (.step bv ab (.step cv bc (.step av ca (.refl _))))
  have split (u) (uv : u ∈ V) : (outN D U u).card + (outN D B u).card = s := by
    have count := card_outN_union (D := D) (show Disjoint B U from disjoint_sdiff) u
    rw [show B ∪ U = V from union_sdiff_of_subset inside,reg _ uv] at count
    omega
  have full (u) (uv : u ∈ V) (noP : D u p ≠ true) (noH : D u h ≠ true) :
      (outN D U u).card = s := by
    have none : outN D B u = ∅ := by
      ext b
      simp only [mem_outN,B,mem_insert,mem_singleton,notMem_empty,iff_false]
      rintro ⟨rfl | rfl, ed⟩
      · exact noP ed
      · exact noH ed
    have eq := split u uv
    simpa only [none,card_empty,add_zero] using eq
  have fresh (c) (cj : c ∈ J) : c ≠ z ∧ D c z ≠ true ∧ D z c ≠ true := by
    obtain ⟨cv,cp⟩ := mem_inN.mp (mem_inter.mp (selected cj)).1
    exact ⟨fun eq => digonfree free (by decide) pv zv pz (eq ▸ cp),
      missing c cj,tri c p z cv pv zv cp pz⟩
  have need (c) (cj : c ∈ J) : s-1 ≤ (outN D U c).card+1 := by
    have cv := (mem_inN.mp (mem_inter.mp (selected cj)).1).1
    have count := split c cv
    have lim := card_le_card (outN_subset : outN D B c ⊆ B)
    have size : B.card=2 := card_pair ph
    omega
  have atZ := full z zv (digonfree free (by decide) pv zv pz)
    (digonfree free (by decide) hv zv hz)
  have funds (w) (wm : w ∈ outN D U z) : (s-1)+1 ≤ (outN D U w).card := by
    obtain ⟨wu,zw⟩ := mem_outN.mp wm
    have wv := (mem_sdiff.mp wu).1
    rw [full w wv (tri p z w pv zv wv pz zw) (tri h z w hv zv wv hz zw)]
    omega
  obtain ⟨ok,eq⟩ := repair_rows (t := s-1) (free.mono_set (show U ⊆ V from sdiff_subset))
    zu fresh need (by omega) funds cost
  refine ⟨ok,eq.trans ?_⟩
  have old := short_rows_eq_jointParents free (by decide) reg pv hv ph hs
  change U.filter _ = _ at old
  rw [old]
  have parents : jointParents D V p h = inN D V p ∩ inN D V h := by
    ext w; simp [jointParents,mem_inN,and_left_comm,and_comm]
  rw [parents]

/-- Each individually selected fresh row can be restored with every other
row's previous short status intact. -/
theorem repair_one {D : CH.Digraph} {V : Finset ℕ} {s p h z c : ℕ}
    (free : QFree D V 3) (reg : OutEq s D V) (hs : 2 ≤ s) (pv : p ∈ V) (hv : h ∈ V)
    (ph : p ≠ h) (zv : z ∈ V) (pz : D p z=true) (hz : D h z=true)
    (row : c ∈ inN D V p ∩ inN D V h) (miss : D c z ≠ true) :
    let U := V \ {p,h}
    QFree (edit D {c} z z) U 3 ∧
      U.filter (fun v => (outN (edit D {c} z z) U v).card < s-1) =
        (inN D V p ∩ inN D V h).erase c := by
  simpa only [sdiff_singleton_eq_erase] using repair_deleted_pair (J := {c}) (e := z) free reg hs pv hv ph zv pz hz
    (singleton_subset_iff.mpr row) (by simpa using miss) (by
      intro w _ _
      simpa using card_le_card (inter_subset_right :
        outN D (V \ {p,h}) w ∩ {c} ⊆ {c}))

#print axioms repair_deleted_pair
#print axioms repair_one

/-- If the edited carrier would be a lower-degree counterexample, at least
one selected short row already sees the target, or two separate successors
of the target would each have to lose at least two outgoing arcs. -/
theorem target_obstruction {D : CH.Digraph} {V : Finset ℕ} {s p h z : ℕ}
    (free : QFree D V 3) (reg : OutEq s D V) (hs : 2 ≤ s) (pv : p ∈ V) (hv : h ∈ V)
    (ph : p ≠ h) (zv : z ∈ V) (pz : D p z=true) (hz : D h z=true)
    (room : V.card = 3*(s-1)+2) (none : BypassRepair.NoHost 3 (s-1)) :
    let U := V \ {p,h}
    let S := inN D V p ∩ inN D V h
    (∃ c ∈ S, D c z = true) ∨
      ∃ w ∈ outN D U z, ∃ v ∈ outN D U z, w ≠ v ∧
        2 ≤ (outN D U w ∩ S).card ∧ 2 ≤ (outN D U v ∩ S).card := by
  classical
  let B : Finset ℕ := {p,h}
  let U := V \ B
  let S := inN D V p ∩ inN D V h
  by_cases direct : ∃ c ∈ S, D c z = true
  · exact Or.inl direct
  right
  by_contra absent
  change (¬∃ w ∈ outN D U z, ∃ v ∈ outN D U z, w ≠ v ∧
    2 ≤ (outN D U w ∩ S).card ∧ 2 ≤ (outN D U v ∩ S).card) at absent
  have existsCut : ∃ e, ∀ w ∈ outN D U z, w ≠ e → (outN D U w ∩ S).card ≤ 1 := by
    by_cases blocker : ∃ e ∈ outN D U z, 2 ≤ (outN D U e ∩ S).card
    · obtain ⟨e,ez,debt⟩ := blocker
      refine ⟨e,?_⟩
      intro w wz we
      by_contra bad
      exact absent ⟨w,wz,e,ez,we,by omega,debt⟩
    · exact ⟨z,fun w wz _ => by
        by_contra bad
        exact blocker ⟨w,wz,by omega⟩⟩
  obtain ⟨e,cost⟩ := existsCut
  obtain ⟨safe,short⟩ := repair_deleted_pair (s := s) (J := S) free reg hs pv hv ph zv pz hz
    (Subset.rfl) (fun c cs edge => direct ⟨c,cs,edge⟩) cost
  change U.filter (fun u => (outN (edit D S z e) U u).card < s-1) = S \ S at short
  have noShort : U.filter (fun u => (outN (edit D S z e) U u).card < s-1) = ∅ :=
    short.trans (Finset.sdiff_eq_empty_iff_subset.mpr (Subset.rfl))
  have size : U.card = 3*(s-1) := by
    rw [show U.card = V.card - B.card from card_sdiff_of_subset (insert_subset pv (singleton_subset_iff.mpr hv)),
      show B.card = 2 from card_pair ph,room]; omega
  have live : U.Nonempty := card_pos.mp (by omega)
  apply none (edit D S z e) U live size.le safe
  intro u uU
  by_contra low
  have hit : u ∈ U.filter (fun v => (outN (edit D S z e) U v).card < s-1) :=
    mem_filter.mpr ⟨uU,by omega⟩
  rw [noShort] at hit
  exact notMem_empty _ hit

#print axioms target_obstruction

/-- At the two-label triangle boundary a single bank and target serve more
than `s/8` marked rows. For every one of those rows, the actual edit
decreases the set of deficient labels by precisely that singleton. -/
theorem exists_repairable_bank {s : ℕ} (X : ShenMinimumOrder.Source 3 s)
    (reg : OutEq s X.D X.V) (hs : 8 ≤ s) (order : X.V.card = 3*(s-1)+2) :
    ∃ m : Cell, Marked X m ∧ JointShort X m ∧ ∃ h ∈ X.V,
      m.parent ≠ h ∧ m.bank = {m.parent,h} ∧ X.D h m.target = true ∧
      let U := X.V \ m.bank
      let S := U.filter (fun v => (outN X.D U v).card < s-1)
      let J := freshRows X.D X.V m.parent h m.target
      m.x ∈ J ∧ J ⊆ S ∧ s < 8*J.card ∧ ∀ c ∈ J,
        let E := edit X.D {c} m.target m.target
        QFree E U 3 ∧ U.filter (fun v => (outN E U v).card < s-1) = S.erase c := by
  classical
  obtain ⟨m,mark,joint,h,hv,ph,bank,hz,xj,many,each⟩ := exists_fresh_marked_pair X reg hs order
  have pv := mark.sub mark.erased
  have zv := (mem_sdiff.mp mark.zu).1
  have original : (X.V \ m.bank).filter (fun v => (outN X.D (X.V \ m.bank) v).card < s-1) =
      inN X.D X.V m.parent ∩ inN X.D X.V h := by
    rw [bank,short_rows_eq_jointParents X.free (by decide) reg pv hv ph (by omega)]
    ext w
    simp only [jointParents,mem_inN,mem_inter]
    tauto
  refine ⟨m,mark,joint,h,hv,ph,bank,hz,xj,?_,many,?_⟩
  · rw [original]
    exact filter_subset _ _
  · intro c cj
    obtain ⟨row,miss⟩ := mem_filter.mp cj
    have paid := repair_one X.free reg (by omega) pv hv ph zv mark.pz hz row miss
    dsimp only
    rw [original,bank]
    exact paid

#print axioms exists_repairable_bank
end LeanCH.BR.JointFreshRepair

