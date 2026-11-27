import checkpoints.shen_extension.TripleBankMenu

/-! Inheriting common targets after the three-hit row replaces one bank label. -/
namespace LeanCH.BR.TripleBank
open Finset BRq2 BRq3 BR45

private theorem count_insert {D : CH.Digraph} {T : Finset ℕ} {a c : ℕ} (ct : c ∉ T) :
    (outN D (insert c T) a).card = (outN D T a).card + if D a c = true then 1 else 0 := by
  classical
  by_cases ac : D a c = true
  · have eq : outN D (insert c T) a = insert c (outN D T a) := by
      ext v
      simp only [mem_outN,mem_insert]
      constructor
      · rintro ⟨rfl | h,ed⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨h,ed⟩
      · rintro (rfl | h)
        · exact ⟨Or.inl rfl,ac⟩
        · exact ⟨Or.inr h.1,h.2⟩
    rw [eq,card_insert_of_notMem (fun h => ct (outN_subset h))]
    simp [ac]
  · have eq : outN D (insert c T) a = outN D T a := by
      ext v
      simp only [mem_outN,mem_insert]
      constructor
      · rintro ⟨rfl | h,ed⟩
        · exact (ac ed).elim
        · exact ⟨h,ed⟩
      · exact fun h => ⟨Or.inr h.1,h.2⟩
    simp [eq,ac]

/-- T is the pair remaining in the bank, and k is its released label.
The rotated short rows form a nonempty set of unit deficits. If it is a
singleton, its row covers every target shared by c and T. -/
theorem rotation {D : CH.Digraph} {V T P : Finset ℕ} {k c s : ℕ}
    (safe : QFree D V 3) (reg : OutEq s D V) (hs : 2 ≤ s) (order : V.card = 3*s)
    (none : BypassRepair.NoHost 3 (s-1))
    (sub : insert k T ⊆ V) (kt : k ∉ T) (two : T.card = 2)
    (cu : c ∈ V \ insert k T) (ck : D c k = true)
    (lone : ∀ a ∈ V \ insert k T, a ≠ c → (outN D (insert k T) a).card ≤ 1)
    (good : (outN D T k).card ≤ 1)
    (pv : P ⊆ V) (common : ∀ b ∈ insert c T, P ⊆ outN D V b) :
    let U := V \ insert c T
    let R := U.filter (fun a => D a c = true ∧ (outN D T a).Nonempty)
    R.Nonempty ∧
      (∀ a ∈ U, (a ∈ R ↔ (outN D (insert c T) a).card = 2) ∧
        (a ∉ R → (outN D (insert c T) a).card ≤ 1)) ∧
      (∀ a ∈ R, a ≠ k ∧ D a k ≠ true ∧ D k a ≠ true) ∧
      ∀ a, R = {a} → P ⊆ outN D V a := by
  classical
  intro U R
  obtain ⟨cv,cb⟩ := mem_sdiff.mp cu
  have ct : c ∉ T := fun h => cb (mem_insert_of_mem h)
  have kv := sub (mem_insert_self _ _)
  have kc : D k c ≠ true := digonfree safe (by decide) cv kv ck
  have bank : insert c T ⊆ V := insert_subset cv (fun _ h => sub (mem_insert_of_mem h))
  have three : (insert c T).card = 3 := by rw [card_insert_of_notMem ct,two]
  have size : U.card = 3*(s-1) := by
    change (V \ insert c T).card = _; rw [card_sdiff_of_subset bank,three,order]; omega
  have original {a} (au : a ∈ U) (ak : a ≠ k) : a ∈ V \ insert k T ∧ a ≠ c := by
    obtain ⟨av,off⟩ := mem_sdiff.mp au
    exact ⟨mem_sdiff.mpr ⟨av,fun h => (mem_insert.mp h).elim ak (fun ht => off (mem_insert_of_mem ht))⟩,
      fun eq => off (eq ▸ mem_insert_self c T)⟩
  have cap {a} (au : a ∈ U) : (outN D T a).card ≤ 1 := by
    by_cases ak : a = k
    · simpa [ak] using good
    · obtain ⟨av,ac⟩ := original au ak
      have bound := lone a av ac
      rw [count_insert kt] at bound
      omega
  have spec (a) (au : a ∈ U) : (a ∈ R ↔ (outN D (insert c T) a).card = 2) ∧
      (a ∉ R → (outN D (insert c T) a).card ≤ 1) := by
    have h := cap au
    have char : a ∈ R ↔ D a c = true ∧ 0 < (outN D T a).card := by
      change (_ ∈ U.filter _) ↔ _
      rw [mem_filter]
      exact ⟨fun h => ⟨h.2.1,card_pos.mpr h.2.2⟩,fun h => ⟨au,h.1,card_pos.mp h.2⟩⟩
    rw [char,count_insert ct]
    by_cases ac : D a c = true
    · simp only [ac,ite_true,true_and]
      omega
    · rw [ite_eq_right ac]
      refine ⟨⟨fun ar => (ac ar.1).elim,fun n => False.elim (by omega)⟩,fun _ => by omega⟩
  have degree {a} (au : a ∈ U) :
      (outN D U a).card + (outN D (insert c T) a).card = s := by
    have eq := card_outN_union (D := D) (show Disjoint (insert c T) U from disjoint_sdiff) a
    rw [union_sdiff_of_subset bank,reg a (mem_sdiff.mp au).1] at eq
    omega
  have live : R.Nonempty := by
    by_contra empty
    apply none D U (card_pos.mp (by omega)) size.le (safe.mono_set sdiff_subset)
    intro a au
    have low := (spec a au).2 (fun h => empty ⟨a,h⟩)
    have eq := degree au
    omega
  refine ⟨live,spec,?_,?_⟩
  · intro a am
    obtain ⟨au,ac,hit⟩ := mem_filter.mp am
    have ak : a ≠ k := fun eq => kc (eq ▸ ac)
    obtain ⟨av,ne⟩ := original au ak
    refine ⟨ak,?_,fun ka => safe a 3 (by decide) (by decide)
      (.step cv ac (.step kv ck (.step (mem_sdiff.mp au).1 ka (.refl _))))⟩
    intro ed
    have bound := lone a av ne
    rw [count_insert kt,ite_eq_left ed] at bound
    have pos := card_pos.mpr hit
    omega
  · intro a single z zp
    have am : a ∈ R := single ▸ mem_singleton_self _
    have au := (mem_filter.mp am).1
    have twoHits := (spec a au).1.mp am
    have hit := card_pos.mp (show 0 < (outN D (insert c T) a).card by omega)
    obtain ⟨E,ok,gain,rest⟩ := single_menu safe reg bank pv common au hit
    by_contra no
    have zm : z ∈ rowMenu D U P a := mem_union_left _ (mem_sdiff.mpr ⟨zp,
      fun m => no (mem_outN.mpr ⟨pv zp,(mem_outN.mp m).2⟩)⟩)
    have pos := card_pos.mpr (show (rowMenu D U P a).Nonempty from ⟨z,zm⟩)
    apply none E U (card_pos.mp (by omega)) size.le ok
    intro v vu
    by_cases va : v = a
    · subst v
      change (outN E U a).card = (outN D U a).card + (rowMenu D U P a).card at gain
      have eq := degree au
      omega
    · have vm : v ∉ R := fun h => va (mem_singleton.mp (single ▸ h))
      have low := (spec v vu).2 vm
      have eq := degree vu
      have same := rest v vu va
      change min (s-1) (outN E U v).card = min (s-1) (outN D U v).card at same
      omega

/-- With three or more tight predecessors, some legal rotation produces at
least two short rows and retains at least half of the indicated predecessors.
Here H may be any surviving predecessors of c with a head in the old bank. -/
theorem choose_rotation {D : CH.Digraph} {V B H : Finset ℕ} {c : ℕ}
    (safe : QFree D V 3) (sub : B ⊆ V) (three : B.card = 3) (cu : c ∈ V \ B)
    (large : 3 ≤ H.card)
    (parents : ∀ a ∈ H, a ∈ V \ B ∧ D a c = true ∧ (outN D B a).Nonempty) :
    ∃ k ∈ B, (outN D (B.erase k) k).card ≤ 1 ∧
      let U := V \ insert c (B.erase k)
      let R := U.filter (fun a => D a c = true ∧ (outN D (B.erase k) a).Nonempty)
      2 ≤ R.card ∧ H.card ≤ 2*R.card := by
  classical
  let R (k : ℕ) := (V \ insert c (B.erase k)).filter
    (fun a => D a c = true ∧ (outN D (B.erase k) a).Nonempty)
  have live := card_pos.mp (show 0 < B.card by omega)
  obtain ⟨i,ib,sink⟩ := exists_sink (safe.mono_set sub) live three.le
  have pair : (B.erase i).card = 2 := by rw [card_erase_of_mem ib,three]
  have eb : B.erase i ⊆ B := erase_subset _ _
  obtain ⟨j,je,sink'⟩ := exists_sink (safe.mono_set (eb.trans sub))
    (card_pos.mp (show 0 < (B.erase i).card by omega)) (by omega)
  obtain ⟨ji,jb⟩ := mem_erase.mp je
  have smallI : (outN D (B.erase i) i).card ≤ 1 := by
    have empty : outN D (B.erase i) i = ∅ := eq_empty_iff_forall_notMem.mpr (fun b m =>
      sink b (eb (outN_subset m)) (mem_outN.mp m).2)
    simp [empty]
  have smallJ : (outN D (B.erase j) j).card ≤ 1 := by
    have only : outN D (B.erase j) j ⊆ {i} := by
      intro b bm
      apply mem_singleton.mpr
      by_contra bi
      exact sink' b (mem_erase.mpr ⟨bi,(mem_erase.mp (outN_subset bm)).2⟩) (mem_outN.mp bm).2
    simpa using card_le_card only
  have incl : H ⊆ R i ∪ R j := by
    intro a am
    obtain ⟨au,ac,b,bm⟩ := parents a am
    obtain ⟨bb,ab⟩ := mem_outN.mp bm
    have nc : a ≠ c := fun eq => loopfree safe (by decide) (mem_sdiff.mp cu).1 (eq ▸ ac)
    have retained {k} (diff : b ≠ k) : a ∈ R k := mem_filter.mpr
      ⟨mem_sdiff.mpr ⟨(mem_sdiff.mp au).1,fun h => (mem_insert.mp h).elim nc
        (fun he => (mem_sdiff.mp au).2 (mem_erase.mp he).2)⟩,
       ac,b,mem_outN.mpr ⟨mem_erase.mpr ⟨diff,bb⟩,ab⟩⟩
    by_cases bi : b = i
    · exact mem_union_right _ (retained (bi ▸ ji.symm))
    · exact mem_union_left _ (retained bi)
  have count := (card_le_card incl).trans (card_union_le (R i) (R j))
  by_cases bigger : (R i).card ≤ (R j).card
  · refine ⟨j,jb,smallJ,?_⟩
    change 2 ≤ (R j).card ∧ H.card ≤ 2*(R j).card
    omega
  · refine ⟨i,ib,smallI,?_⟩
    change 2 ≤ (R i).card ∧ H.card ≤ 2*(R i).card
    omega

#print axioms choose_rotation
#print axioms rotation
end LeanCH.BR.TripleBank
