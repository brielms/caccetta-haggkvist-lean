import checkpoints.shen_extension.PuncturedSeymourBank
import LeanCH.BR.BRWeightedInverseComparison

namespace LeanCH.BR.ShenPuncture
open BRq2 BRq3 Finset WeightedSD

/-- Full rows that point to at least one remaining tight row. -/
def payingParents (E : CH.Digraph) (U : Finset ℕ) (s : ℕ) :=
  U \ (tight E U s ∪ available E U s)

def Blocked (E : CH.Digraph) (U : Finset ℕ) (s : ℕ) : Prop :=
  ∀ t ∈ tight E U s, ∀ z ∈ U, E t z = true ∨ t ∈ ball E U z 2

private theorem row_insert {E : CH.Digraph} {U : Finset ℕ} {t z v : ℕ} (hz : z ∈ U) :
    outN (insertArc E t z) U v =
      if v=t then insert z (outN E U v) else outN E U v := by
  ext w
  by_cases h : v=t <;> by_cases k : w=z <;>
    simp_all [mem_outN, insertArc]

private theorem promote {E U A s n t z} (h : PunctureAt E U A s n)
    (ht : t ∈ tight E U s) (hz : z ∈ U) (missing : E t z ≠ true)
    (safe : t ∉ ball E U z 2) :
    PunctureAt (insertArc E t z) U A s n ∧
      tight (insertArc E t z) U s = (tight E U s).erase t := by
  obtain ⟨tu,td⟩ := mem_filter.mp ht
  have fresh : z ∉ outN E U t := fun hz' => missing (mem_outN.mp hz').2
  have paid : (outN (insertArc E t z) U t).card = s := by
    simpa [row_insert hz,card_insert_of_notMem fresh] using td
  have same {v : ℕ} (ne : v ≠ t) : outN (insertArc E t z) U v = outN E U v := by
    simp [row_insert hz,ne]
  have bank_ne {a} (ha : a∈A) : a ≠ t := fun eq => disjoint_left.mp h.heavy ha (eq ▸ ht)
  have small : tight (insertArc E t z) U s = (tight E U s).erase t := by
    ext v
    by_cases eq : v=t
    · subst v
      simp [tight,paid]
    · simp [tight,eq,same eq]
  refine ⟨⟨qfree_insertArc h.free ⟨t,tu⟩ ⟨z,hz⟩ safe,h.size,?_,?_,h.bank,h.width,?_,?_,?_⟩,small⟩
  · intro v hv
    by_cases eq : v=t
    · exact Or.inr (eq ▸ paid)
    · rw [same eq]
      exact h.degrees v hv
  · rw [small]
    exact (card_le_card (erase_subset _ _)).trans_lt h.few
  · rw [small]
    exact h.heavy.mono_right (erase_subset _ _)
  · intro a ha b hb
    rw [small] at hb
    simpa [insertArc,bank_ne ha] using h.rectangle a ha b (mem_of_mem_erase hb)
  · apply h.exits.trans
    apply card_le_card
    intro b hb
    obtain ⟨hit,out⟩ := mem_sdiff.mp hb
    obtain ⟨a,ha,ab⟩ := mem_biUnion.mp hit
    exact mem_sdiff.mpr ⟨mem_biUnion.mpr ⟨a,ha,(same (bank_ne ha)).symm ▸ ab⟩,out⟩

/-- The carrier, marked bank, exits and old arcs survive successive repairs. -/
theorem blocked_extension {E U A s n} (h : PunctureAt E U A s n) :
    ∃ F, PunctureAt F U A s n ∧ (∀ v w, E v w=true → F v w=true) ∧ Blocked F U s := by
  classical
  let attain (k : ℕ) := ∃ F, PunctureAt F U A s n ∧
    (∀ v w, E v w=true → F v w=true) ∧ (tight F U s).card=k
  have live : ∃ k, attain k := ⟨_,E,h,fun _ _ e => e,rfl⟩
  obtain ⟨F,hF,inc,num⟩ := Nat.find_spec live
  refine ⟨F,hF,inc,?_⟩
  intro t ht z hz
  by_contra! miss
  obtain ⟨hnext,smaller⟩ := promote hF ht hz miss.1 miss.2
  have next : attain (tight (insertArc F t z) U s).card :=
    ⟨_,hnext,fun v w e => insertArc_mono F t z v w (inc v w e),rfl⟩
  have le := Nat.find_min' live next
  rw [smaller,card_erase_of_mem ht,← num] at le
  have := card_pos.mpr ⟨t,ht⟩
  omega

/-- Every missing bank-to-tight pair in the reverse direction is covered by
the rectangle of an actual full parent, and a present arc forbids such a return. -/
theorem missing_iff_parent {E U A s n a t} (h : PunctureAt E U A s n) (blocked : Blocked E U s)
    (ha : a ∈ available E U s) (ht : t ∈ tight E U s) :
    E t a ≠ true ↔ ∃ p ∈ payingParents E U s, E a p=true ∧ E p t=true := by
  obtain ⟨au,an,sep⟩ := mem_filter.mp ha
  have tu := (mem_filter.mp ht).1
  constructor
  · intro miss
    obtain ⟨_,j,hj,w⟩ := mem_ball.mp ((blocked t ht a au).resolve_left miss)
    interval_cases j
    · cases w
      exact (an ht).elim
    · cases w with
      | step hv e w => cases w; exact (disjoint_left.mp sep (mem_outN.mpr ⟨hv,e⟩) ht).elim
    · cases w with
      | step hp ap w => cases w with
        | step _ pt w =>
          cases w
          refine ⟨_,mem_sdiff.mpr ⟨hp,?_⟩,ap,pt⟩
          intro bad
          rcases mem_union.mp bad with tp | avail
          · exact disjoint_left.mp sep (mem_outN.mpr ⟨hp,ap⟩) tp
          · exact disjoint_left.mp (mem_filter.mp avail).2.2 (mem_outN.mpr ⟨tu,pt⟩) ht
  · rintro ⟨p,hp,ap,pt⟩ ta
    exact h.free t 3 (by decide) le_rfl (.step au ta (.step (mem_sdiff.mp hp).1 ap
      (.step tu pt (.refl t))))

/-- Quantitative projection of the labelled rectangles for each tight row. -/
theorem return_rows_bound {E U A s n t} (h : PunctureAt E U A s n) (blocked : Blocked E U s)
    (ht : t∈tight E U s) :
    (available E U s).card + 1 ≤ s +
      ((available E U s).filter (fun a => ∃ p ∈ payingParents E U s,
        E a p=true ∧ E p t=true)).card := by
  classical
  let K := available E U s
  let R := K.filter (fun a => ∃ p ∈ payingParents E U s, E a p=true ∧ E p t=true)
  have cover : K ⊆ outN E U t ∪ R := by
    intro a ha
    by_cases e : E t a=true
    · exact mem_union_left _ (mem_outN.mpr ⟨(mem_filter.mp ha).1,e⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨ha,(missing_iff_parent h blocked ha ht).mp e⟩)
  have le := (card_le_card cover).trans (card_union_le _ _)
  have deg := (mem_filter.mp ht).2
  change K.card + 1 ≤ s + R.card
  omega

theorem blocked_source {D V s} (free : QFree D V 3) (live : V.Nonempty)
    (order : V.card ≤ 3*s) (degree : ∀ x∈V, s≤(outN D V x).card) :
    ∃ E U A, Puncture E U A s ∧ Blocked E U s := by
  obtain ⟨E,U,A,h⟩ := extract free live order degree
  obtain ⟨F,hF,_,stop⟩ := blocked_extension h
  exact ⟨F,U,A,hF,stop⟩

#print axioms blocked_source
#print axioms missing_iff_parent
#print axioms return_rows_bound

/-- In a least failing degree this applies to any nonempty induced set of
at most 3(s−1) vertices. Y is any allowed destination set containing X. -/
private theorem footprint {E : CH.Digraph} {U X : Finset ℕ} {s d cap : ℕ}
    (free : QFree E U 3) (lower : ∀ j<s, BankLaw j)
    (sub : X ⊆ U) (live : X.Nonempty) (small : X.card ≤ 3*(s-1))
    (rows : ∀ x∈X, ∃ Y : Finset ℕ, X ⊆ Y ∧ Y.card ≤ cap ∧
      d ≤ (outN E U x).card ∧ outN E U x ⊆ Y) :
    3*d + 2*X.card + 1 ≤ 3*cap := by
  let j := (X.card+2)/3
  have pos := live.card_pos
  have js : j<s := by dsimp [j]; omega
  obtain ⟨x,hx,short⟩ : ∃ x∈X, (outN E X x).card < j := by
    by_contra! high
    exact (bankLaw_iff j).mp (lower j js) E X (free.mono_set sub) live
      (by dsimp [j]; omega) high
  obtain ⟨Y,inside,capacity,deg,allowed⟩ := rows x hx
  have cover : outN E U x ⊆ outN E X x ∪ (Y \ X) := by
    intro w hw
    by_cases hit : w∈X
    · exact mem_union_left _ (mem_outN.mpr ⟨hit,(mem_outN.mp hw).2⟩)
    · exact mem_union_right _ (mem_sdiff.mpr ⟨allowed hw,hit⟩)
  have count := (card_le_card cover).trans (card_union_le _ _)
  have split := card_sdiff_add_card_eq_card inside
  dsimp [j] at short
  omega

def missingParents (E : CH.Digraph) (U : Finset ℕ) (s t : ℕ) :=
  (payingParents E U s).filter (fun p => E p t ≠ true)

/-- The two low rows may be different. Each spends its own tight label's
missing parents. Thus the maximum of the row counts suffices in both bounds. -/
theorem rowwise_parent_budget {E U A s n m} (h : PunctureAt E U A s n) (hn : n≤3*s)
    (blocked : Blocked E U s)
    (lower : ∀ j<s, BankLaw j) (S : Finset ℕ) (live : S.Nonempty)
    (st : S ⊆ tight E U s)
    (cap : ∀ v∈S, (missingParents E U s v).card ≤ m) :
    3*(tight E U s).card + 4*S.card + 9*(payingParents E U s).card + 8 + 9*(3*s-n) ≤
      12*s + 15*m := by
  classical
  let T := tight E U s
  let K := available E U s
  let P := payingParents E U s
  let M := missingParents E U s
  let B := K ∩ S.biUnion (outN E U)
  have tsub : T ⊆ U := filter_subset _ _
  have ksub : K ⊆ U := filter_subset _ _
  have ps : P ⊆ U := sdiff_subset
  have bk : B ⊆ K := inter_subset_left
  have dj : Disjoint T K := disjoint_left.mpr (fun _ ht hk => (mem_filter.mp hk).2.1 ht)
  have tu : T ∪ K ⊆ U := union_subset tsub ksub
  have partition := card_sdiff_add_card_eq_card tu
  change P.card + (T ∪ K).card = U.card at partition
  rw [card_union_of_disjoint dj] at partition
  have tpos := live.card_pos
  have sts := card_le_card st
  have few : T.card < s := h.few
  have order := h.size
  have ks : s ≤ K.card := h.available_card
  obtain ⟨t,ht⟩ := live
  have pp : P.Nonempty := by
    obtain ⟨a,ha,miss⟩ : ∃ a∈K, E t a ≠ true := by
      by_contra! allhit
      have sub : K ⊆ outN E U t := fun a ha => mem_outN.mpr ⟨ksub ha,allhit a ha⟩
      have r := card_le_card sub
      have eq := (mem_filter.mp (st ht)).2
      omega
    obtain ⟨p,hp,_⟩ := (missing_iff_parent h blocked ha (st ht)).mp miss
    exact ⟨p,hp⟩
  have ppos := pp.card_pos
  have part {w} (hw : w∈U) (nt : w∉T) (nk : w∉K) : w∈P := by
    exact mem_sdiff.mpr ⟨hw,fun bad => (mem_union.mp bad).elim nt nk⟩
  have ss : S.card ≤ 3*(s-1) := by change S.card ≤ T.card at sts; omega
  have first := footprint h.free lower (st.trans tsub) ⟨t,ht⟩ ss
    (cap := T.card+m+B.card) (d := s-1) (by
      intro v hv
      have deg := (mem_filter.mp (st hv)).2
      refine ⟨(T ∪ M v) ∪ B,fun z hz => mem_union_left _ (mem_union_left _ (st hz)),?_,by omega,?_⟩
      · have c1 := card_union_le (T ∪ M v) B
        have c2 := card_union_le T (M v)
        have lim : (M v).card ≤ m := cap v hv
        omega
      intro w hw
      have wu := outN_subset hw
      by_cases wk : w∈K
      · exact mem_union_right _ (mem_inter.mpr ⟨wk,mem_biUnion.mpr ⟨v,hv,hw⟩⟩)
      by_cases wt : w∈T
      · exact mem_union_left _ (mem_union_left _ wt)
      exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨part wu wt wk,
        digonfree h.free (by decide) (tsub (st hv)) wu (mem_outN.mp hw).2⟩)))
  have bs := card_le_card bk
  have stc : S.card ≤ T.card := sts
  have bound1 : 3*s+2*S.card ≤ 3*T.card+3*m+3*B.card+2 := by omega
  have bound2 : 3*s+2*B.card+1 ≤ 3*K.card+3*m := by
    by_cases bl : B.Nonempty
    · have small : B.card ≤ 3*(s-1) := by omega
      have second := footprint h.free lower (bk.trans ksub) bl small
        (cap := K.card+m) (d:=s) (by
          intro b hb
          have kb := bk hb
          have bu := ksub kb
          have deg := (h.degrees b bu).resolve_left (fun eq =>
            (mem_filter.mp kb).2.1 (mem_filter.mpr ⟨bu,eq⟩))
          obtain ⟨v,hv,vb⟩ := mem_biUnion.mp (mem_inter.mp hb).2
          refine ⟨K ∪ M v,fun z hz => mem_union_left _ (bk hz),?_,deg.ge,?_⟩
          · exact (card_union_le _ _).trans (Nat.add_le_add_left (cap v hv) _)
          intro w hw
          by_cases wk : w∈K
          · exact mem_union_left _ wk
          have wt : w∉T := fun hit => disjoint_left.mp (mem_filter.mp kb).2.2 hw hit
          refine mem_union_right _ (mem_filter.mpr ⟨part (outN_subset hw) wt wk,?_⟩)
          intro wv
          exact h.free v 3 (by decide) le_rfl (.step bu (mem_outN.mp vb).2
            (.step (outN_subset hw) (mem_outN.mp hw).2 (.step (tsub (st hv))
              wv (.refl v)))))
      omega
    · have bz : B.card=0 := by simp [not_nonempty_iff_eq_empty.mp bl]
      omega
  change 3*T.card+4*S.card+9*P.card+8+9*(3*s-n) ≤ 12*s+15*m
  omega

theorem common_parent_budget {E U A s n} (h : PunctureAt E U A s n) (hn : n≤3*s)
    (blocked : Blocked E U s) (lower : ∀ j<s, BankLaw j) (S C : Finset ℕ)
    (live : S.Nonempty) (st : S ⊆ tight E U s)
    (common : ∀ c∈C, ∀ v∈S, E c v=true) :
    3*(tight E U s).card + 4*S.card + 9*(payingParents E U s).card + 8 + 9*(3*s-n) ≤
      12*s + 15*((payingParents E U s) \ C).card := by
  apply rowwise_parent_budget h hn blocked lower S live st
  intro v hv
  apply card_le_card
  intro p hp
  exact mem_sdiff.mpr ⟨(mem_filter.mp hp).1,fun hc => (mem_filter.mp hp).2 (common p hc v hv)⟩

#print axioms common_parent_budget

/-- Distribution of the missing-parent counts. For S consisting of the j
smallest counts, m can be the j-th count, for every j in the same graph. -/
theorem tight_subset_distribution {E U A s n m} (h : PunctureAt E U A s n) (hn : n≤3*s)
    (stop : Blocked E U s) (lower : ∀ j<s, BankLaw j) (S : Finset ℕ)
    (live : S.Nonempty) (st : S ⊆ tight E U s)
    (cap : ∀ v∈S, (missingParents E U s v).card ≤ m) :
    15*s+4*S.card ≤ 6*(tight E U s).card+9*(available E U s).card+15*m+1 := by
  let T := tight E U s
  let K := available E U s
  let P := payingParents E U s
  have b := rowwise_parent_budget h hn stop lower S live st cap
  change 3*T.card+4*S.card+9*P.card+8+9*(3*s-n) ≤ 12*s+15*m at b
  have tu : T ∪ K ⊆ U := union_subset (filter_subset _ _) (filter_subset _ _)
  have dj : Disjoint T K := disjoint_left.mpr (fun _ ht hk => (mem_filter.mp hk).2.1 ht)
  have partition := card_sdiff_add_card_eq_card tu
  change P.card + (T ∪ K).card = U.card at partition
  rw [card_union_of_disjoint dj] at partition
  have ord := h.size
  change 15*s+4*S.card ≤ 6*T.card+9*K.card+15*m+1
  omega

#print axioms tight_subset_distribution

def partialParents (E : CH.Digraph) (U : Finset ℕ) (s : ℕ) :=
  (payingParents E U s).filter (fun p => ∃ t ∈ tight E U s, E p t ≠ true)

/-- One and the same tight row witnesses the entire distinct-parent deficit. -/
theorem labelled_parent_tradeoff {E U A s n} (h : PunctureAt E U A s n) (hn : n≤3*s)
    (stop : Blocked E U s) (lower : ∀ j<s, BankLaw j) (live : (tight E U s).Nonempty) :
    ∃ v∈tight E U s,
      15*s ≤ 2*(tight E U s).card+9*(available E U s).card+15*(missingParents E U s v).card+1 ∧
      13*s+1 ≤ 9*(available E U s).card+15*(missingParents E U s v).card := by
  classical
  let T := tight E U s
  let K := available E U s
  obtain ⟨v,hv,maxv⟩ := T.exists_max_image (fun w => (missingParents E U s w).card) live
  refine ⟨v,hv,?_⟩
  have budget := tight_subset_distribution h hn stop lower T live (Subset.refl _) maxv
  change 15*s+4*T.card ≤ 6*T.card+9*K.card+15*(missingParents E U s v).card+1 at budget
  have few : T.card < s := h.few
  change 15*s ≤ 2*T.card+9*K.card+15*(missingParents E U s v).card+1 ∧
    13*s+1 ≤ 9*K.card+15*(missingParents E U s v).card
  omega

theorem partial_parent_tradeoff {E U A s n} (h : PunctureAt E U A s n) (hn : n≤3*s)
    (stop : Blocked E U s) (lower : ∀ j<s, BankLaw j) (live : (tight E U s).Nonempty) :
    15*s ≤ 2*(tight E U s).card+9*(available E U s).card+15*(partialParents E U s).card+1 ∧
    13*s+1 ≤ 9*(available E U s).card+15*(partialParents E U s).card := by
  obtain ⟨v,hv,b₁,b₂⟩ := labelled_parent_tradeoff h hn stop lower live
  have sub : missingParents E U s v ⊆ partialParents E U s := fun p hp =>
    mem_filter.mpr ⟨(mem_filter.mp hp).1,v,hv,(mem_filter.mp hp).2⟩
  have le := card_le_card sub
  omega

theorem first_failure_partial {E U A s n} (h : PunctureAt E U A s n) (hn : n≤3*s)
    (stop : Blocked E U s) (lower : ∀ j<s, BankLaw j) (live : (tight E U s).Nonempty)
    (first : (available E U s).card=s) :
    4*s+1 ≤ 15*(partialParents E U s).card := by
  have b := (partial_parent_tradeoff h hn stop lower live).2
  rw [first] at b
  omega

/-- A single tight row forces a larger available bank at every degree. -/
theorem single_tight_bank {E U A s n} (h : PunctureAt E U A s n) (hn : n≤3*s)
    (stop : Blocked E U s) (lower : ∀ j<s, BankLaw j) (one : (tight E U s).card=1) :
    5*s ≤ 3*(available E U s).card+1 := by
  obtain ⟨t,ht⟩ := card_eq_one.mp one
  have live : (tight E U s).Nonempty := card_pos.mp (by omega)
  have noPartial : partialParents E U s = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro p hit
    obtain ⟨pp,z,hz,miss⟩ := mem_filter.mp hit
    obtain ⟨pu,neither⟩ := mem_sdiff.mp pp
    rw [ht] at hz
    have eq := mem_singleton.mp hz
    subst z
    apply neither
    apply mem_union_right
    refine mem_filter.mpr ⟨pu,fun tp => neither (mem_union_left _ tp),?_⟩
    rw [ht]
    exact disjoint_left.mpr (fun w hw iw => miss ((mem_singleton.mp iw) ▸ (mem_outN.mp hw).2))
  have bound := (partial_parent_tradeoff h hn stop lower live).1
  rw [one,noPartial,card_empty] at bound
  omega

#print axioms partial_parent_tradeoff
#print axioms labelled_parent_tradeoff
#print axioms first_failure_partial
#print axioms single_tight_bank

/-- Every pair whose deletion costs each retained tight row zero must be hit
twice by an outside row, since the reduced degree is already settled. -/
theorem pair_receipt {E U A s n t y} (h : PunctureAt E U A s n)
    (hn : n ≤ 3*s) (hs : 3≤s) (lower : BankLaw (s-1))
    (tu : t∈U) (yu : y∈U) (ne : y≠t)
    (intact : ∀ z∈tight E U s, z≠t → z≠y → E z t≠true ∧ E z y≠true) :
    ∃ p∈U, p≠t ∧ p≠y ∧ E p t=true ∧ E p y=true := by
  classical
  let pair : Finset ℕ := {t,y}
  let X := U \ pair
  have inside : pair ⊆ U := insert_subset tu (singleton_subset_iff.mpr yu)
  have width : pair.card=2 := by simp [pair,Ne.symm ne]
  have xx := card_sdiff_add_card_eq_card inside
  change X.card + pair.card = U.card at xx
  have aw := (card_le_card h.bank)
  rw [h.width] at aw
  have live : X.Nonempty := card_pos.mp (by omega)
  have order := h.size
  have sub : X ⊆ U := sdiff_subset
  by_contra none
  apply (bankLaw_iff _).mp lower E X (h.free.mono_set sub) live (by omega)
  intro z hz
  have zu := sub hz
  have zt : z≠t := fun eq => (mem_sdiff.mp hz).2 (by simp [pair,eq])
  have zy : z≠y := fun eq => (mem_sdiff.mp hz).2 (by simp [pair,eq])
  have conflict (e : E z t=true) (f : E z y=true) : False := by
    exact none ⟨z,zu,zt,zy,e,f⟩
  have lost : ((outN E U z) ∩ pair).card ≤ 1 := by
    apply card_le_one.mpr
    intro a ha b hb
    obtain ⟨za,pa⟩ := mem_inter.mp ha
    obtain ⟨zb,pb⟩ := mem_inter.mp hb
    simp only [pair,mem_insert,mem_singleton] at pa pb
    have ea := (mem_outN.mp za).2
    have eb := (mem_outN.mp zb).2
    rcases pa with rfl | rfl <;> rcases pb with rfl | rfl <;> first | rfl | exact (conflict ea eb).elim | exact (conflict eb ea).elim
  have row : outN E X z = outN E U z \ pair := by
    ext b
    simp only [mem_outN,X,mem_sdiff]
    tauto
  have split := card_sdiff_add_card_inter (outN E U z) pair
  rw [row]
  rcases h.degrees z zu with short | full
  · obtain ⟨noT,noY⟩ := intact z (mem_filter.mpr ⟨zu,short⟩) zt zy
    have zero : (outN E U z) ∩ pair = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro b hb
      obtain ⟨edge,pairHit⟩ := mem_inter.mp hb
      have e := (mem_outN.mp edge).2
      rcases mem_insert.mp pairHit with rfl | hit
      · exact noT e
      · exact noY ((mem_singleton.mp hit) ▸ e)
    rw [zero,card_empty] at split
    omega
  · omega

/-- With a single tight row its full parents dominate the remaining host. -/
theorem single_tight_common_parent {E U A s n t y} (h : PunctureAt E U A s n)
    (hn : n ≤ 3*s) (hs : 3≤s) (lower : BankLaw (s-1))
    (one : tight E U s = {t}) (yu : y∈U) (ne : y≠t) :
    ∃ p∈payingParents E U s, E p t=true ∧ E p y=true := by
  have ht : t∈tight E U s := by simp [one]
  have tu := (mem_filter.mp ht).1
  obtain ⟨p,pu,pt,_,et,ey⟩ := pair_receipt h hn hs lower tu yu ne (by
    intro z hz zt
    rw [one] at hz
    exact (zt (mem_singleton.mp hz)).elim)
  refine ⟨p,mem_sdiff.mpr ⟨pu,?_⟩,et,ey⟩
  intro hit
  rcases mem_union.mp hit with inT | inK
  · rw [one] at inT
    exact pt (mem_singleton.mp inT)
  · exact disjoint_left.mp (mem_filter.mp inK).2.2 (mem_outN.mpr ⟨tu,et⟩) ht

#print axioms single_tight_common_parent
#print axioms pair_receipt

/-- Deleting the sole tight row leaves minimum degree s−1. The original
order must therefore be the top order at this degree. -/
theorem single_tight_top_order {E U A s n t} (h : PunctureAt E U A s n)
    (hn : n≤3*s) (hs : 2≤s) (lower : BankLaw (s-1)) (one : tight E U s = {t}) :
    n=3*s := by
  have ht : t∈tight E U s := by simp [one]
  have tu := (mem_filter.mp ht).1
  let W := U.erase t
  have size : W.card=U.card-1 := card_erase_of_mem tu
  have base := card_le_card h.bank
  rw [h.width] at base
  have pos : W.Nonempty := card_pos.mp (by omega)
  have ord := h.size
  by_contra wrong
  apply (bankLaw_iff _).mp lower E W (h.free.mono_set (erase_subset _ _)) pos (by omega)
  intro x hx
  have xu : x∈U := mem_of_mem_erase hx
  have xt : x≠t := (mem_erase.mp hx).1
  have full := (h.degrees x xu).resolve_left (fun eq => xt (mem_singleton.mp
    (one ▸ (show x∈tight E U s from mem_filter.mpr ⟨xu,eq⟩))))
  have row : outN E W x = (outN E U x).erase t := by
    ext w
    simp only [W,mem_outN,mem_erase]
    tauto
  rw [row]
  by_cases hit : t∈outN E U x
  · rw [card_erase_of_mem hit,full]
  · rw [erase_eq_of_notMem hit,full]
    omega

#print axioms single_tight_top_order

/-- Domination gives each available row a parent and a grandparent in P.
The row can hit neither of them. A light row inside K converts these two
exclusions into a uniform lower bound, retaining the original order deficit. -/
theorem single_tight_parent_floor {E U A s n t} (h : PunctureAt E U A s n)
    (hn : n≤3*s) (hs : 3≤s) (lower : ∀ j<s, BankLaw j) (one : tight E U s = {t}) :
    9+(3*s-n) ≤ 2*(payingParents E U s).card := by
  let K := available E U s
  let P := payingParents E U s
  have ht : t∈tight E U s := by simp [one]
  have tu := (mem_filter.mp ht).1
  have ks : s≤K.card := h.available_card
  have kl : K.Nonempty := card_pos.mp (by omega)
  have kt {a} (ha : a∈K) : a≠t := fun eq => (mem_filter.mp ha).2.1 (eq ▸ ht)
  have pk {p} (hp : p∈P) : p∉K := fun hit => (mem_sdiff.mp hp).2 (mem_union_right _ hit)
  have pt {p} (hp : p∈P) : p≠t := fun eq =>
    (mem_sdiff.mp hp).2 (mem_union_left _ (eq ▸ ht))
  have low := lower (s-1) (by omega)
  have parents {y} (hy : y∈U) (yt : y≠t) := single_tight_common_parent h hn hs low one hy yt
  obtain ⟨a,ka⟩ := kl
  obtain ⟨p,pp,_⟩ := parents (mem_filter.mp ka).1 (kt ka)
  have pos : 0<P.card := card_pos.mpr ⟨p,pp⟩
  have partition := card_sdiff_add_card_eq_card
    (union_subset (filter_subset (fun v => (outN E U v).card+1=s) U) (show K ⊆ U from filter_subset _ _))
  change P.card + (tight E U s ∪ K).card = U.card at partition
  have disj : Disjoint (tight E U s) K :=
    disjoint_left.mpr (fun _ hit hk => (mem_filter.mp hk).2.1 hit)
  rw [card_union_of_disjoint disj,one,card_singleton] at partition
  have ord := h.size
  have bound := footprint h.free lower (show K⊆U from filter_subset _ _) ⟨a,ka⟩
    (by omega) (d:=s) (cap:=U.card-3) (by
      intro x hx
      have xu := (mem_filter.mp hx).1
      obtain ⟨b,hb,_,bx⟩ := parents xu (kt hx)
      obtain ⟨c,hc,_,cb⟩ := parents (mem_sdiff.mp hb).1 (pt hb)
      have bu := (mem_sdiff.mp hb).1
      have cu := (mem_sdiff.mp hc).1
      have cbne : c≠b := fun eq => loopfree h.free (by decide) bu (eq ▸ cb)
      let cut : Finset ℕ := {t,b,c}
      have sub : cut ⊆ U := insert_subset tu (insert_subset bu (singleton_subset_iff.mpr cu))
      have size : cut.card=3 := by simp [cut,Ne.symm (pt hb),Ne.symm (pt hc),Ne.symm cbne]
      have rest := card_sdiff_add_card_eq_card sub
      refine ⟨U \ cut,?_,by omega,?_,?_⟩
      · intro w hw
        refine mem_sdiff.mpr ⟨(mem_filter.mp hw).1,?_⟩
        simp only [cut,mem_insert,mem_singleton]
        rintro (rfl|rfl|rfl)
        · exact kt hw rfl
        · exact pk hb hw
        · exact pk hc hw
      · exact ((h.degrees x xu).resolve_left (fun eq =>
          (mem_filter.mp hx).2.1 (mem_filter.mpr ⟨xu,eq⟩))).ge
      · intro w hw
        refine mem_sdiff.mpr ⟨outN_subset hw,?_⟩
        simp only [cut,mem_insert,mem_singleton]
        rintro (rfl|rfl|rfl)
        · exact disjoint_left.mp (mem_filter.mp hx).2.2 hw ht
        · exact digonfree h.free (by decide) bu xu bx (mem_outN.mp hw).2
        · exact h.free _ 3 (by decide) le_rfl (.step bu cb (.step xu bx
            (.step cu (mem_outN.mp hw).2 (.refl _)))))
  change 9+(3*s-n) ≤ 2*P.card
  omega

#print axioms single_tight_parent_floor

theorem single_tight_window {E U A s n t} (h : PunctureAt E U A s n) (hn : n≤3*s)
    (hs : 3≤s) (stop : Blocked E U s) (lower : ∀ j<s, BankLaw j) (one : tight E U s={t}) :
    n=3*s ∧ 5≤(payingParents E U s).card ∧
      5*s≤3*(available E U s).card+1 ∧ (available E U s).card+7≤3*s := by
  have eq := single_tight_top_order h hn (by omega) (lower (s-1) (by omega)) one
  have floor := single_tight_parent_floor h hn hs lower one
  have bound := single_tight_bank h hn stop lower (by rw [one,card_singleton])
  have disj : Disjoint (tight E U s) (available E U s) :=
    disjoint_left.mpr (fun _ hit hk => (mem_filter.mp hk).2.1 hit)
  have tu : tight E U s ∪ available E U s ⊆ U := union_subset (filter_subset _ _) (filter_subset _ _)
  have partition := card_sdiff_add_card_eq_card tu
  change (payingParents E U s).card + (tight E U s ∪ available E U s).card = U.card at partition
  rw [card_union_of_disjoint disj,one,card_singleton] at partition
  have ord := h.size
  omega

#print axioms single_tight_window

/-- Across degrees, any triangle counterexample supplies this least-degree
instance. Its proper-degree footprint tests therefore need no extra assumption. -/
theorem least_degree_blocked_source {D V s} (free : QFree D V 3) (live : V.Nonempty)
    (order : V.card ≤ 3*s) (degree : ∀ x∈V, s≤(outN D V x).card) :
    ∃ d ≤ s, (∀ j<d, BankLaw j) ∧ ∃ n ≤ 3*d, ∃ E U A,
      PunctureAt E U A d n ∧ Blocked E U d ∧ (tight E U d).Nonempty ∧
      ∃ v∈tight E U d, 13*d+1 ≤ 9*(available E U d).card+15*(missingParents E U d v).card := by
  classical
  have fails : ¬BankLaw s := fun law => (bankLaw_iff s).mp law D V free live order degree
  have existsFail : ∃ j, ¬BankLaw j := ⟨s,fails⟩
  let d := Nat.find existsFail
  have bad : ¬BankLaw d := Nat.find_spec existsFail
  rw [bankLaw_iff] at bad
  push Not at bad
  obtain ⟨F,W,fw,lw,sw,deg,_⟩ := bad
  let host (n : ℕ) := ∃ (F : CH.Digraph) (W : Finset ℕ), QFree F W 3 ∧
    W.Nonempty ∧ W.card=n ∧ ∀ x∈W, d≤(outN F W x).card
  have hosts : ∃ n, host n := ⟨_,F,W,fw,lw,rfl,deg⟩
  let n := Nat.find hosts
  have nw : n ≤ W.card := Nat.find_min' hosts (show host W.card from ⟨F,W,fw,lw,rfl,deg⟩)
  obtain ⟨G,V',fg,vg,num,gd⟩ := Nat.find_spec hosts
  obtain ⟨E,U,A,h⟩ := extract_at_order fg vg (by rw [num]; exact nw.trans sw) gd
  rw [num] at h
  obtain ⟨H,punct,_,stop⟩ := blocked_extension h
  have low : ∀ j<d, BankLaw j := fun j hj => not_not.mp (Nat.find_min existsFail hj)
  have tightLive : (tight H U d).Nonempty := by
    by_contra empty
    have full : ∀ v∈U, d ≤ (outN H U v).card := by
      intro v hv
      exact ((punct.degrees v hv).resolve_left (fun eq =>
        empty ⟨v,mem_filter.mpr ⟨hv,eq⟩⟩)).ge
    have spos : 0<d := by have := punct.few; omega
    have ulive := (card_pos.mp (punct.width ▸ spos) : A.Nonempty).mono punct.bank
    have less : U.card<n := by have := punct.size; omega
    exact Nat.find_min hosts less ⟨H,U,punct.free,ulive,rfl,full⟩
  obtain ⟨v,hv,_,bill⟩ := labelled_parent_tradeoff punct (nw.trans sw) stop low tightLive
  exact ⟨d,Nat.find_min' existsFail fails,low,n,nw.trans sw,H,U,A,punct,stop,tightLive,v,hv,bill⟩

#print axioms least_degree_blocked_source
end LeanCH.BR.ShenPuncture
