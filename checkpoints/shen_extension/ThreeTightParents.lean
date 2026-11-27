import checkpoints.shen_extension.LoneRowBudget
import checkpoints.shen_extension.SharedRepairHead
import checkpoints.shen_extension.RotatedBank
import checkpoints.shen_extension.BypassCloneCover

/-! A clean head pays one tight predecessor of a lone deficient row while
leaving all the other predecessors' outgoing rows unchanged. -/
namespace LeanCH.BR.TripleBank
open Finset BRq2 BRq3 BR45

theorem promote_parent_with_edges {D : CH.Digraph} {U : Finset ℕ} {a c k t : ℕ}
    (safe : QFree D U 3) (cu : c ∈ U) (ku : k ∈ U) (ck : D c k = true)
    (parents : a ∈ tightParents D U c t) (miss : D a k ≠ true)
    (spare : ∀ w ∈ outN D U k, t < (outN D U w).card)
    (others : ∀ v ∈ U, v ≠ c → t ≤ (outN D U v).card) :
    ∃ E : CH.Digraph, QFree E U 3 ∧ (∀ v ∈ U, v ≠ c → t ≤ (outN E U v).card) ∧
      tightParents E U c t = (tightParents D U c t).erase a ∧
      (∀ v ∈ inN D U c, v ≠ a → outN E U v = outN D U v) ∧
      ∀ v z, E v z = true → D v z = true ∨ v = a ∧ z = k := by
  classical
  obtain ⟨parent,cap⟩ := mem_filter.mp parents
  obtain ⟨au,ac⟩ := mem_inN.mp parent
  have an : a ≠ c := fun h => loopfree safe (by decide) cu (h ▸ ac)
  have ak : a ≠ k := fun h => digonfree safe (by decide) cu ku ck (h ▸ ac)
  have ka : D k a ≠ true := fun ka => safe c 3 (by decide) (by decide)
    (.step ku ck (.step au ka (.step cu ac (.refl _))))
  have nc (w) (wm : w ∈ outN D U k) : D w c ≠ true := fun wc => safe c 3 (by decide) (by decide)
    (.step ku ck (.step (outN_subset wm) (mem_outN.mp wm).2 (.step cu wc (.refl _))))
  let A (v : ℕ) : Finset ℕ := if v = a then {k} else ∅
  let C (v : ℕ) : Finset ℕ := if v ∈ outN D U k then {a} else ∅
  let E := patch D A C
  have added {v z} (m : z ∈ A v) : v = a ∧ z = k := by
    by_cases eq : v = a
    · exact ⟨eq,by simpa [A,eq] using m⟩
    · simp [A,eq] at m
  obtain ⟨ok,rows⟩ := patch_certificate (A := A) (C := C) safe
    (fun v _ z m => by
      obtain ⟨va,zk⟩ := added m
      subst v; subst z
      exact ⟨ku,ak.symm,miss,ka⟩)
    (fun v _ z m w wu zw _ => by
      obtain ⟨va,zk⟩ := added m
      subst v; subst z
      exact Or.inr (by simp [C,mem_outN.mpr ⟨wu,zw⟩]))
    (fun v _ z m _ m' => False.elim (ak ((added m').1.symm.trans (added m).2)))
  have akOut : a ∉ outN D U k := fun h => ka (mem_outN.mp h).2
  have paid : (outN E U a).card = (outN D U a).card+1 := by
    simpa [E,A,C,akOut] using rows a au
  have same {v} (va : v ≠ a) (out : v ∉ outN D U k) : outN E U v = outN D U v := by
    have noCut : C v = ∅ := by simp [C,out]
    ext z; simp [E,patch,A,va,noCut,mem_outN]
  have keep (v) (vm : v ∈ inN D U c) (va : v ≠ a) := same va (fun h => nc v h (mem_inN.mp vm).2)
  have kc : k ≠ c := fun h => loopfree safe (by decide) cu (h ▸ ck)
  have parentsEq : inN E U c = inN D U c := by
    ext v
    have noNew : c ∉ A v := fun h => kc (added h).2.symm
    have noCut : c ∉ C v := by
      by_cases wk : v ∈ outN D U k <;> simp [C,wk,Ne.symm an]
    simp [E,patch,mem_inN,noNew,noCut]
  have edges (v z) (ed : E v z = true) : D v z = true ∨ v = a ∧ z = k :=
    (of_decide_eq_true ed : z ∈ A v ∨ D v z = true ∧ z ∉ C v).elim
      (fun m => Or.inr (added m)) (fun h => Or.inl h.1)
  refine ⟨E,ok,?_,?_,keep,edges⟩
  · intro v vu vc
    by_cases va : v = a
    · subst v; have := others a au an; omega
    by_cases wk : v ∈ outN D U k
    · have eq := rows v vu
      change (outN E U v).card = _ at eq
      simp [A,C,va,wk,sdiff_singleton_eq_erase] at eq
      have gap := spare v wk
      by_cases hit : a ∈ outN D U v
      · rw [card_erase_of_mem hit] at eq; omega
      · rw [erase_eq_of_notMem hit] at eq; omega
    · rw [same va wk]; exact others v vu vc
  · ext v
    simp only [tightParents,parentsEq,mem_filter,mem_erase]
    by_cases va : v = a
    · subst v; have := others a au an; omega
    by_cases vm : v ∈ inN D U c
    · rw [keep v vm va]; tauto
    · tauto

theorem promote_parent {D : CH.Digraph} {U : Finset ℕ} {a c k t : ℕ}
    (safe : QFree D U 3) (cu : c ∈ U) (ku : k ∈ U) (ck : D c k = true)
    (parents : a ∈ tightParents D U c t) (miss : D a k ≠ true)
    (spare : ∀ w ∈ outN D U k, t < (outN D U w).card)
    (others : ∀ v ∈ U, v ≠ c → t ≤ (outN D U v).card) :
    ∃ E : CH.Digraph, QFree E U 3 ∧ (∀ v ∈ U, v ≠ c → t ≤ (outN E U v).card) ∧
      tightParents E U c t = (tightParents D U c t).erase a ∧
      ∀ v ∈ inN D U c, v ≠ a → outN E U v = outN D U v := by
  obtain ⟨E,ok,rest,eq,keep,_⟩ := promote_parent_with_edges safe cu ku ck parents miss spare others
  exact ⟨E,ok,rest,eq,keep⟩

private theorem two_tight {D : CH.Digraph} {U : Finset ℕ} {q c k t : ℕ}
    (safe : QFree D U q) (cu : c ∈ U) (ku : k ∈ U) (kc : k ≠ c)
    (none : BypassRepair.NoHost q t) (small : U.card ≤ q*t) (large : 2 ≤ t)
    (others : ∀ v ∈ U, v ≠ c → t ≤ (outN D U v).card) :
    2 ≤ (tightParents D U c t).card := by
  obtain ⟨y,yu,_,yc,tight,_⟩ := BypassCloneCover.misses_copy none small safe cu ku kc others
  obtain ⟨_,_,v,vu,_,vy,vc,vt,_⟩ := BypassCloneCover.another_parent
    (BypassCloneCover.separation none small safe cu others) cu yc tight large
  have ys : y ∈ tightParents D U c t := mem_filter.mpr ⟨mem_inN.mpr ⟨yu,yc⟩,tight.le⟩
  have vs : v ∈ tightParents D U c t := mem_filter.mpr ⟨mem_inN.mpr ⟨vu,vc⟩,vt.le⟩
  exact (card_pair vy).symm ▸ card_le_card (insert_subset vs (singleton_subset_iff.mpr ys))

/-- A single c → k with a spare unit on every successor of k forces three
distinct tight parents, provided all other rows meet the lower quota. -/
theorem three_tight {D : CH.Digraph} {U : Finset ℕ} {c k t : ℕ}
    (safe : QFree D U 3) (cu : c ∈ U) (ku : k ∈ U) (ck : D c k = true)
    (none : BypassRepair.NoHost 3 t) (small : U.card ≤ 3*t) (large : 2 ≤ t)
    (others : ∀ v ∈ U, v ≠ c → t ≤ (outN D U v).card)
    (spare : ∀ w ∈ outN D U k, t < (outN D U w).card) :
    3 ≤ (tightParents D U c t).card := by
  have kc : k ≠ c := fun h => loopfree safe (by decide) cu (h ▸ ck)
  obtain ⟨a,au,_,ac,eq,miss⟩ := BypassCloneCover.misses_copy none small safe cu ku kc others
  have am : a ∈ tightParents D U c t := mem_filter.mpr ⟨mem_inN.mpr ⟨au,ac⟩,eq.le⟩
  obtain ⟨E,ok,rest,new,_⟩ := promote_parent safe cu ku ck am miss spare others
  have bound := two_tight ok cu ku kc none small large rest
  rw [new,card_erase_of_mem am] at bound
  omega

/-- The common targets actually furnished by the selected triple include
a head of c whose surviving successors each have a spare unit. -/
theorem three_tight_on_lone_frontier {D : CH.Digraph} {V B P : Finset ℕ} {s c : ℕ}
    (safe : QFree D V 3) (reg : OutEq s D V) (hs : 3 ≤ s) (order : V.card = 3*s)
    (none : BypassRepair.NoHost 3 (s-1)) (sub : B ⊆ V) (three : B.card = 3)
    (pv : P ⊆ V) (many : 2 ≤ P.card) (common : ∀ b ∈ B, P ⊆ outN D V b)
    (cu : c ∈ V \ B) (lone : ∀ a ∈ V \ B, a ≠ c → (outN D B a).card ≤ 1)
    (menu : (rowMenu D (V \ B) P c).card ≤ 1) :
    3 ≤ (tightParents D (V \ B) c (s-1)).card := by
  classical
  let U := V \ B
  have inside {k} (kp : k ∈ P) : k ∈ U := mem_sdiff.mpr ⟨pv kp,fun kb =>
    loopfree safe (by decide) (pv kp) (mem_outN.mp (common k kb kp)).2⟩
  have inherited : ∃ k ∈ P, D c k = true := by
    by_contra! miss
    have inc : P ⊆ rowMenu D U P c := fun k kp => mem_union_left _ (mem_sdiff.mpr
      ⟨kp,fun edge => miss k kp (mem_outN.mp edge).2⟩)
    have lim := (card_le_card inc).trans menu
    omega
  obtain ⟨k,kp,ck⟩ := inherited
  have size : U.card = 3*(s-1) := by
    change (V \ B).card = _; rw [card_sdiff_of_subset sub,order,three]; omega
  have split (a) (au : a ∈ U) : (outN D U a).card + (outN D B a).card = s := by
    have h := card_outN_union (D := D) (show Disjoint B U from disjoint_sdiff) a
    rw [union_sdiff_of_subset sub,reg a (mem_sdiff.mp au).1] at h
    omega
  apply three_tight (safe.mono_set sdiff_subset) cu (inside kp) ck none size.le (by omega)
  · intro v vu vc
    have eq := split v vu
    have low := lone v vu vc
    change s-1 ≤ (outN D U v).card
    omega
  · intro w wm
    obtain ⟨wu,kw⟩ := mem_outN.mp wm
    have no : outN D B w = ∅ := eq_empty_iff_forall_notMem.mpr (fun b h => by
      obtain ⟨bb,wb⟩ := mem_outN.mp h
      exact safe b 3 (by decide) (by decide)
        (.step (pv kp) (mem_outN.mp (common b bb kp)).2 (.step (mem_sdiff.mp wu).1 kw
          (.step (sub bb) wb (.refl _)))))
    have eq := split w wu
    rw [no,card_empty,add_zero] at eq
    change s-1 < (outN D U w).card
    omega

/-- The same selected bank from the existing top-order dichotomy now
has at least three tight predecessors in its lone three-hit alternative. -/
theorem top_parent_frontier {D : CH.Digraph} {V : Finset ℕ} {s : ℕ}
    (safe : QFree D V 3) (reg : OutEq s D V) (hs : 7 ≤ s) (order : V.card = 3*s)
    (none : BypassRepair.NoHost 3 (s-1)) :
    ∃ P ⊆ V, 2 ≤ P.card ∧ ∃ B ⊆ V, B.card = 3 ∧ (∀ b ∈ B, P ⊆ outN D V b) ∧
      let U := V \ B
      let S := U.filter (fun a => 2 ≤ (outN D B a).card)
      (∀ a ∈ S, ∃ k ∈ P, D a k ≠ true) ∧
      (2 ≤ S.card ∨ ∃ c, S = {c} ∧ (outN D B c).card = 3 ∧ (rowMenu D U P c).card = 1 ∧
        3 ≤ (tightParents D U c (s-1)).card) := by
  classical
  obtain ⟨P,pv,pc,B,bv,bc,common,miss,_,front⟩ := top_repair_frontier safe reg hs order none
  refine ⟨P,pv,pc,B,bv,bc,common,miss,?_⟩
  rcases front with several | ⟨c,single,hits,menu⟩
  · exact Or.inl several
  · refine Or.inr ⟨c,single,hits,menu,?_⟩
    have cs : c ∈ (V \ B).filter (fun a => 2 ≤ (outN D B a).card) := single ▸ mem_singleton_self _
    apply three_tight_on_lone_frontier safe reg (by omega) order none bv bc pv pc common
      (mem_filter.mp cs).1 _ menu.le
    intro a au ac
    by_contra! many
    exact ac (mem_singleton.mp (single ▸ (mem_filter.mpr ⟨au,by omega⟩)))

/-- On the actual lone three-hit frontier one can choose a new bank with
at least two unit deficits, a single fresh head for every one, and a
nonempty inherited set of common targets. That fresh head cannot retain
the floor if its successors must cut every return to the short rows. -/
theorem rotated_lone_frontier {D : CH.Digraph} {V B P : Finset ℕ} {s c : ℕ}
    (safe : QFree D V 3) (reg : OutEq s D V) (hs : 3 ≤ s) (order : V.card = 3*s)
    (none : BypassRepair.NoHost 3 (s-1)) (sub : B ⊆ V) (three : B.card = 3)
    (pv : P ⊆ V) (many : 2 ≤ P.card) (common : ∀ b ∈ B, P ⊆ outN D V b)
    (cu : c ∈ V \ B) (allB : (outN D B c).card = 3)
    (lone : ∀ a ∈ V \ B, a ≠ c → (outN D B a).card ≤ 1)
    (menu : (rowMenu D (V \ B) P c).card = 1) :
    let I := P ∩ outN D V c
    I.Nonempty ∧ (P \ I).card ≤ 1 ∧ ∃ k ∈ B,
      let T := B.erase k
      let U := V \ insert c T
      let R := U.filter (fun a => D a c = true ∧ (outN D T a).Nonempty)
      (outN D T k).card ≤ 1 ∧ (∀ b ∈ insert c T, I ⊆ outN D V b) ∧
      2 ≤ R.card ∧ (tightParents D (V \ B) c (s-1)).card ≤ 2*R.card ∧
      (∀ a ∈ U, (a ∈ R ↔ (outN D (insert c T) a).card = 2) ∧
        (a ∉ R → (outN D (insert c T) a).card ≤ 1)) ∧
      (∀ a ∈ R, a ≠ k ∧ D a k ≠ true ∧ D k a ≠ true) ∧
      (retainable D U R k (s-1)).card < s-1 := by
  classical
  intro I
  have incl : P \ I ⊆ rowMenu D (V \ B) P c := by
    intro z zm
    obtain ⟨zp,zi⟩ := mem_sdiff.mp zm
    exact mem_union_left _ (mem_sdiff.mpr ⟨zp,fun h => zi
      (mem_inter.mpr ⟨zp,mem_outN.mpr ⟨pv zp,(mem_outN.mp h).2⟩⟩)⟩)
  have bound := (card_le_card incl).trans menu.le
  have live : I.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty.mp h,sdiff_empty] at bound
    omega
  let H := tightParents D (V \ B) c (s-1)
  have big := three_tight_on_lone_frontier safe reg hs order none sub three pv many common cu lone menu.le
  have hp (a) (am : a ∈ H) : a ∈ V \ B ∧ D a c = true ∧ (outN D B a).Nonempty := by
    obtain ⟨inc,low⟩ := mem_filter.mp am
    obtain ⟨au,ac⟩ := mem_inN.mp inc
    have eq := card_outN_union (D := D) (show Disjoint B (V \ B) from disjoint_sdiff) a
    rw [union_sdiff_of_subset sub,reg a (mem_sdiff.mp au).1] at eq
    exact ⟨au,ac,card_pos.mp (by omega)⟩
  obtain ⟨k,kb,good,count,half⟩ := choose_rotation safe sub three cu big hp
  let T := B.erase k
  let U := V \ insert c T
  let R := U.filter (fun a => D a c = true ∧ (outN D T a).Nonempty)
  have kT : k ∉ T := notMem_erase _ _
  have Bform : insert k T = B := insert_erase kb
  have two : T.card = 2 := by change (B.erase k).card = _; rw [card_erase_of_mem kb,three]
  have common' (b) (bm : b ∈ insert c T) : I ⊆ outN D V b := by
    rcases mem_insert.mp bm with rfl | bt
    · exact inter_subset_right
    · exact inter_subset_left.trans (common b (mem_erase.mp bt).2)
  have same : outN D B c = B := eq_of_subset_of_card_le outN_subset (by omega)
  have km : k ∈ outN D B c := by rw [same]; exact kb
  have ck := (mem_outN.mp km).2
  obtain ⟨_,spec,fresh,_⟩ := rotation (T := T) (P := I) safe reg (by omega) order none
    (Bform ▸ sub) kT two (Bform ▸ cu) ck (Bform ▸ lone) good (inter_subset_left.trans pv) common'
  refine ⟨live,bound,k,kb,good,common',count,half,spec,fresh,?_⟩
  have kv := sub kb
  have nc : k ≠ c := fun eq => (mem_sdiff.mp cu).2 (eq ▸ kb)
  have ku : k ∈ U := mem_sdiff.mpr ⟨kv,fun h => (mem_insert.mp h).elim nc kT⟩
  have ct : c ∉ T := fun h => (mem_sdiff.mp cu).2 (mem_erase.mp h).2
  have bank : insert c T ⊆ V := insert_subset (mem_sdiff.mp cu).1
    (fun _ bt => sub (mem_erase.mp bt).2)
  have size : U.card = 3*(s-1) := by
    change (V \ insert c T).card = _
    rw [card_sdiff_of_subset bank,card_insert_of_notMem ct,two,order]; omega
  have room (a) (au : a ∈ U) : s-1 ≤ (outN D U a).card + (if a ∈ R then 1 else 0) := by
    have eq := card_outN_union (D := D) (show Disjoint (insert c T) U from disjoint_sdiff) a
    rw [union_sdiff_of_subset bank,reg a (mem_sdiff.mp au).1] at eq
    obtain ⟨yes,no⟩ := spec a au
    by_cases ar : a ∈ R
    · rw [ite_eq_left ar]; have := yes.mp ar; omega
    · rw [ite_eq_right ar]; have := no ar; omega
  by_contra! enough
  obtain ⟨C,ok,floor⟩ := (shared_head_iff (safe.mono_set (sdiff_subset : U ⊆ V)) ku fresh room).mpr enough
  exact none _ U ⟨k,ku⟩ size.le ok floor

#print axioms rotated_lone_frontier
#print axioms top_parent_frontier
#print axioms three_tight_on_lone_frontier
#print axioms promote_parent
#print axioms three_tight
end LeanCH.BR.TripleBank
