import checkpoints.shen_extension.ThreeParentOverlap

namespace LeanCH.BR.TripleBank
open Finset BRq2 BRq3 BR45 JointFreeTargets

/-- A free head removes its tail from the tight parents and leaves every
other row on the same carrier unchanged. -/
theorem free_promote_parent {D : CH.Digraph} {U : Finset ℕ} {c a p t : ℕ}
    (safe : QFree D U 3) (cu : c ∈ U) (parent : a ∈ tightParents D U c t)
    (target : FreeTarget D U a p)
    (floor : ∀ v ∈ U, v ≠ c → t ≤ (outN D U v).card) :
    let E := addTargets D {a} (fun _ => p)
    QFree E U 3 ∧ (∀ v ∈ U, v ≠ c → t ≤ (outN E U v).card) ∧
    tightParents E U c t = (tightParents D U c t).erase a ∧
    ∀ v, v ≠ a → outN E U v = outN D U v := by
  classical
  dsimp only
  let E := addTargets D {a} (fun _ => p)
  have ha := mem_inN.mp (mem_filter.mp parent).1
  have ac : a ≠ c := fun e => loopfree safe (by decide) cu (e ▸ ha.2)
  have pc : p ≠ c := fun e => target.2.2.1 (e ▸ ha.2)
  obtain ⟨ok,rows⟩ := free_repair (R := {a}) (f := fun _ => p) safe
    (fun v vs => by
      obtain rfl := mem_singleton.mp vs
      exact ⟨target, by simpa using target.2.1⟩)
  have same (v) (va : v ≠ a) : outN E U v = outN D U v := by
    ext z
    simp [E, addTargets, mem_outN, va]
  have parents : inN E U c = inN D U c := by
    ext v
    simp [E, addTargets, mem_inN, pc.symm]
  refine ⟨ok, ?_, ?_, same⟩
  · intro v vu vc
    exact (floor v vu vc).trans (by rw [rows v]; omega)
  · change tightParents E U c t = (tightParents D U c t).erase a
    ext v
    simp only [tightParents, mem_filter, mem_erase, parents]
    by_cases va : v = a
    · subst v
      have paid := rows a
      simp at paid
      have old := floor a ha.1 ac
      change (outN E U a).card = (outN D U a).card + 1 at paid
      have high : ¬ (outN E U a).card ≤ t := by omega
      simp [high]
    · rw [same v va]
      simp [va]

/-- A free promotion and an ordinary promotion on the same bank leave one
tight parent. A preserved head of that parent fills the freed slot. -/
theorem no_free_with_promotion {D : CH.Digraph} {U : Finset ℕ} {c a b d k t : ℕ}
    (safe : QFree D U 3) (cu : c ∈ U) (ku : k ∈ U) (ck : D c k = true)
    (small : U.card ≤ 3*t) (none : BypassRepair.NoHost 3 t)
    (floor : ∀ v ∈ U, v ≠ c → t ≤ (outN D U v).card)
    (ab : a ≠ b) (ad : a ≠ d) (bd : b ≠ d)
    (triple : tightParents D U c t = {a,b,d})
    (miss : D b k ≠ true) (dk : D d k = true)
    (spare : ∀ w ∈ outN D U k, t < (outN D U w).card) :
    ∀ p, ¬ FreeTarget D U a p := by
  classical
  intro p target
  have am : a ∈ tightParents D U c t := by simp [triple]
  have dm : d ∈ tightParents D U c t := by simp [triple]
  have db : d ≠ b := bd.symm
  have kc : k ≠ c := fun e => loopfree safe (by decide) cu (e ▸ ck)
  have ka : k ≠ a := fun e => digonfree safe (by decide) cu ku ck
    (e ▸ (mem_inN.mp (mem_filter.mp am).1).2)
  obtain ⟨ok, lower, erased, same⟩ := free_promote_parent safe cu am target floor
  let E := addTargets D {a} (fun _ => p)
  change QFree E U 3 at ok
  change tightParents E U c t = (tightParents D U c t).erase a at erased
  have reduced : tightParents E U c t = {b,d} := by
    rw [erased,triple]
    ext v
    simp only [mem_erase, mem_insert, mem_singleton]
    grind
  have Eparent : b ∈ tightParents E U c t := by simp [reduced]
  have Edm : d ∈ tightParents E U c t := by simp [reduced]
  have Ehc : E c k = true := by simp [E,addTargets,ck]
  have Ehk : E d k = true := by simp [E,addTargets,dk]
  have Emiss : E b k ≠ true := by simp [E,addTargets,miss,ab.symm]
  have Espare (w) (wm : w ∈ outN E U k) : t < (outN E U w).card := by
    rw [same k ka] at wm
    have ne : w ≠ a := fun eq => safe c 3 (by decide) (by decide)
      (.step ku ck (.step (outN_subset wm) (mem_outN.mp wm).2
        (.step cu (eq.symm ▸ (mem_inN.mp (mem_filter.mp am).1).2) (.refl _))))
    rw [same w ne]
    exact spare w wm
  obtain ⟨G,gok,glower,new,keep⟩ := promote_parent ok cu ku Ehc Eparent Emiss Espare lower
  obtain ⟨w,wu,_,wc,wd,absent⟩ := BypassCloneCover.misses_copy none small gok cu ku kc glower
  have wm : w ∈ tightParents G U c t := mem_filter.mpr ⟨mem_inN.mpr ⟨wu,wc⟩,wd.le⟩
  rw [new,reduced] at wm
  have eq : w = d := by
    simp only [mem_erase, mem_insert, mem_singleton] at wm
    exact wm.2.resolve_left wm.1
  subst w
  have keepD := keep d (mem_filter.mp Edm).1 db
  apply absent
  exact (mem_outN.mp (keepD ▸ mem_outN.mpr ⟨ku,Ehk⟩ : k ∈ outN G U d)).2

/-- A single free promotion cannot leave two tight parents that have
a common head away from the deficient row. -/
theorem no_free_with_common_head {D : CH.Digraph} {U : Finset ℕ} {c a b d k t : ℕ}
    (safe : QFree D U 3) (cu : c ∈ U) (ku : k ∈ U) (kc : k ≠ c)
    (small : U.card ≤ 3*t) (none : BypassRepair.NoHost 3 t)
    (floor : ∀ v ∈ U, v ≠ c → t ≤ (outN D U v).card)
    (ad : a ≠ d) (bd : b ≠ d)
    (triple : tightParents D U c t = {a,b,d})
    (ak : D a k = true) (bk : D b k = true) :
    ∀ p, ¬ FreeTarget D U d p := by
  classical
  intro p target
  have dm : d ∈ tightParents D U c t := by simp [triple]
  obtain ⟨ok, lower, erased, same⟩ := free_promote_parent safe cu dm target floor
  obtain ⟨w,wu,_,wc,wd,absent⟩ := BypassCloneCover.misses_copy none small ok cu ku kc lower
  have wm : w ∈ tightParents (addTargets D {d} (fun _ => p)) U c t :=
    mem_filter.mpr ⟨mem_inN.mpr ⟨wu,wc⟩,wd.le⟩
  rw [erased,triple] at wm
  simp only [mem_erase, mem_insert, mem_singleton] at wm
  have hit : D w k = true := by
    rcases wm.2 with rfl | rfl | rfl
    · exact ak
    · exact bk
    · exact (wm.1 rfl).elim
  have edge : k ∈ outN (addTargets D {d} (fun _ => p)) U w := by
    rw [same w wm.1]
    exact mem_outN.mpr ⟨ku,hit⟩
  exact absent (mem_outN.mp edge).2

/-- Both nonsinks of the three-parent structure point to its sink.
All three tight parents have no free target on the original carrier. -/
theorem three_parent_saturation {D : CH.Digraph} {U L : Finset ℕ} {c a b d k t : ℕ}
    (safe : QFree D U 3) (cu : c ∈ U) (ku : k ∈ U) (ck : D c k = true)
    (small : U.card ≤ 3*t) (none : BypassRepair.NoHost 3 t)
    (floor : ∀ v ∈ U, v ≠ c → t ≤ (outN D U v).card)
    (ab : a ≠ b) (ad : a ≠ d) (bd : b ≠ d) (triple : tightParents D U c t = {a,b,d})
    (ak : D a k ≠ true) (bk : D b k ≠ true) (dk : D d k = true)
    (spare : ∀ w ∈ outN D U k, t < (outN D U w).card)
    (sink : ∀ h ∈ tightParents D U c t, D d h ≠ true)
    (drow : (outN D U d).erase c = L)
    (clear : L ⊆ neutral D U (tightParents D U c t) c) :
    D a d = true ∧ D b d = true ∧
      ∀ x ∈ tightParents D U c t, ∀ p, ¬ FreeTarget D U x p := by
  have satA := no_free_with_promotion safe cu ku ck small none floor ab ad bd triple bk dk spare
  have swap : tightParents D U c t = {b,a,d} := by rw [triple, insert_comm]
  have satB := no_free_with_promotion safe cu ku ck small none floor ab.symm bd ad swap ak dk spare
  have dm : d ∈ tightParents D U c t := by simp [triple]
  have du := (mem_inN.mp (mem_filter.mp dm).1).1
  have dc := (mem_inN.mp (mem_filter.mp dm).1).2
  have hit (x) (xm : x ∈ tightParents D U c t) (xd : x ≠ d)
      (sat : ∀ p, ¬ FreeTarget D U x p) : D x d = true := by
    by_contra hd
    apply sat d
    refine ⟨du, xd.symm, hd, sink x xm, ?_⟩
    intro w wu dw
    by_cases wc : w = c
    · subst w
      obtain ⟨xu,xc⟩ := mem_inN.mp (mem_filter.mp xm).1
      exact fun cx => digonfree safe (by decide) cu xu cx xc
    · have wl : w ∈ L := drow ▸ mem_erase.mpr ⟨wc,mem_outN.mpr ⟨wu,dw⟩⟩
      have dis := (mem_filter.mp (clear wl)).2
      exact fun wx => disjoint_left.mp dis (mem_outN.mpr
        ⟨(mem_inN.mp (mem_filter.mp xm).1).1,wx⟩) xm
  have toD₁ := hit a (by simp [triple]) ad satA
  have toD₂ := hit b (by simp [triple]) bd satB
  have dc' : d ≠ c := fun e => loopfree safe (by decide) cu (e ▸ dc)
  have satD := no_free_with_common_head safe cu du dc' small none floor ad bd triple toD₁ toD₂
  refine ⟨toD₁,toD₂,?_⟩
  intro x xm
  rw [triple] at xm
  simp only [mem_insert,mem_singleton] at xm
  rcases xm with rfl | rfl | rfl
  · exact satA
  · exact satB
  · exact satD

/-- The same witnesses from the three-parent structure carry the two edges
to the sink and incoming saturation. -/
theorem saturated_three_parent_structure {D : CH.Digraph} {U L : Finset ℕ} {c k t : ℕ}
    (safe : QFree D U 3) (cu : c ∈ U) (ku : k ∈ U) (ck : D c k = true)
    (small : U.card ≤ 3*t) (none : BypassRepair.NoHost 3 t)
    (floor : ∀ v ∈ U, v ≠ c → t ≤ (outN D U v).card)
    (spare : ∀ w ∈ outN D U k, t < (outN D U w).card)
    (size : L.card+1 = t) (clear : L ⊆ neutral D U (tightParents D U c t) c)
    (three : (tightParents D U c t).card = 3) :
    let H := tightParents D U c t
    ∃ a b d, a ≠ b ∧ a ≠ d ∧ b ≠ d ∧ H = {a,b,d} ∧
      (D a k ≠ true ∧ D b k ≠ true ∧ D d k = true) ∧
      (∀ h ∈ H, D d h ≠ true) ∧ (outN D U d).erase c = L ∧
      Disjoint (outN D U a) L ∧ Disjoint (outN D U b) L ∧
      (∀ v ∈ (outN D U a ∪ outN D U b).erase c, v ≠ d → D v d = true) ∧
      D a d = true ∧ D b d = true ∧ (∀ x ∈ H, ∀ p, ¬ FreeTarget D U x p) := by
  dsimp only
  obtain ⟨a,b,d,ab,ad,bd,triple,heads,sink,drow,al,bl,gate⟩ :=
    three_parent_structure safe cu ku ck small none floor spare size clear three
  obtain ⟨ak,bk,dk⟩ := heads
  exact ⟨a,b,d,ab,ad,bd,triple,⟨ak,bk,dk⟩,sink,drow,al,bl,gate,
    three_parent_saturation safe cu ku ck small none floor ab ad bd triple ak bk dk spare sink drow clear⟩

#print axioms free_promote_parent
#print axioms no_free_with_promotion
#print axioms no_free_with_common_head
#print axioms three_parent_saturation
#print axioms saturated_three_parent_structure
end LeanCH.BR.TripleBank
