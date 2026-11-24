import checkpoints.shen_extension.OneHeadPivotLoops
import checkpoints.shen_extension.SeymourTransition

namespace LeanCH.BR.Closure.PivotLoops
open BRq2 BRq3 Finset OneHeadHeavyRows DeleteRepair

private theorem free_of_edges {D E : CH.Digraph} {W : Finset ℕ} {q}
    (safe : QFree E W q) (sub : ∀ x ∈ W, ∀ z ∈ W, D x z = true → E x z = true) : QFree D W q := by
  have lift {x z k} (w : Walk D W x z k) (hx : x ∈ W) : Walk E W x z k := by
    induction w with
    | refl => exact .refl _
    | step hz e _ ih => exact .step hz (sub _ hx _ hz e) (ih hz)
  intro x k lo hi w
  have hx : x ∈ W := by
    cases w with
    | refl => omega
    | step hz _ rest => exact rest.end_mem_or.elim (fun eq => eq ▸ hz) id
  exact safe x k lo hi (lift w hx)

/-- A low indegree witness at every marked deletion that kills all triangles.
This is sensitive to the order of the original nearly regular completion. -/
theorem puncture_low_indegree {H : CH.Digraph} {U : Finset ℕ} {s v : ℕ}
    (safe : QFree H U 2) (hv : v ∈ U) (live : (U.erase v).Nonempty)
    (puncture : QFree H (U.erase v) 3) (degree : ∀ x ∈ U, s ≤ (outN H U x).card)
    (order : U.card+1 ≤ 3*s) :
    ∃ x ∈ U.erase v, (BR45.inN H U x).card < s ∧
      (s ≤ (BR45.inN H U x).card+1 → H x v = true) := by
  obtain ⟨x,hx,_,low⟩ := ShenSeymour.surviving_row puncture (by decide) (Subset.refl _) live
  have xu := (mem_erase.mp hx).2
  have deg := degree x xu
  change 2*(outN H (U.erase v) x).card + (BR45.inN H (U.erase v) x).card < _ at low
  have ins : BR45.inN H (U.erase v) x = (BR45.inN H U x).erase v := by
    ext z
    simp only [BR45.mem_inN,mem_erase]
    tauto
  rw [UnitState.outN_erase,ins,card_erase_of_mem hv] at low
  have ci := pred_card_le_card_erase (s:=BR45.inN H U x) (a:=v)
  have co := pred_card_le_card_erase (s:=outN H U x) (a:=v)
  by_cases hit : H x v = true
  · have no := digonfree safe (by decide) xu hv hit
    rw [erase_eq_of_notMem (fun m => no (BR45.mem_inN.mp m).2)] at low
    exact ⟨x,hx,by omega,fun _ => hit⟩
  · rw [erase_eq_of_notMem (fun m => hit (mem_outN.mp m).2)] at low
    exact ⟨x,hx,by omega,by omega⟩

/-- Fill any one missing head of the short row. Every new short cycle
uses both endpoints, including when the new edge closes a digon. -/
theorem filled_punctures {U d} (a : UnitRowState U d) (norm : Normal a) {y}
    (hy : y ∈ U) (new : a.graph a.root y ≠ true) :
    let H := repair a.graph {a.root} (fun _ => {y})
    (∀ x ∈ U, (outN H U x).card=d+1) ∧
    ∀ v ∈ ({a.root,y} : Finset ℕ), QFree H (U.erase v) 3 := by
  intro H
  have edges (x z) : H x z = true ↔ a.graph x z = true ∨ x = a.root ∧ z = y := by
    simp [H,repair]
  have enough (x) (hx : x ∈ U) : (outN H U x).card = d+1 := by
    by_cases eq : x = a.root
    · subst x
      have row : outN H U a.root = insert y (outN a.graph U a.root) := by
        ext z
        simp only [mem_outN,mem_insert,edges]
        have := hy
        grind
      rw [row,card_insert_of_notMem (fun h => new (mem_outN.mp h).2),a.short]
    · have row : outN H U x = outN a.graph U x := by ext z; simp [mem_outN,edges,eq]
      rw [row,norm x hx eq]
  refine ⟨enough,?_⟩
  intro v hv
  apply free_of_edges (a.free.mono_set (erase_subset v U))
  intro x hx z hz e
  have noX := (mem_erase.mp hx).1
  have noZ := (mem_erase.mp hz).1
  rcases (edges x z).mp e with old | ⟨xr,zy⟩
  · exact old
  · simp only [mem_insert,mem_singleton] at hv
    grind

#print axioms filled_punctures

/-- Fill the missing edge on a normalized three-pivot loop. Every row pays,
and deleting any one of the loop's three roots kills every short cycle.
Each such deletion at native order supplies an indegree-deficient witness. -/
theorem loop_punctures {U d} (O : Origin 3 (d+1)) (small : U.card < O.V.card)
    (a : UnitRowState U d) (norm : Normal a) {y t} (site : Site a y t) :
    let H := repair a.graph {a.root} (fun _ => {y})
    (∀ x ∈ U, (outN H U x).card = d+1) ∧ QFree H U 2 ∧
    ∀ v ∈ ({a.root,y,t} : Finset ℕ), v ∈ U ∧ (U.erase v).Nonempty ∧ QFree H (U.erase v) 3 := by
  intro H
  have th : t ∈ returns a.graph U y a.root := site.single ▸ mem_singleton_self t
  obtain ⟨th,tu⟩ := mem_filter.mp th
  obtain ⟨tU,yt⟩ := mem_outN.mp th
  have new : a.graph a.root y ≠ true := fun h => a.free a.root 3 (by decide) (by decide)
    (.step site.live h (.step tU yt (.step a.live tu (.refl _))))
  have edges (x z) : H x z = true ↔ a.graph x z = true ∨ x = a.root ∧ z = y := by
    simp [H,repair]
  have enough := (filled_punctures a norm site.live new).1
  have orient : QFree H U 2 := by
    apply repair_qfree (a.free.mono_bound (by decide : 2 ≤ 3))
    intro u hu z hz u' hu' m hm walk
    obtain rfl := mem_singleton.mp hz
    obtain rfl := mem_singleton.mp hu'
    rcases (show m = 0 ∨ m = 1 by omega) with rfl | rfl
    · cases walk
      exact site.distinct rfl
    · cases walk with
      | step _ edge tail => cases tail; exact site.nonparent edge
  obtain ⟨b,turn,_,_⟩ := rotate O small a norm site
  refine ⟨enough,orient,?_⟩
  intro v hv
  simp only [mem_insert,mem_singleton] at hv
  have vU : v ∈ U := by rcases hv with rfl|rfl|rfl; exact a.live; exact site.live; exact tU
  have live : (U.erase v).Nonempty := by
    by_cases eq : v = a.root
    · exact ⟨y,mem_erase.mpr ⟨eq ▸ site.distinct,site.live⟩⟩
    · exact ⟨a.root,mem_erase.mpr ⟨Ne.symm eq,a.live⟩⟩
  refine ⟨vU,live,?_⟩
  by_cases last : v = t
  · have sub (x) (hx : x ∈ U.erase v) (z) (hz : z ∈ U.erase v) (edge : H x z = true) :
        b.graph x z = true := by
      have spec := turn.2.2 x (mem_erase.mp hx).2 z (mem_erase.mp hz).2
      have nz := (mem_erase.mp hz).1
      rcases (edges x z).mp edge with old|added
      · exact spec.mpr (Or.inl ⟨old,Or.inr (last ▸ nz)⟩)
      · exact spec.mpr (Or.inr added)
    exact free_of_edges (b.free.mono_set (erase_subset v U)) sub
  · have choice : v = a.root ∨ v = y := by tauto
    have sub (x) (hx : x ∈ U.erase v) (z) (hz : z ∈ U.erase v) (edge : H x z = true) :
        a.graph x z = true := by
      have nx := (mem_erase.mp hx).1
      have nz := (mem_erase.mp hz).1
      rcases (edges x z).mp edge with old|added
      · exact old
      · grind
    exact free_of_edges (a.free.mono_set (erase_subset v U)) sub

theorem native_loop_witnesses {U d} (O : Origin 3 (d+1)) (small : U.card < O.V.card)
    (a : UnitRowState U d) (norm : Normal a) {y t} (site : Site a y t)
    (order : U.card+1 ≤ 3*(d+1)) :
    let H := repair a.graph {a.root} (fun _ => {y})
    (∀ x ∈ U, (outN H U x).card = d+1) ∧
    ∀ v ∈ ({a.root,y,t} : Finset ℕ), ∃ x ∈ U.erase v,
      (BR45.inN H U x).card < d+1 ∧ (d+1 ≤ (BR45.inN H U x).card+1 → H x v = true) := by
  obtain ⟨deg,safe,punctures⟩ := loop_punctures O small a norm site
  refine ⟨deg,?_⟩
  intro v hv
  obtain ⟨vU,live,free⟩ := punctures v hv
  exact puncture_low_indegree safe vU live free (fun x hx => (deg x hx).ge) order

/-- At native order, deleting two labels including any triangle label produces
a common parent outside the pair. This uses the frontier at one lower degree. -/
theorem native_pair_parent {q d v w} {U : Finset ℕ} {H : CH.Digraph}
    (lower : DeficitLevels.OrderLaw q d (q*d+1)) (size : U.card = q*d+2) (nd : 0 < q*d)
    (deg : ∀ x ∈ U, d+1 ≤ (outN H U x).card) (free : QFree H (U.erase v) q)
    (hv : v ∈ U) (hw : w ∈ U) (ne : w ≠ v) :
    ∃ x ∈ (U.erase v).erase w, H x v = true ∧ H x w = true := by
  let K := (U.erase v).erase w
  have wv : w ∈ U.erase v := mem_erase.mpr ⟨ne,hw⟩
  have ck : K.card = q*d := by simp only [K,card_erase_of_mem wv,card_erase_of_mem hv,size]; omega
  have live : K.Nonempty := card_pos.mp (ck ▸ nd)
  by_contra! none
  have pays (x) (hx : x ∈ K) : d ≤ (outN H K x).card := by
    have orig := deg x ((mem_erase.mp (mem_erase.mp hx).2).2)
    rw [show outN H K x = ((outN H U x).erase v).erase w by
      simp only [K,UnitState.outN_erase]]
    by_cases xv : H x v = true
    · have xw := none x hx xv
      rw [erase_eq_of_notMem (a:=w) (fun hit => xw ((mem_outN.mp (mem_of_mem_erase hit)).2))]
      have := pred_card_le_card_erase (s:=outN H U x) (a:=v)
      omega
    · rw [erase_eq_of_notMem (fun hit => xv (mem_outN.mp hit).2)]
      have := pred_card_le_card_erase (s:=outN H U x) (a:=w)
      omega
  have impossible := lower H K (free.mono_set (erase_subset w _)) pays live
  omega

#print axioms puncture_low_indegree
#print axioms loop_punctures
#print axioms native_loop_witnesses
#print axioms native_pair_parent
end LeanCH.BR.Closure.PivotLoops
