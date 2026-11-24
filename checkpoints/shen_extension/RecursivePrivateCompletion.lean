import checkpoints.shen_extension.RecursivePackingFrontier

/-! A full head can be copied privately. Every old row except its designated
parent stays unchanged, and the new row is full. The operation is allowed
to change the carrier and the origin. -/
namespace LeanCH.BR.Closure.PrivateCompletion
open BRq2 BRq3 Finset DeficitLevels

theorem full_head {D : CH.Digraph} {U : Finset ℕ} {s q u : ℕ}
    (free : QFree D U q) (hq : 1≤q) (small : total s D U<s)
    (hu : u∈U) (short : 0<cost s D U u) :
    ∃ h∈outN D U u, s≤(outN D U h).card := by
  by_contra! none
  have sub : outN D U u ⊆ U.erase u := by
    intro h hit
    refine mem_erase.mpr ⟨?_,outN_subset hit⟩
    intro eq
    exact loopfree free hq hu (eq ▸ (mem_outN.mp hit).2)
  have rows := sum_le_sum (s:=outN D U u) (f:=fun _ => 1) (g:=cost s D U)
    (fun h hit => by have := none h hit; unfold cost; omega)
  simp only [sum_const,Nat.nsmul_eq_mul,Nat.mul_one] at rows
  have extend := sum_le_sum_of_subset_of_nonneg (f:=cost s D U) sub (fun _ _ _ => Nat.zero_le _)
  have count := sum_erase_add U (cost s D U) hu
  change _ + cost s D U u = total s D U at count
  unfold cost at short
  change _ + (s-(outN D U u).card) = total s D U at count
  omega

/-- A single private clone is one step of the recursion. Its removal
recovers exactly the old graph on the old labels. -/
theorem private_step {D : CH.Digraph} {U : Finset ℕ} {s q u : ℕ}
    (free : QFree D U q) (hq : 1≤q) (small : total s D U<s)
    (hu : u∈U) (short : 0<cost s D U u) :
    ∃ E v, v∉U ∧ QFree E (insert v U) q ∧ (∀ x∈U,∀ y∈U,E x y=D x y) ∧
      (∀ x∈U, E x v=true ↔ x=u) ∧ total s E (insert v U)+1=total s D U := by
  obtain ⟨h,edge,full⟩ := full_head free hq small hu short
  let v := U.max' ⟨u,hu⟩ + 1
  have far : v∉U := fun hit => by have := le_max' U v hit; dsimp [v] at this; omega
  let p (x : ℕ) := if x=v then h else x
  let E : CH.Digraph := fun x y => if y=v then decide (x=u) else D (p x) y
  have pv : p v=h := by simp [p]
  have pold {x} (hx : x∈U) : p x=x := by
    have ne : x≠v := fun e => far (e ▸ hx)
    simp [p,ne]
  have proj {x} (hx : x∈insert v U) : p x∈U := by
    rcases mem_insert.mp hx with rfl|hOld
    · rw [pv]; exact outN_subset edge
    · rwa [pold hOld]
  have map {x y} (xy : E x y=true) : D (p x) (p y)=true := by
    by_cases hy : y=v
    · have xu : x=u := by simpa [E,hy] using xy
      rw [xu,hy,pv,pold hu]; exact (mem_outN.mp edge).2
    · simpa [E,p,hy] using xy
  have walks {a b k} (w : Walk E (insert v U) a b k) : Walk D U (p a) (p b) k := by
    induction w with
    | refl => exact .refl _
    | step hb xy _ ih => exact .step (proj hb) (map xy) ih
  have eq {x y} (hx : x∈U) (hy : y∈U) : E x y = D x y := by
    have ne : y≠v := fun e => far (e ▸ hy)
    simp [E,ne,pold hx]
  have vu : v≠u := fun e => far (e ▸ hu)
  have oldrow (x) (hx : x∈U) : outN E (insert v U) x =
      if x=u then insert v (outN D U x) else outN D U x := by
    ext y
    by_cases yv : y=v
    · subst y
      by_cases xu : x=u <;> simp [mem_outN,E,xu,far]
    · by_cases yu : y∈U
      · by_cases xu : x=u <;> simp [mem_outN,xu,yv,yu,E,pold hx,pold hu]
      · by_cases xu : x=u <;> simp [mem_outN,xu,yv,yu]
  have newrow : outN E (insert v U) v = outN D U h := by
    ext y
    by_cases yv : y=v
    · subst y; simp [mem_outN,E,vu,far]
    · simp [mem_outN,E,yv,pv]
  have next (x) (hx : x∈U) :
      cost s E (insert v U) x + (if x=u then 1 else 0) = cost s D U x := by
    unfold cost
    rw [oldrow _ hx]
    by_cases xu : x=u
    · subst x
      have absent : v∉outN D U u := fun h => far (outN_subset h)
      simp only [ite_true, card_insert_of_notMem absent]
      unfold cost at short
      omega
    · simp [xu]
  refine ⟨E,v,far,fun a k lo hi w => free _ _ lo hi (walks w),
    fun _ hx _ hy => eq hx hy,fun x _ => by simp [E],?_⟩
  have num := sum_congr rfl next
  simp only [sum_add_distrib] at num
  have bill : (∑ x∈U, if x=u then 1 else (0:ℕ))=1 := by simp [hu]
  rw [bill] at num
  have paid : cost s E (insert v U) v=0 := by unfold cost; rw [newrow]; omega
  unfold total
  rw [sum_insert far,paid,Nat.zero_add]
  exact num

#print axioms full_head
#print axioms private_step
/-- An order-N completion whose final label alone is worth one unit. -/
def FinishesAt (q s N : ℕ) : Prop :=
  ∃ (D E : CH.Digraph) (U : Finset ℕ) (v : ℕ), v∉U ∧ U.Nonempty ∧
    (insert v U).card=N ∧ QFree E (insert v U) q ∧
    (∀ x∈U, ∀ y∈U, E x y=D x y) ∧ total s D U=1 ∧ total s E (insert v U)=0

theorem finishes_at {q s : ℕ} (hq : 1≤q) {D : CH.Digraph} {U : Finset ℕ}
    (free : QFree D U q) (pos : 0<total s D U) (small : total s D U<s) :
    FinishesAt q s (U.card+total s D U) := by
  suffices recur : ∀ k, ∀ (G : CH.Digraph) (W : Finset ℕ), QFree G W q →
      total s G W=k → 0<k → k<s → FinishesAt q s (W.card+k) from
    recur _ D U free rfl pos small
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro G W safe value positive below
    have existsShort : ∃ u∈W, 0<cost s G W u := by
      by_contra! none
      have zero : total s G W=0 := sum_eq_zero (fun u hu => by have := none u hu; omega)
      omega
    obtain ⟨u,hu,short⟩ := existsShort
    obtain ⟨E,v,fresh,free',kept,_,price⟩ := private_step safe hq (by omega) hu short
    have sz := card_insert_of_notMem fresh
    by_cases endNow : k=1
    · exact ⟨G,E,W,v,fresh,⟨u,hu⟩,by omega,free',kept,by omega,by omega⟩
    · have child := ih (total s E (insert v W)) (by omega) E (insert v W)
        free' rfl (by omega) (by omega)
      rwa [show (insert v W).card+total s E (insert v W)=W.card+k by omega] at child

/-- At exact cost the new origin has the same least order. Its original
one-label deletion has shortfall exactly one, including after saturation. -/
theorem rebase_exact {q s : ℕ} (O : Origin q s) {st : State}
    (valid : Valid O st) (hq : 1≤q) (pos : 0<total s st.H st.U)
    (small : total s st.H st.U<s) (exactCost : st.U.card+total s st.H st.U=O.V.card) :
    ∃ (P : Origin q s) (v : ℕ) (t : State), P.V.card=O.V.card ∧ MaximalReturns q P.G P.V ∧
      v∈P.V ∧ t.U=P.V.erase v ∧ Reach (RStep q s) P.init t ∧ total s t.H t.U=1 := by
  obtain ⟨D,E,U,v,fresh,live,N,safe,kept,unit,paid⟩ := finishes_at hq valid.2.2 pos small
  rw [exactCost] at N
  let W := insert v U
  obtain ⟨H,inc,freeH,maxH⟩ := BRsub.exists_satQ safe
  have deg (x) (hx : x∈W) : s≤(outN H W x).card := by
    have le := single_le_sum (s:=W) (f:=cost s E W) (fun _ _ => Nat.zero_le _) hx
    change s-(outN E W x).card ≤ total s E W at le
    have sub : outN E W x ⊆ outN H W x := by
      intro y hy
      exact mem_outN.mpr ⟨(mem_outN.mp hy).1,inc _ hx _ (mem_outN.mp hy).1 (mem_outN.mp hy).2⟩
    have := card_le_card sub
    change total s E W=0 at paid
    omega
  let P : Origin q s := ⟨H,W,insert_nonempty _ _,N.le.trans O.order,freeH,
    fun F Y ff fd ne => N.le.trans (O.least F Y ff fd ne),deg⟩
  have maxP : MaximalReturns q P.G P.V := by
    intro u hu z hz no
    obtain ⟨_,k,le,w⟩ := mem_ball.mp (maxH z hz u hu no)
    exact ⟨k,by omega,w⟩
  let t : State := ⟨U,H⟩
  have ss : U ⊂ W := ssubset_insert fresh
  have reach : Reach (RStep q s) P.init t := Relation.ReflTransGen.single (Or.inl ⟨rfl,ss,live⟩)
  have upto : total s H U ≤ total s D U := by
    apply sum_le_sum
    intro x hx
    have incl : outN D U x ⊆ outN H U x := by
      intro y hy
      obtain ⟨hy,xy⟩ := mem_outN.mp hy
      exact mem_outN.mpr ⟨hy,inc _ (mem_insert_of_mem hx) _ (mem_insert_of_mem hy)
        (by rwa [kept x hx y hy])⟩
    have := card_le_card incl
    unfold cost
    omega
  have nonzero : 0<total s H U := by
    by_contra! zero
    apply valid_not_paid P (rreach_valid P reach) (card_lt_card ss)
    intro u hu
    have le := single_le_sum (s:=U) (f:=cost s H U) (fun _ _ => Nat.zero_le _) hu
    change s-(outN H U u).card≤total s H U at le
    change s≤(outN H U u).card
    omega
  refine ⟨P,v,t,N,maxP,mem_insert_self _ _,?_,reach,?_⟩
  · change U=(insert v U).erase v
    simp [fresh]
  · change total s H U=1
    omega

#print axioms finishes_at
#print axioms rebase_exact
/-- Three consequences attached to the actual least-degree frontier. In the
exact-cost case the origin may change, but neither its degree nor its order does. -/
def Alternatives {q d : ℕ} (O : Origin q (d+1)) (st : State) : Prop :=
  (total (d+1) st.H st.U=d+1 ∧
    ∀ v∈O.V, (outN O.G O.V v).card=d+1 ∧ (BR45.inN O.G O.V v).card=d+1) ∨
  (∃ (P : Origin q (d+1)) (v : ℕ) (t : State), P.V.card=O.V.card ∧
    MaximalReturns q P.G P.V ∧ v∈P.V ∧ t.U=P.V.erase v ∧
    Reach (RStep q (d+1)) P.init t ∧ total (d+1) t.H t.U=1) ∨
  (total (d+1) st.H st.U<d+1 ∧ ∃ g e, 0<g ∧
    O.V.card+e=q*(d+1) ∧ O.V.card+g=st.U.card+total (d+1) st.H st.U ∧
    let t := (st.U.filter (fun u => 0<cost (d+1) st.H st.U u)).card
    total (d+1) st.H st.U+t*t+t*e≤t*(q+2*g))

theorem candidate_alternatives {D : CH.Digraph} {V : Finset ℕ} {s q : ℕ}
    (hq : 1≤q) (free : QFree D V q) (live : V.Nonempty)
    (bound : V.card≤q*s) (degree : ∀ u∈V, s≤(outN D V u).card) :
    ∃ d, d+1≤s ∧ ∃ (O : Origin q (d+1)) (st : State),
      PackingFrontier.Frontier O st ∧ Alternatives O st := by
  obtain ⟨d,ds,O,st,fr⟩ := PackingFrontier.from_candidate hq free live bound degree
  refine ⟨d,ds,O,st,fr,?_⟩
  rcases fr.alternative with high|⟨low,g,e,size,gap,box⟩
  · exact Or.inl ⟨high,PackingFrontier.high_regular fr high hq⟩
  · by_cases zero : g=0
    · apply Or.inr ∘ Or.inl
      apply rebase_exact O (rreach_valid O fr.reached) hq fr.positive low
      simpa [zero] using gap.symm
    · exact Or.inr (Or.inr ⟨low,g,e,by omega,size,gap,box⟩)

#print axioms candidate_alternatives
/-- One unit identifies one row owing one head and every other row is full. -/
theorem unit_profile {D : CH.Digraph} {U : Finset ℕ} {s : ℕ} (unit : total s D U=1) :
    ∃ u∈U, (outN D U u).card+1=s ∧ ∀ x∈U, x≠u → s≤(outN D U x).card := by
  have existsShort : ∃ u∈U, 0<cost s D U u := by
    by_contra! none
    have zero : total s D U=0 := sum_eq_zero (fun u hu => by have := none u hu; omega)
    omega
  obtain ⟨u,hu,short⟩ := existsShort
  have sum := sum_erase_add U (cost s D U) hu
  change _ + cost s D U u = total s D U at sum
  refine ⟨u,hu,by unfold cost at short sum; omega,?_⟩
  intro x hx ne
  have er : x∈U.erase u := mem_erase.mpr ⟨ne,hx⟩
  have le := single_le_sum (f:=cost s D U) (fun _ _ => Nat.zero_le _) er
  change s-(outN D U x).card ≤ _ at le
  omega

/-- In a proper one-unit state, for every head h of the unique short row
and every retained non-head z of that row, a degree-s parent of z misses h.
Otherwise erase z and clone h on the remaining carrier and obtain a paid
graph with exactly the old proper order. -/
theorem unit_separation {q s : ℕ} (O : Origin q s) {st : State}
    (valid : Valid O st) (proper : st.U.card<O.V.card) (unit : total s st.H st.U=1) :
    ∃ u∈st.U, (outN st.H st.U u).card+1=s ∧
      ∀ h∈outN st.H st.U u, ∀ z∈st.U, st.H u z≠true →
        ∃ p∈st.U, (outN st.H st.U p).card=s ∧ st.H p z=true ∧ st.H p h≠true := by
  classical
  obtain ⟨u,hu,short,full⟩ := unit_profile unit
  refine ⟨u,hu,short,?_⟩
  intro h head z hz missed
  by_contra! none
  let W := st.U.erase z
  have hU := outN_subset head
  have hW : h∈W := mem_erase.mpr ⟨fun eq => missed (eq ▸ (mem_outN.mp head).2),hU⟩
  let clone (w : ℕ) : ℕ := if w=h then 1 else 0
  have row (x) (hx : x∈W) : s≤(outN st.H W x).card + ∑ w∈outN st.H W x, clone w := by
    have xU := mem_of_mem_erase hx
    have er : outN st.H W x=(outN st.H st.U x).erase z := by
      ext w; simp only [W,mem_outN,mem_erase]; tauto
    have spare (edge : st.H x h=true) : 1≤∑ w∈outN st.H W x, clone w := by
      have le := single_le_sum (f:=clone) (fun _ _ => Nat.zero_le _) (mem_outN.mpr ⟨hW,edge⟩)
      simpa [clone] using le
    by_cases hit : st.H x z=true
    · have ne : x≠u := fun eq => missed (eq ▸ hit)
      have deg := full x xU ne
      have sz := card_erase_of_mem (mem_outN.mpr ⟨hz,hit⟩ : z∈outN st.H st.U x)
      rw [← er] at sz
      by_cases eq : (outN st.H st.U x).card=s
      · have := spare (none x xU eq hit)
        omega
      · omega
    · have abs : z∉outN st.H st.U x := fun e => hit (mem_outN.mp e).2
      rw [erase_eq_of_notMem abs] at er
      have sameSize := congrArg Finset.card er
      by_cases xu : x=u
      · subst x; have := spare (mem_outN.mp head).2; omega
      · have := full x xU xu; omega
  have bill := WeightedHost.cover_bound O.least clone (valid.2.2.mono_set (erase_subset z st.U))
    (show W.Nonempty from ⟨h,hW⟩) row
  have clones : ∑ w∈W, clone w=1 := by simp [clone,hW]
  rw [clones] at bill
  change O.V.card ≤ W.card+1 at bill
  have sz : W.card+1=st.U.card := card_erase_add_one hz
  omega

#print axioms unit_separation
end LeanCH.BR.Closure.PrivateCompletion
