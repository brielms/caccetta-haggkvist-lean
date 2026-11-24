import checkpoints.shen_extension.CutoffDegreeRank

namespace LeanCH.BR.Closure.CoreExchange
open Finset BRq2 BRq3 BR45 DeficitLevels

/-- At exactly qd labels the interior has a row below d and the exterior
has a row above d into the very same set. -/
theorem gap {q s d} (O : Origin q s) (_hq : 1≤q) (laws : ∀j<s,OrderLaw q j (q*j+1))
    {U : Finset ℕ} (uv : U⊆O.V) (live : U.Nonempty) (outside : (O.V\U).Nonempty)
    (size : U.card=q*d) :
    (∃x∈U,(outN O.G U x).card<d) ∧ (∃y∈O.V\U,d<(outN O.G U y).card) := by
  have vsize := card_sdiff_add_card_eq_card uv
  obtain ⟨x,xu,small⟩ := PaidLayerDescent.light O laws uv (by have := card_pos.mpr outside; omega) live
  let L := PaidLayerDescent.Layers.start (D:=O.G) U uv
  have rest : ((O.V\L.old)\L.bank).Nonempty := by simpa [L,PaidLayerDescent.Layers.start] using outside
  have used : (L.old∪L.bank).Nonempty := by simpa [L,PaidLayerDescent.Layers.start] using live
  obtain ⟨y,yv,large⟩ := PaidLayerDescent.price O laws L rest used
  simp only [L,PaidLayerDescent.Layers.start,card_empty,sdiff_empty,Nat.add_zero,Nat.mul_zero] at large yv
  refine ⟨⟨x,xu,?_⟩,y,yv,?_⟩
  · by_contra! ge
    have := Nat.mul_le_mul_left q ge
    omega
  · by_contra! le
    have := Nat.mul_le_mul_left q le
    have ord := O.order
    omega

/-- Insert one row into an induced graph and count its incoming and
outgoing original arcs separately. -/
private theorem insert_arcs {D : CH.Digraph} {W : Finset ℕ} {v} (fresh : v∉W) (no : D v v≠true) :
    UnitBatch.arcs D (insert v W)=UnitBatch.arcs D W+(outN D W v).card+(inN D W v).card := by
  classical
  have row (x) : (outN D (insert v W) x).card =
      (outN D W x).card+(if D x v=true then 1 else 0) := by
    by_cases hit : D x v=true
    · have eq : outN D (insert v W) x=insert v (outN D W x) := by
        ext z; simp only [mem_outN,mem_insert]; grind
      have vn : v∉outN D W x := fun h => fresh (outN_subset h)
      simp [eq,card_insert_of_notMem vn,hit]
    · have eq : outN D (insert v W) x=outN D W x := by
        ext z; simp only [mem_outN,mem_insert]; grind
      simp [eq,hit]
  unfold UnitBatch.arcs
  rw [sum_insert fresh,row]
  rw [ite_eq_right no,Nat.add_zero]
  simp_rw [row]
  rw [sum_add_distrib]
  have eq : (∑x∈W,if D x v=true then 1 else 0)=(inN D W v).card := by rw [←card_filter]; rfl
  omega

/-- At a maximal arc count any improving outgoing exchange has to pay for
its gain with a loss in the incoming column, on the same rows. -/
theorem reverse_gap {q s d} (O : Origin q s) (hq : 2≤q) {U : Finset ℕ} (uv : U⊆O.V)
    {x y} (xu : x∈U) (yv : y∈O.V\U) (low : (outN O.G U x).card<d)
    (high : d<(outN O.G U y).card)
    (stuck : UnitBatch.arcs O.G (insert y (U.erase x))≤UnitBatch.arcs O.G U) :
    (inN O.G U y).card<(inN O.G U x).card := by
  classical
  let W := U.erase x
  have xv := uv xu
  have vy := (mem_sdiff.mp yv).1
  have yn := (mem_sdiff.mp yv).2
  have xw : x∉W := notMem_erase _ _
  have yw : y∉W := fun hit => yn (erase_subset _ _ hit)
  have nox := loopfree O.free (by omega) xv
  have noy := loopfree O.free (by omega) vy
  have eq : insert x W=U := insert_erase xu
  have old := insert_arcs (D:=O.G) xw nox
  rw [eq] at old
  have new := insert_arcs (D:=O.G) yw noy
  change UnitBatch.arcs O.G (insert y W)≤_ at stuck
  rw [new,old] at stuck
  have difference (D : CH.Digraph) (a) : (outN D U a).card=(outN D W a).card+(if D a x=true then 1 else 0) := by
    have sub : outN D W a=(outN D U a).erase x := by
      ext z; simp only [W,mem_outN,mem_erase]; tauto
    rw [sub]
    by_cases ax : D a x=true
    · have mem := mem_outN.mpr ⟨xu,ax⟩
      simpa [ax] using (card_erase_add_one mem).symm
    · have absent : x∉outN D U a := fun h => ax (mem_outN.mp h).2
      simp [ax,erase_eq_of_notMem absent]
  have rdiff (a) : (inN O.G U a).card=(inN O.G W a).card+(if O.G x a=true then 1 else 0) :=
    difference (fun u v => O.G v u) a
  rw [difference O.G x] at low
  rw [difference O.G y] at high
  rw [rdiff x,rdiff y]
  rw [ite_eq_right nox] at low ⊢
  by_cases yx : O.G y x=true
  · have xy := digonfree O.free hq vy xv yx
    rw [ite_eq_left yx] at high
    rw [ite_eq_right xy]
    omega
  · rw [ite_eq_right yx] at high
    split_ifs <;> omega

def Step (D : CH.Digraph) (V : Finset ℕ) (d : ℕ) (U B : Finset ℕ) : Prop :=
  ∃x∈U, ∃y∈V\U,(outN D U x).card<d ∧ d<(outN D U y).card ∧ B=insert y (U.erase x)

/-- Start at a specified carrier. The reachable exchange states contain
one on which *all* allowed row choices incur a strictly opposite incoming
inequality. The witnesses still exist there. -/
theorem reachable_barrier {q s d} (O : Origin q s) (hq : 2≤q)
    (laws : ∀j<s,OrderLaw q j (q*j+1)) {U : Finset ℕ} (uv : U⊆O.V)
    (live : U.Nonempty) (proper : U.card<O.V.card) (size : U.card=q*d) :
    ∃B⊆O.V, B.card=U.card ∧ Reach (Step O.G O.V d) U B ∧
      (∃x∈B,(outN O.G B x).card<d) ∧ (∃y∈O.V\B,d<(outN O.G B y).card) ∧
      ∀x∈B,∀y∈O.V\B,(outN O.G B x).card<d → d<(outN O.G B y).card →
        (inN O.G B y).card<(inN O.G B x).card := by
  classical
  let states := O.V.powerset.filter (fun B => B.card=U.card ∧ Reach (Step O.G O.V d) U B)
  have seed : U∈states := mem_filter.mpr ⟨mem_powerset.mpr uv,rfl,.refl⟩
  obtain ⟨B,hit,maximum⟩ := states.exists_max_image (UnitBatch.arcs O.G) ⟨U,seed⟩
  obtain ⟨bv,bs,path⟩ := mem_filter.mp hit
  have sub := mem_powerset.mp bv
  have ct := card_sdiff_add_card_eq_card sub
  have ⟨lo,hi⟩ := gap O (by omega) laws sub (card_pos.mp (by have := card_pos.mpr live; omega))
    (card_pos.mp (by omega)) (bs.trans size)
  refine ⟨B,sub,bs,path,lo,hi,?_⟩
  intro x xb y yv low high
  apply reverse_gap O hq sub xb yv low high
  apply maximum
  have yn : y∉B.erase x := fun a => (mem_sdiff.mp yv).2 (erase_subset _ _ a)
  have step : Step O.G O.V d B (insert y (B.erase x)) := ⟨x,xb,y,yv,low,high,rfl⟩
  refine mem_filter.mpr ⟨mem_powerset.mpr (insert_subset (mem_sdiff.mp yv).1 ((erase_subset _ _).trans sub)),?_,
    path.tail step⟩
  rw [card_insert_of_notMem yn,card_erase_add_one xb,bs]

/-- Compare the two scales on the *same* deletion at the boundary order
of the internal degree d. An exterior original row sends at least d+1
heads into the punctured core, while a tight interior row loses its head t. -/
theorem boundary_puncture {q s d} (O : Origin q s) (hq : 1≤q) (laws : ∀j<s,OrderLaw q j (q*j+1))
    {T : Finset ℕ} (tv : T⊆O.V) (proper : T.card<O.V.card) (dpos : 0<d)
    (sz : T.card=q*d+1) (degree : ∀x∈T,d≤(outN O.G T x).card) :
    ∃t∈T, (outN O.G T t).card=d ∧
      (∃x∈T.erase t,(outN O.G T x).card=d ∧ O.G x t=true) ∧
      ∃y∈O.V\T,d<(outN O.G (T.erase t) y).card := by
  have live := card_pos.mp (show 0<T.card by omega)
  obtain ⟨t,tm,light⟩ := PaidLayerDescent.light O laws tv proper live
  have low : (outN O.G T t).card≤d := by
    by_contra! large
    have cmp := Nat.mul_le_mul_left q large
    rw [Nat.mul_succ] at cmp
    omega
  have tight := low.antisymm (degree t tm)
  let W := T.erase t
  have wt : W⊆T := erase_subset _ _
  have wu := wt.trans tv
  have count := card_erase_add_one tm
  change W.card+1=T.card at count
  have pos := Nat.mul_pos (by omega : 0<q) dpos
  have tn : t∉W := notMem_erase _ _
  obtain ⟨⟨x,xw,xlow⟩,y,yw,yhigh⟩ := gap (d:=d) O hq laws wu (card_pos.mp (by omega))
    ⟨t,mem_sdiff.mpr ⟨tv tm,tn⟩⟩ (by omega)
  have row : outN O.G W x=(outN O.G T x).erase t := by
    ext a; simp only [W,mem_outN,mem_erase]; tauto
  rw [row] at xlow
  have ge := degree x (wt xw)
  have xt : t∈outN O.G T x := by
    by_contra absent
    rw [erase_eq_of_notMem absent] at xlow
    omega
  have num := card_erase_add_one xt
  have yt : y∉T := by
    intro ym
    have eq : y=t := by by_contra ne; exact (mem_sdiff.mp yw).2 (mem_erase.mpr ⟨ne,ym⟩)
    subst y
    have le := card_le_card (show outN O.G W t⊆outN O.G T t from fun a aa =>
      mem_outN.mpr ⟨wt (outN_subset aa),(mem_outN.mp aa).2⟩)
    omega
  exact ⟨t,tm,tight,⟨x,xw,by omega,(mem_outN.mp xt).2⟩,y,mem_sdiff.mpr ⟨(mem_sdiff.mp yw).1,yt⟩,yhigh⟩

#print axioms boundary_puncture
#print axioms reachable_barrier
#print axioms gap
#print axioms reverse_gap
end LeanCH.BR.Closure.CoreExchange
