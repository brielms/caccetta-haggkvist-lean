import checkpoints.shen_extension.CornerHeadRecurrence

namespace LeanCH.BR.Closure.CornerBlockPayment
open Finset BRq2 BRq3 BR45 BRsub WeightedSD CornerHeadRecurrence

/-- With the total block mass preserved, the only rows that need to be
    tested on a proper replacement are its retained labels and the pivot. -/
theorem sparse {q : ℕ} {D : CH.Digraph} {V S : Finset ℕ} {y : ℕ}
    (hq : 2≤q) (free : QFree D V q) (small : SmallerSmallRow q V.card)
    (yv : y∈V) (block : Block D (V.erase y) S) (outside : ∃j∈V\S,j≠y)
    (w : ℕ→ℚ) (pos : ∀i∈V,0<w i) (high : ∀i∈V,mass V w<WeightedSD.row q D V w i)
    {L : Finset ℕ} (proper : L⊂S) (u : ℕ→ℚ) (live : ∀i∈L,0<u i) (total : mass L u=mass S w) :
    let W := V\S
    w y+q*(outW D W w y+outW D L u y)<mass V w ∨
    ∃i∈L,u i+q*(outW D W w i+outW D L u i)<mass V w := by
  classical
  intro W
  let K := W∪L
  let z (i : ℕ) := if i∈L then u i else w i
  have sv : S⊆V := fun _ s=>mem_of_mem_erase (block.1 s)
  have ks : K⊆V := union_subset sdiff_subset (proper.subset.trans sv)
  have diff : Disjoint W L := disjoint_left.mpr (fun _ iw il=>(mem_sdiff.mp iw).2 (proper.subset il))
  have onW {i} (iw : i∈W) : z i=w i := ite_eq_right (fun il=>disjoint_left.mp diff iw il)
  have onL {i} (il : i∈L) : z i=u i := ite_eq_left il
  have wz : mass W z=mass W w := sum_congr rfl fun _ iw=>onW iw
  have uz : mass L z=mass L u := sum_congr rfl fun _ il=>onL il
  have zm : mass K z=mass V w := (sum_union diff).trans (by
    change mass W z+mass L z=mass V w
    rw [wz,uz,total]; exact sum_sdiff sv)
  have paid (i) : WeightedSD.row q D K z i=z i+q*(outW D W w i+outW D L u i) := by
    have ext : outW D W z i=outW D W w i := sum_congr rfl fun j jw=>by rw [onW jw]
    have int : outW D L z i=outW D L u i := sum_congr rfl fun j jl=>by rw [onL jl]
    rw [WeightedSD.row,show outW D K z i=outW D W z i+outW D L z i from sum_union diff,ext,int]
  have unchanged (i) (iw : i∈W) (iy : i≠y) : WeightedSD.row q D K z i=WeightedSD.row q D V w i := by
    obtain ⟨iv,off⟩ := mem_sdiff.mp iw
    have iu := mem_erase.mpr ⟨iy,iv⟩
    obtain ⟨r,rs⟩ := (ssubset_iff_of_subset proper.subset).mp proper
    have adj {j} (js : j∈S) : D i j=D i r := block.2.2.1 j js r rs.1 i iu off
    have equal : outW D L u i=outW D S w i := by
      cases bit : D i r with
      | false =>
        have a : outW D L u i=0 := sum_eq_zero fun j jl=>by simp [(adj (proper.subset jl)).trans bit]
        have b : outW D S w i=0 := sum_eq_zero fun j js=>by simp [(adj js).trans bit]
        exact a.trans b.symm
      | true =>
        have a : outW D L u i=mass L u := sum_congr rfl fun j jl=>by simp [(adj (proper.subset jl)).trans bit]
        have b : outW D S w i=mass S w := sum_congr rfl fun j js=>by simp [(adj js).trans bit]
        exact a.trans (total.trans b.symm)
    rw [paid,onW iw,equal,WeightedSD.row,outW_split sv w i,add_comm (outW D S w i)]
  have yw : y∈W := mem_sdiff.mpr ⟨yv,fun ys=>(mem_erase.mp (block.1 ys)).1 rfl⟩
  by_contra! all
  have feasible (i) (ik : i∈K) : mass K z≤WeightedSD.row q D K z i := by
    rw [zm]
    rcases mem_union.mp ik with iw|il
    · by_cases iy : i=y
      · subst i; rw [paid,onW yw]; exact all.1
      · rw [unchanged i iw iy]; exact (high i (mem_sdiff.mp iw).1).le
    · rw [paid,onL il]; exact all.2 i il
  have strictSub : K⊂V := Finset.ssubset_iff_subset_ne.mpr ⟨ks,fun eq=>by
    obtain ⟨i,ih⟩ := exists_of_ssubset proper
    have ik : i∈K := by rw [eq]; exact sv ih.1
    exact (mem_union.mp ik).elim (fun iw=>(mem_sdiff.mp iw).2 ih.1) ih.2⟩
  have positive (i) (ik : i∈K) : 0<z i := by
    rcases mem_union.mp ik with iw|il
    · rw [onW iw]; exact pos i (mem_sdiff.mp iw).1
    · rw [onL il]; exact live i il
  obtain ⟨j,jw,jy⟩ := outside
  have eq := positive_feasible_rows_tight_of_smallRow hq (small D K (card_lt_card strictSub) (free.mono_set ks))
    z positive feasible j (mem_union_left L jw)
  rw [unchanged j jw jy,zm] at eq
  exact (high j (mem_sdiff.mp jw).1).ne' eq

/-- Concentrating the block on a child of y leaves only that child
    underpaid. Concentrating it on a parent pays the parent strictly
    and leaves only y underpaid. Both experiments use the same weights. -/
theorem two_deletions {q : ℕ} {D : CH.Digraph} {V S : Finset ℕ} {y v t : ℕ}
    (hq : 2≤q) (free : QFree D V q) (small : SmallerSmallRow q V.card)
    (yv : y∈V) (block : Block D (V.erase y) S) (outside : ∃j∈V\S,j≠y)
    (vs : v∈S) (yvEdge : D y v=true) (ts : t∈S) (ty : D t y=true)
    (w : ℕ→ℚ) (pos : ∀i∈V,0<w i) (high : ∀i∈V,mass V w<WeightedSD.row q D V w i) :
    let W := V\S
    mass S w+q*outW D W w v<mass V w ∧ mass V w<mass S w+q*outW D W w t ∧
    w y+q*outW D W w y<mass V w := by
  classical
  intro W
  have sv : S⊆V := fun _ s=>mem_of_mem_erase (block.1 s)
  have ys : y∉S := fun s=>(mem_erase.mp (block.1 s)).1 rfl
  have ms : 0<mass S w := sum_pos (fun i si=>pos i (sv si)) ⟨v,vs⟩
  have one (r) (rs : r∈S) :
      w y+q*(outW D W w y+(if D y r=true then mass S w else 0))<mass V w ∨
      mass S w+q*outW D W w r<mass V w := by
    have room : ({r}:Finset ℕ)⊂S := Finset.ssubset_iff_subset_ne.mpr ⟨singleton_subset_iff.mpr rs,fun eq=>by
      have size := block.2.1
      rw [←eq,card_singleton] at size
      omega⟩
    have test := sparse hq free small yv block outside w pos high room (fun _=>mass S w)
      (fun _ _=>ms) (by simp [mass])
    have rr := Bool.eq_false_iff.mpr (loopfree free (by omega) (sv rs))
    simpa [outW,sum_singleton,rr,W] using test
  have light := small.induced free S sv (fun eq=>ys (eq ▸ yv))
  obtain ⟨i,si,low⟩ := light w (fun i si=>(pos i (sv si)).le) ⟨t,ts⟩
  have outLe : outW D W w i≤outW D W w t := by
    apply sum_le_sum
    intro j jw
    obtain ⟨jv,js⟩ := mem_sdiff.mp jw
    by_cases jy : j=y
    · subst j
      rw [ite_eq_left ty]
      split <;> first | rfl | exact (pos _ yv).le
    · rw [block.2.2.2 i si t ts j (mem_erase.mpr ⟨jy,jv⟩) js]
  have pay := high i (sv si)
  rw [WeightedSD.row,outW_split sv w i,mul_add] at pay
  unfold WeightedSD.row at low
  have qt := mul_le_mul_of_nonneg_left outLe (Nat.cast_nonneg (α:=ℚ) q)
  have tHigh : mass V w<mass S w+q*outW D W w t := by linarith only [pay,low,qt]
  have yt : D y t=false := Bool.eq_false_iff.mpr (fun e=>free y 2 (by decide) hq
    (.step (sv ts) e (.step yv ty (.refl _))))
  have yLow := (one t ts).resolve_right (not_lt.mpr tHigh.le)
  simp only [yt,Bool.false_eq_true,ite_false,add_zero] at yLow
  have cap : outW D S w y≤mass S w := by
    rw [outW_eq_mass]
    exact mass_mono (filter_subset _ _) (fun j js=>(pos j (sv js)).le)
  have yHigh := high y yv
  rw [WeightedSD.row,outW_split sv w y] at yHigh
  have qcap := mul_le_mul_of_nonneg_left cap (Nat.cast_nonneg (α:=ℚ) q)
  have vLow := one v vs
  rw [ite_eq_left yvEdge] at vLow
  have paidY : ¬w y+q*(outW D W w y+mass S w)<mass V w := by
    change ¬w y+q*(outW D (V\S) w y+mass S w)<mass V w
    linarith only [yHigh,qcap]
  exact ⟨vLow.resolve_left paidY,tHigh,yLow⟩

open ShortestCycleWeights FirstPacketBarrier MarkedCyclePeeling SharedArcComponentExchange

/-- The capstone's source already supplies a strictly feasible weight
    on every native row. No new payment or weight hypothesis is needed. -/
theorem on_source {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    (F : Family) {y h : X.V} (fresh : Fresh X F (y,h)) {S}
    (bl : OldBlockAt X.D (graph X.D F) X.V y S) :
    let w := fun j=>(X.weights j:ℚ)
    let W := X.V\S
    (∀L⊂S,∀u:ℕ→ℚ,(∀i∈L,0<u i) → mass L u=mass S w →
      w y+q*(outW X.D W w y+outW X.D L u y)<mass X.V w ∨
      ∃i∈L,u i+q*(outW X.D W w i+outW X.D L u i)<mass X.V w) ∧
    ∀v∈S,X.D y v=true → ∀t∈S,X.D t y=true →
      mass S w+q*outW X.D W w v<mass X.V w ∧ mass X.V w<mass S w+q*outW X.D W w t ∧
      w y+q*outW X.D W w y<mass X.V w := by
  intro w W
  have outside : h.val∉S := fun hs=>Bool.noConfusion
    (fresh.2.2.2.symm.trans ((bl.2.1 h hs).2.trans fresh.2.2.1))
  have ne : h.val≠y.val := fun e=>loopfree X.free (by omega) y.property (e ▸ fresh.2.2.1)
  have kept : ∃j∈W,j≠y.val := ⟨h,mem_sdiff.mpr ⟨h.property,outside⟩,ne⟩
  have wp (i) (iv : i∈X.V) : 0<w i := by
    change (0:ℚ)<(X.weights i:ℚ)
    exact_mod_cast X.positive i iv
  exact ⟨fun _ less u p m=>sparse hq X.free small y.property bl.1 kept w wp X.strict less u p m,
    fun _ vs yv _ ts ty=>two_deletions hq X.free small y.property bl.1 kept vs yv ts ty w wp X.strict⟩

/-- An actual shorter host when a pivot return has q−1 arcs: keep its
    q labels, divide the block mass equally, and preserve every exterior
    row except the pivot. Three scalar checks suffice for this repair
    because all path rows see the same exterior away from the pivot. -/
theorem path_cut {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    (F : Family) {y h : X.V} (fresh : Fresh X F (y,h)) {S}
    (bl : OldBlockAt X.D (graph X.D F) X.V y S) (room : q<S.card)
    (returns : InternalReturns q (graph X.D F) S y)
    {v t} (vs : v∈S) (yv : graph X.D F y v=true) (ts : t∈S) (ty : graph X.D F t y=true)
    (off : graph X.D F t v=false) :
    let w := fun j=>(X.weights j:ℚ)
    let W := X.V\S
    let c := mass S w / q
    w y+q*(outW X.D W w y+c)<mass X.V w ∨
      c+q*outW X.D W w t<mass X.V w ∨ c+q*(outW X.D W w v+c)<mass X.V w := by
  classical
  intro w W c
  have path := returns v vs yv t ts ty
  rw [ite_eq_right (Bool.eq_false_iff.mp off)] at path
  obtain ⟨f,fv,ft,arcs⟩ := path.toFun
  let L := (range ((q-1)+1)).image f
  have sv : S⊆X.V := fun _ s=>mem_of_mem_erase (bl.1.1 s)
  have native {i j} (e : graph X.D F i j=true) : X.D i j=true := (mem_col.mp (active.mp e).choose_spec).2.2.2
  have ls : L⊆S := by
    intro i il
    obtain ⟨k,kr,rfl⟩ := mem_image.mp il
    have bound := mem_range.mp kr
    cases k with
    | zero => exact fv ▸ vs
    | succ k => exact (arcs k (by omega)).1
  have uniq := short_walk_index_injective ((PrivateArcEndpoints.graph_free X F).mono_set sv)
    (by omega : q-1≤q) f arcs
  have count : L.card=q := by
    dsimp [L]
    rw [card_image_of_injOn uniq,card_range]
    omega
  have proper : L⊂S := Finset.ssubset_iff_subset_ne.mpr ⟨ls,fun eq=>by rw [←eq,count] at room; omega⟩
  have cpos : 0<c := div_pos (sum_pos (fun i si=>by
    change (0:ℚ)<(X.weights i:ℚ); exact_mod_cast X.positive i (sv si)) ⟨v,vs⟩) (by exact_mod_cast (by omega : 0<q))
  have total : mass L (fun _=>c)=mass S w := by
    have nz : (q:ℚ)≠0 := by exact_mod_cast (by omega : q≠0)
    simp [mass,c,count,nz,mul_div_cancel₀]
  have cut := (on_source X hq small F fresh bl).1 L proper (fun _=>c) (fun _ _=>cpos) total
  have price {i j} (jl : j∈L) (ij : X.D i j=true) : c≤outW X.D L (fun _=>c) i := by
    rw [outW_eq_mass]
    have bound := mass_mono (singleton_subset_iff.mpr (mem_outN.mpr ⟨jl,ij⟩))
      (w:=fun _=>c) (fun _ _=>cpos.le)
    simpa only [mass,sum_singleton] using bound
  have vl : v∈L := fv ▸ mem_image_of_mem f (mem_range.mpr (by omega : 0<(q-1)+1))
  have vy : X.D v y=false := Bool.eq_false_iff.mpr (fun back=>X.free y 2 (by decide) hq
    (.step (sv vs) (native yv) (.step y.property back (.refl _))))
  have base {i} (il : i∈L) : outW X.D W w v≤outW X.D W w i := by
    apply sum_le_sum
    intro j jw
    obtain ⟨jv,js⟩ := mem_sdiff.mp jw
    by_cases jy : j=y.val
    · subst j; rw [ite_eq_right (Bool.eq_false_iff.mp vy)]
      have yn : 0≤w y := Nat.cast_nonneg (X.weights y)
      split <;> first | exact yn | rfl
    · rw [bl.1.2.2.2 v vs i (ls il) j (mem_erase.mpr ⟨jy,jv⟩) js]
  have qp : (0:ℚ)≤q := Nat.cast_nonneg _
  rcases cut with first|⟨i,il,under⟩
  · change w y+q*(outW X.D W w y+outW X.D L (fun _=>c) y)<mass X.V w at first
    exact Or.inl ((add_le_add le_rfl (mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (price vl (native yv))) qp)).trans_lt first)
  · right
    change c+q*(outW X.D W w i+outW X.D L (fun _=>c) i)<mass X.V w at under
    by_cases it : i=t
    · subst i
      have nonneg : 0≤outW X.D L (fun _=>c) t := by
        rw [outW_eq_mass]; exact mass_nonneg (fun _ _=>cpos.le)
      exact Or.inl ((add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_right nonneg) qp)).trans_lt under)
    · obtain ⟨k,kr,eq⟩ := mem_image.mp il
      have bound := mem_range.mp kr
      have before : k<q-1 := by
        by_contra! no
        have same : k=q-1 := by omega
        exact it (eq.symm.trans (same ▸ ft))
      have jl : f (k+1)∈L := mem_image_of_mem f (mem_range.mpr (by omega))
      have edge : X.D i (f (k+1))=true := by rw [←eq]; exact native (arcs k before).2
      exact Or.inr ((add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (add_le_add (base il) (price jl edge)) qp)).trans_lt under)

end LeanCH.BR.Closure.CornerBlockPayment
#print axioms LeanCH.BR.Closure.CornerBlockPayment.sparse
#print axioms LeanCH.BR.Closure.CornerBlockPayment.two_deletions
#print axioms LeanCH.BR.Closure.CornerBlockPayment.on_source
#print axioms LeanCH.BR.Closure.CornerBlockPayment.path_cut
