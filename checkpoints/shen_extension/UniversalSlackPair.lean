import checkpoints.shen_extension.FlatPairCover
import checkpoints.shen_extension.CycleCoverWeights

namespace LeanCH.BR.Closure.UniversalSlackPair
open Finset BRq2 BRq3 BR45 WeightedSD ShenCycleSuccessor MarkedCyclePeeling FirstPacketBarrier
open ShortestCycleWeights FlatOverlapDescent

/-- The alternative in which every two cycles meet and cover has no
strict least support. Three cycles require the degree-two deficiency theorem. -/
theorem cover_false {q E V x} {G : Family} (hq : 2≤q) (free : QFree E V q)
    (small : SmallerSmallRow q V.card) (many : 2≤G.card) (cycles : ∀M∈G,Cycle E V q M)
    (wit : ∀u∈V,∀v∈V,E u v=true → ∃M∈G,u∈M ∧ v∈M)
    (xp : ∀i∈V,0≤x i) (strict : ∀i∈V,mass V x<WeightedSD.row q E V x i)
    (cover : ∀A∈G,∀B∈G,A≠B → (A∩B).Nonempty ∧ V=A∪B) : False := by
  classical
  obtain ⟨A,ag,B,bg,ne⟩ := one_lt_card.mp (show 1<G.card by omega)
  have ca := cycles A ag
  have cb := cycles B bg
  have al : A.Nonempty := card_pos.mp (by rw [ca.size]; omega)
  have vl := al.mono ca.sub
  have prop : A≠V := by
    intro eq
    exact ne (eq_of_subset_of_card_le (eq.symm ▸ cb.sub : B⊆A) (by rw [ca.size,cb.size])).symm
  let misses (h : ℕ) := G.filter (fun M => h∉M)
  have atMost (h) (hv : h∈V) : (misses h).card≤1 := by
    apply card_le_one.mpr
    intro L lh M mh
    obtain ⟨lf,hl⟩ := mem_filter.mp lh
    obtain ⟨mf,hm⟩ := mem_filter.mp mh
    by_contra diff
    have unionH := (cover L lf M mf diff).2 ▸ hv
    exact (mem_union.mp unionH).elim hl hm
  by_cases common : ∃h∈V,∀M∈G,h∈M
  · obtain ⟨h,_,all⟩ := common
    apply CycleCoverWeights.common_false hq free ca xp strict (h:=h)
    intro u uv v vv edge
    obtain ⟨M,mf,um,vm⟩ := wit _ uv _ vv edge
    exact ⟨M,cycles M mf,all M mf,um,vm⟩
  have missOne (h) (hv : h∈V) : (misses h).card=1 := by
    refine le_antisymm (atMost h hv) (card_pos.mpr ?_)
    by_contra! empty
    apply common
    refine ⟨h,hv,?_⟩
    intro M mg
    by_contra no
    exact notMem_empty M (empty ▸ (show M∈misses h from mem_filter.mpr ⟨mg,no⟩))
  have cardSplit (v) (vv : v∈V) : (G.filter (v∈·)).card+1=G.card := by
    have eq := card_filter_add_card_filter_not (s:=G) (fun M => v∈M)
    change (G.filter (v∈·)).card+(misses v).card=G.card at eq
    rwa [missOne v vv] at eq
  by_cases large : 4≤G.card
  · have triple (u) (uv : u∈V) (v) (vv : v∈V) (w) (wv : w∈V) : ∃M∈G,u∈M ∧ v∈M ∧ w∈M := by
      let bad := misses u ∪ misses v ∪ misses w
      have lim : bad.card≤3 := by
        have a := card_union_le (misses u) (misses v)
        have b := card_union_le (misses u∪misses v) (misses w)
        change (misses u∪misses v∪misses w).card≤3
        have u1 := atMost u uv
        have v1 := atMost v vv
        have w1 := atMost w wv
        omega
      have outside : (G\bad).Nonempty := sdiff_nonempty.mpr (fun sub => by have := card_le_card sub; omega)
      obtain ⟨M,mh⟩ := outside
      obtain ⟨mg,no⟩ := mem_sdiff.mp mh
      have notBad : M∉misses u ∧ M∉misses v ∧ M∉misses w := by simpa [bad,not_or] using no
      exact ⟨M,mg,by by_contra h; exact notBad.1 (mem_filter.mpr ⟨mg,h⟩),
        by by_contra h; exact notBad.2.1 (mem_filter.mpr ⟨mg,h⟩),
        by by_contra h; exact notBad.2.2 (mem_filter.mpr ⟨mg,h⟩)⟩
    obtain ⟨u,ua,low⟩ := small.induced free A ca.sub prop x (fun i hi => xp i (ca.sub hi)) al
    obtain ⟨w,wh⟩ := card_pos.mp (show 0<(outN E A u).card by rw [ca.heads u ua]; decide)
    obtain ⟨wa,uw⟩ := mem_outN.mp wh
    have same : outN E V u=outN E A u := by
      ext v
      simp only [mem_outN]
      constructor
      · rintro ⟨vv,edge⟩
        obtain ⟨M,mf,um,vm,wm⟩ := triple u (ca.sub ua) v vv w (ca.sub wa)
        have eq := card_le_one.mp ((cycles M mf).heads u um).le _ (mem_outN.mpr ⟨wm,uw⟩) _ (mem_outN.mpr ⟨vm,edge⟩)
        exact ⟨eq ▸ wa,edge⟩
      · exact fun a => ⟨ca.sub a.1,a.2⟩
    have hi := strict u (ca.sub ua)
    rw [WeightedSD.row,outW_eq_mass,same] at hi
    rw [WeightedSD.row,outW_eq_mass] at low
    have ml : mass A x≤mass V x := sum_le_sum_of_subset_of_nonneg ca.sub (fun i hi _ => xp i hi)
    linarith
  · obtain ⟨h,hh⟩ := (cover A ag B bg ne).1
    have hv := ca.sub (mem_inter.mp hh).1
    have pair : ({A,B} : Family)⊆G.filter (h∈·) := by
      intro M mh
      rcases (show M=A ∨ M=B by simpa using mh) with rfl|rfl
      · exact mem_filter.mpr ⟨ag,(mem_inter.mp hh).1⟩
      · exact mem_filter.mpr ⟨bg,(mem_inter.mp hh).2⟩
    have ct := card_le_card pair
    rw [card_pair ne] at ct
    have three := cardSplit h hv
    apply CycleCoverWeights.twofold_false hq free vl cycles wit _ xp strict
    intro v vv
    have count := cardSplit v vv
    omega

/-- The strict normalized source has a pair of actual shortest cycles
whose deletion child has a slack column for every normalized dual law. -/
theorem on_source {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    {F : Family} (sub : F⊆family X) (many : 2≤F.card) {x : ℕ→ℚ} (xp : ∀i∈X.V,0≤x i)
    (strict : ∀i∈X.V,mass X.V x<WeightedSD.row q (graph X.D F) X.V x i) :
    let E := graph X.D F
    ∃G : Family,F⊆G ∧ G⊆family X ∧ graph X.D G=E ∧ (∀M,M∈G ↔ Cycle E X.V q M) ∧
      ∃A∈G,∃B∈G,A≠B ∧
        let U := X.V\(A\B)
        U⊂X.V ∧ B⊆U ∧ ForcedSlack q E U ∧
          ∃p,RealDual q E U 1 p ∧ ∃z∈U,realCol q E U p z<1 := by
  classical
  intro E
  obtain ⟨G,fg,valid,same,cond,_⟩ := FlatCycleFamilyCompletion.on_source X hq small sub
  have cycles (M) (mg : M∈G) := (cond M).mp mg
  have wit (u) (_ : u∈X.V) (v) (_ : v∈X.V) (edge : E u v=true) : ∃M∈G,u∈M ∧ v∈M := by
    obtain ⟨M,mw⟩ := active.mp edge
    obtain ⟨mf,um,vm,_⟩ := mem_col.mp mw
    exact ⟨M,fg mf,um,vm⟩
  have free := PrivateArcEndpoints.graph_free X F
  obtain ⟨A,ag,B,bg,ne,slack⟩ := (FlatPairCover.alternatives hq free small cond wit xp strict).resolve_right
    (cover_false hq free small (many.trans (card_le_card fg)) cycles wit xp strict)
  have ca := cycles A ag
  have cb := cycles B bg
  let U := X.V\(A\B)
  have bu : B⊆U := fun i ib => mem_sdiff.mpr ⟨cb.sub ib,fun g => (mem_sdiff.mp g).2 ib⟩
  have bl : B.Nonempty := card_pos.mp (by rw [cb.size]; omega)
  obtain ⟨u,ug⟩ := sdiff_nonempty.mpr (show ¬A⊆B from fun incl => ne (eq_of_subset_of_card_le incl (by rw [ca.size,cb.size])))
  have proper : U⊂X.V := Finset.ssubset_iff_subset_ne.mpr ⟨sdiff_subset,fun eq =>
    (mem_sdiff.mp (show u∈U from eq.symm ▸ ca.sub (mem_sdiff.mp ug).1)).2 ug⟩
  exact ⟨G,fg,valid,same,cond,A,ag,B,bg,ne,proper,bu,slack,
    FlatCycleFamilyCompletion.realized free small proper (bl.mono bu) slack⟩

#print axioms cover_false
#print axioms on_source
end LeanCH.BR.Closure.UniversalSlackPair
