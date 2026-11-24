import checkpoints.shen_extension.IndependentReturnGeometry
import Mathlib.Combinatorics.SetFamily.LYM

namespace LeanCH.BR.Closure.ReturnIncidenceAntichain
open Finset BRq2 BRq3 BR45 WeightedSD LabelledLeakageCapacity TwoParentReturnPivot

noncomputable def returns (q : ℕ) (E : CH.Digraph) (V : Finset ℕ) (b p : ℕ) :=
  outN E (region q E V b) p

noncomputable def innerNonneighbours (q : ℕ) (E : CH.Digraph) (V : Finset ℕ) (b p : ℕ) :=
  (region q E V b).filter (fun k=>k≠p ∧ E p k=false ∧ E k p=false)

noncomputable def labels (q : ℕ) (E : CH.Digraph) (V : Finset ℕ) (b p : ℕ) :=
  if q=3 then innerNonneighbours q E V b p else insert b (innerNonneighbours q E V b p)

/-- Between two returns that receive no internal arcs, a saturated walk
separates their incoming profiles on the actual inner nonneighbours.
Only the deleted root can be an additional label, and only above cutoff 3. -/
theorem last_label {q E V b p y I t h} (hq : 3≤q) (free : QFree E V q) (sat : BRsub.Sat q E V)
    (sep : ShenParentIntersection.Separated E V V) (bv : b∈V) (parents : inN E V b={p,y})
    (within : I⊆returns q E V b p) (none : ∀i∈I,∀s∈returns q E V b p,E s i=false)
    (ti : t∈I) (hi : h∈I) (ne : t≠h) :
    ∃k∈labels q E V b p,E k h=true ∧ E k t=false := by
  obtain ⟨tr,pt⟩ := mem_outN.mp (within ti)
  obtain ⟨hr,ph⟩ := mem_outN.mp (within hi)
  have tv := BRsub.ballSet_subset tr
  have hv := BRsub.ballSet_subset hr
  have par : p∈inN E V b := parents ▸ mem_insert_self _ _
  have pv := (mem_inN.mp par).1
  have two : 2≤q := by omega
  have miss : E h t≠true := by simp [none t ti h (within hi)]
  obtain ⟨_,j,le,path⟩ := mem_ball.mp (sat t tv h hv miss)
  cases j with
  | zero => cases path; exact (ne rfl).elim
  | succ l =>
    obtain ⟨k,pre,_,kh⟩ := path.unsnoc
    have lp : 1≤l := by
      by_contra! low
      have z : l=0 := by omega
      subst l; cases pre
      exact Bool.noConfusion (kh.symm.trans (none h hi t (within ti)))
    have kv : k∈V := by
      cases l with
      | zero => omega
      | succ _ => exact pre.unsnoc.choose_spec.2.1
    have kt : E k t=false := by
      cases e : E k t
      · rfl
      · exact (free t _ (by omega) (by omega) (pre.snoc tv e)).elim
    have nkp : E k p=false := by
      cases kp : E k p
      · rfl
      · exact (free p _ (by omega) (by omega) ((Walk.step tv pt pre).snoc pv kp)).elim
    have kp : k≠p := fun eq=>free p _ (by omega) (by omega) (eq ▸ Walk.step tv pt pre)
    obtain ⟨i,iv,ib,ih⟩ := sep b bv h hv ((saturated_region two free sat bv hv).mp hr).1
    have either : i∈({p,y}:Finset ℕ) := parents ▸ mem_inN.mpr ⟨iv,ib⟩
    have iy : i=y := mem_singleton.mp ((mem_insert.mp either).resolve_left (fun eq=>Bool.noConfusion ((eq ▸ ih).symm.trans ph)))
    subst i
    have ky : k≠y := fun eq=>Bool.noConfusion (ih.symm.trans (eq ▸ kh))
    refine ⟨k,?_,kh,kt⟩
    by_cases kb : k=b
    · subst k
      have notThree : q≠3 := by
        rintro rfl
        have one : l=1 := by omega
        subst l
        obtain ⟨a,zero,_,tb⟩ := pre.unsnoc
        cases zero
        exact ((saturated_region (by decide) free sat bv tv).mp tr).2 tb
      simp [labels,notThree]
    · have noB : E k b≠true := fun arc=>by
        have par' : k∈({p,y}:Finset ℕ) := parents ▸ mem_inN.mpr ⟨kv,arc⟩
        simp [kp,ky] at par'
      have kr := (saturated_region two free sat bv kv).mpr ⟨kb,noB⟩
      have pk : E p k=false := by
        cases arc : E p k
        · rfl
        · exact Bool.noConfusion (kh.symm.trans (none h hi k (mem_outN.mpr ⟨kr,arc⟩)))
      have mem : k∈innerNonneighbours q E V b p := mem_filter.mpr ⟨kr,kp,pk,nkp⟩
      unfold labels; split_ifs <;> simp [mem]

/-- Every label that receives no internal arc needs its own incomparable
incoming profile. This applies to any selected subset of such labels. -/
theorem zero_count {q E V b p y I} (hq : 3≤q) (free : QFree E V q) (sat : BRsub.Sat q E V)
    (sep : ShenParentIntersection.Separated E V V) (bv : b∈V) (parents : inN E V b={p,y})
    (within : I⊆returns q E V b p) (none : ∀h∈I,∀t∈returns q E V b p,E t h=false) :
    let m := (labels q E V b p).card
    I.card≤m.choose (m/2) := by
  classical
  intro m
  let M := labels q E V b p
  let f (h : ℕ) : Finset M := univ.filter (fun k=>E k h=true)
  have anti {h t} (hi : h∈I) (ti : t∈I) (ne : h≠t) : ¬f h⊆f t := by
    obtain ⟨k,km,kh,kt⟩ := last_label hq free sat sep bv parents within none ti hi ne.symm
    intro sub
    have mh : (⟨k,km⟩ : M)∈f h := mem_filter.mpr ⟨mem_univ _,kh⟩
    exact Bool.noConfusion (kt.symm.trans (mem_filter.mp (sub mh)).2)
  have inj : Set.InjOn f (↑I : Set ℕ) := by
    intro h hi t ti eq
    by_contra ne; exact anti hi ti ne eq.subset
  have incomparable : IsAntichain (·⊆·) (↑(I.image f) : Set (Finset M)) := by
    intro A ha B hb ne
    obtain ⟨h,hi,rfl⟩ := mem_image.mp ha
    obtain ⟨t,ti,rfl⟩ := mem_image.mp hb
    exact anti hi ti (fun eq=>ne (congrArg f eq))
  simpa only [card_image_of_injOn inj,Fintype.card_coe] using incomparable.sperner

/-- For all native returns at p, either a retained common head exists,
or the union of mandatory banks contains all but a bounded number of
return labels. The inequality also controls their original weight. -/
theorem sponsored {q E V b p y} (hq : 3≤q) (free : QFree E V q) (sat : BRsub.Sat q E V)
    (sep : ShenParentIntersection.Separated E V V) (bv : b∈V) (parents : inN E V b={p,y})
    (w : ℕ→ℚ) (cap : ∀i∈V,(q:ℚ)^2*w i≤1) :
    let U := V.erase b
    let S := returns q E V b p
    let K := S.biUnion (fun t=>bank q E U t y)
    let m := (labels q E V b p).card
    (∃t∈S,∃h∈outN E U p,h∈outN E U t \ bank q E U t y) ∨
      (S \ K).card≤m.choose (m/2) ∧ S.card≤(S∩K).card+m.choose (m/2) ∧
      (q:ℚ)^2*mass S w≤(q:ℚ)^2*mass (S∩K) w+m.choose (m/2) := by
  intro U S K m
  by_cases common : ∃t∈S,∃h∈outN E U p,h∈outN E U t \ bank q E U t y
  · exact Or.inl common
  right
  have capped (j) (js : j∈S) := cap j (BRsub.ballSet_subset (outN_subset js))
  have none (h) (hi : h∈S\K) (t) (ts : t∈S) : E t h=false := by
    obtain ⟨hs,hk⟩ := mem_sdiff.mp hi
    obtain ⟨hr,ph⟩ := mem_outN.mp hs
    have hv := BRsub.ballSet_subset hr
    have hu : h∈U := mem_erase.mpr ⟨((saturated_region (by omega) free sat bv hv).mp hr).1,hv⟩
    cases arc : E t h
    · rfl
    · exact (common ⟨t,ts,h,mem_outN.mpr ⟨hu,ph⟩,mem_sdiff.mpr ⟨mem_outN.mpr ⟨hu,arc⟩,
        fun hb=>hk (mem_biUnion.mpr ⟨t,ts,hb⟩)⟩⟩).elim
  have cnt := zero_count hq free sat sep bv parents (sdiff_subset : S\K⊆S) none
  have dis : Disjoint (S\K) (S∩K) := disjoint_left.mpr (fun _ hi hj=>(mem_sdiff.mp hi).2 (mem_inter.mp hj).2)
  have cards := card_union_of_disjoint dis
  rw [sdiff_union_inter] at cards
  have weights : mass (S\K) w+mass (S∩K) w=mass S w := by
    simp only [mass,←sum_union dis,sdiff_union_inter]
  have bound : (q:ℚ)^2*mass (S\K) w≤(S\K).card := by
    simpa [mass,mul_sum] using sum_le_sum (s:=S\K) (g:=fun _=> (1:ℚ)) (fun j hi=>capped j (mem_sdiff.mp hi).1)
  change (S\K).card≤m.choose (m/2) at cnt
  refine ⟨cnt,by omega,?_⟩
  linarith only [congrArg (fun s : ℚ=>(q:ℚ)^2*s) weights,bound,(show ((S\K).card:ℚ)≤m.choose (m/2) by exact_mod_cast cnt)]

#print axioms last_label
#print axioms zero_count
#print axioms sponsored
end LeanCH.BR.Closure.ReturnIncidenceAntichain
