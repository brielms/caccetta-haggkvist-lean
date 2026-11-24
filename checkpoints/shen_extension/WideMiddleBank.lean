import checkpoints.shen_extension.WideShortCycleExit

namespace LeanCH.BR.LowShellCycleSelection
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking PhysicalCycleStock OneOmissionSinkBank

theorem wide_middle_bank {D V q r C u} (free : QFree D V q) (hq : 6≤q)
    (reg : OutEq r D V) (uv : u∈V) (fits : r≤q+2) (len : q<C.card)
    (rooted : ∀x∈C,Rooted D V x C) (first : C⊆outN D V u)
    (upper : (N2 D V u).card≤r) (wide : r<(exterior D V C).card)
    (low : (ball D V u 3).card≤3*r) :
    (N3 D V u).card+1=r ∧ ∃K⊆N2 D V u,q<K.card ∧
      (N2 D V u\K).card≤1 ∧ ∀x∈K,Rooted D V x K := by
  let X := outN D V u
  let Y := N2 D V u
  let Z := N3 D V u
  have xv : X⊆V := outN_subset
  have yv : Y⊆V := fun _ h=>N2_subV h
  obtain ⟨ys,miss⟩ := wide_all_rows free (by omega) reg uv fits len rooted first upper wide
  have eq := wide_short_false free hq reg uv fits len rooted first upper wide
  have b1 := card_B1 (free.mono_bound (by omega : 4≤q)) uv
  rw [reg _ uv] at b1
  have b2 := @card_B2 D V u
  have b3 := @card_B3 D V u
  have zs : Z.card+1=r := by dsimp [Z]; omega
  refine ⟨zs,?_⟩
  have cyclic : ¬QFree D Y Y.card := by
    intro dag
    have ret s (sm : s∈sinks D Y) : ∃x∈X,D s x=true := by
      by_contra! none
      have out : outN D V s⊆Z := by
        intro a am
        apply (headY (free.mono_bound (by omega : 4≤q)) uv (mem_filter.mp sm).1 (outN_subset am) (mem_outN.mp am).2).resolve_left
        intro h
        rcases mem_union.mp h with ax|ay
        · have := none a ax; have := (mem_outN.mp am).2; simp_all
        · exact (mem_filter.mp sm).2 a ay (mem_outN.mp am).2
      have bound := card_le_card out
      rw [reg _ (yv (mem_filter.mp sm).1)] at bound
      omega
    obtain ⟨S,_,charge,cover⟩ := split_sink_budget free yv xv first dag (by omega : 2+2≤q)
      (fun x xm=>((rooted x xm).one x xm).ge) miss ret
    have gaps := card_sdiff_of_subset first
    have bound := card_le_card first
    have dx := reg u uv
    change (X\C).card=X.card-C.card at gaps
    change X.card=r at dx
    change C.card≤X.card at bound
    have slots : (X\C).card=1 := by
      have bal := gate_balance free (by omega) uv first
      change _+_+(exterior D V C).card=(X\C).card+_ at bal
      omega
    have small : S.card≤2 := by
      by_contra! many
      have := Nat.mul_le_mul_right (q-1) (show 3≤S.card by omega)
      omega
    change Y.card=r at ys
    omega
  obtain ⟨K,ky,size,cy⟩ := actual_cycle free (by omega) yv cyclic
  exact ⟨K,ky,size,by change (Y\K).card≤1; have := card_sdiff_of_subset ky; change Y.card=r at ys; omega,cy⟩

/-- If the extra label receives too many arcs from K, it can afford
neither a K-head nor a first-layer head. Every other K row is full on Z. -/
theorem full_second_bank {D V X Y Z K q r d} (free : QFree D V q) (hq : 3≤q)
    (reg : OutEq r D V) (xv : X⊆V) (yv : Y⊆V) (ky : K⊆Y) (len : q<K.card)
    (cy : ∀v∈K,Rooted D V v K) (slots : (Y\K).card≤1) (size : Z.card+1=r)
    (menu : ∀v∈Y,outN D V v⊆(X∪Y)∪Z) (miss : ∀x∈X,(Y\outN D V x).card≤d)
    (time : d<q-1) (cap : (Y\K).Nonempty → K.card≤q-1+d) :
    K.card≤(K.filter (fun v=>Z⊆outN D V v)).card+d := by
  classical
  let A := K.filter (fun v=>Z⊆outN D V v)
  have safe v (vm : v∈K) x (xm : x∈X) : D v x≠true := by
    intro arc
    have bill := crossed_omissions free (by omega) yv ky len cy vm (xv xm) arc
    have := miss x xm
    omega
  have need a (am : a∈K\A) : ∃b∈Y\K,D a b=true := by
    by_contra! none
    have sub : outN D V a⊆outN D K a∪(Z∩outN D V a) := by
      intro b bm
      have arc := (mem_outN.mp bm).2
      rcases mem_union.mp (menu _ (ky (mem_sdiff.mp am).1) bm) with early|bz
      · have by' := (mem_union.mp early).resolve_left (fun bx=>safe _ (mem_sdiff.mp am).1 _ bx arc)
        have bk : b∈K := by by_contra off; have := none b (mem_sdiff.mpr ⟨by',off⟩); simp_all
        exact mem_union_left _ (mem_outN.mpr ⟨bk,arc⟩)
      · exact mem_union_right _ (mem_inter.mpr ⟨bz,bm⟩)
    have h := (card_le_card sub).trans (card_union_le _ _)
    rw [reg _ (yv (ky (mem_sdiff.mp am).1)),(cy _ (mem_sdiff.mp am).1).one _ (mem_sdiff.mp am).1] at h
    have eq := eq_of_subset_of_card_le (inter_subset_left (s₂:=outN D V a) : Z∩outN D V a⊆Z) (by omega)
    exact (mem_sdiff.mp am).2 (mem_filter.mpr ⟨(mem_sdiff.mp am).1,eq ▸ inter_subset_right⟩)
  have count := card_sdiff_of_subset (filter_subset (fun v=>Z⊆outN D V v) K)
  change (K\A).card=K.card-A.card at count
  change K.card≤A.card+d
  by_contra! excess
  obtain ⟨a,am⟩ := card_pos.mp (by omega : 0<(K\A).card)
  obtain ⟨b,bm,_⟩ := need a am
  have smallK := cap ⟨b,bm⟩
  have bv := yv (mem_sdiff.mp bm).1
  have feed v (vm : v∈K\A) : D v b=true := by
    obtain ⟨w,wm,e⟩ := need v vm
    exact card_le_one.mp slots w wm b bm ▸ e
  have off : outN D V b⊆Z := by
    intro x xm
    have e := (mem_outN.mp xm).2
    apply (mem_union.mp (menu _ (mem_sdiff.mp bm).1 xm)).resolve_left
    intro hit
    rcases mem_union.mp hit with xx|xy
    · have blocked : K\A⊆Y\outN D V x := fun v vm=>mem_sdiff.mpr ⟨ky (mem_sdiff.mp vm).1,fun into=>
        free b 3 (by decide) hq (.step (xv xx) e (.step (outN_subset into) (mem_outN.mp into).2 (.step bv (feed v vm) (.refl b))))⟩
      have := (card_le_card blocked).trans (miss x xx)
      omega
    · by_cases xk : x∈K
      · have lim := exception_parents free (ky.trans yv) (fun v vm=>((cy v vm).one v vm).ge)
          bv xk (Walk.step (yv xy) e (.refl x)) (by omega)
        have seen : K\A⊆inN D K b := fun v vm=>mem_inN.mpr ⟨(mem_sdiff.mp vm).1,feed v vm⟩
        have := card_le_card seen
        omega
      have same := card_le_one.mp slots x (mem_sdiff.mpr ⟨xy,xk⟩) b bm
      exact loopfree free (by omega) bv (same ▸ e)
  have h := card_le_card off
  rw [reg _ bv] at h
  omega

#print axioms full_second_bank
#print axioms wide_middle_bank
end LeanCH.BR.LowShellCycleSelection
