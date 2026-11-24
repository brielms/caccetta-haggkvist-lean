import checkpoints.shen_extension.dot_tensor_research.DotDegreeSixQ5Bank_20261121

namespace LeanCH.BR.DotDegreeSix
open Finset BRq2 BRq3 BR45 BRsGen DotDegreeSevenLow
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem no_short_banks_of_six_certificate
    {D : CH.Digraph} {V : Finset ℕ} {K : Finset (Finset ℕ)}
    (hf : QFree D V 5) (hn : V.card=30)
    (L : Finset ℕ) (roots escorts : Finset ℕ → Finset ℕ)
    (hL : L = K.biUnion roots)
    (rsub : ∀ B∈K, roots B⊆V) (hne : ∀ B∈K, (roots B).Nonempty)
    (ed : (↑K : Set (Finset ℕ)).PairwiseDisjoint roots)
    (esub : ∀ B∈K, escorts B⊆V) (e4 : ∀ B∈K, (escorts B).card=6)
    (miss : ∀ B∈K, ∀ u∈roots B, (roots B).erase u ⊆ missingMixed D V u)
    (pay : ∀ v∈V, 31+(K.filter (fun B => v∈escorts B)).card ≤
      mixedScore D V v + (if v∈L then 1 else 0)) :
    K=∅ := by
  classical
  have lv : L⊆V := hL ▸ biUnion_subset.mpr rsub
  have tax : (∑ v∈V,(K.filter (fun B => v∈escorts B)).card)=6*K.card := by
    calc
      _ = ∑ v∈V, ∑ B∈K, (if v∈escorts B then (1 : ℕ) else 0) := by
        apply sum_congr rfl
        intro v hv
        rw [←sum_filter]
        simp
      _ = ∑ B∈K, ∑ v∈V, (if v∈escorts B then (1 : ℕ) else 0) := sum_comm
      _ = ∑ B∈K,(6 : ℕ) := by
        apply sum_congr rfl
        intro B hB
        simp [sum_ite_mem, inter_eq_right.mpr (esub B hB),e4 B hB]
      _ = 6*K.card := by rw [Finset.sum_const_nat (fun _ _ => rfl),Nat.mul_comm]
  have sumPay := sum_le_sum pay
  have cL : (∑ v∈V, if v∈L then (1 : ℕ) else 0)=L.card := by
    simp [sum_ite_mem, inter_eq_right.mpr lv]
  rw [sum_add_distrib,sum_add_distrib,tax,cL,
    Finset.sum_const_nat (fun _ _ => rfl),hn] at sumPay
  have budget := mixedScore_with_missing hf
  rw [hn] at budget
  have missL :
      (∑ B∈K, (roots B).card*((roots B).card-1)) ≤ ∑ v∈V,(missingMixed D V v).card := by
    calc
      _ = ∑ B∈K, ∑ v∈roots B, ((roots B).card-1) := by
        simp only [Finset.sum_const_nat (fun _ _ => rfl)]
      _ ≤ ∑ B∈K, ∑ v∈roots B, (missingMixed D V v).card := by
        apply sum_le_sum
        intro B hB
        apply sum_le_sum
        intro v hv
        simpa only [card_erase_of_mem hv] using card_le_card (miss B hB v hv)
      _ = ∑ v∈L,(missingMixed D V v).card := by rw [hL,sum_biUnion ed]
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg lv (fun _ _ _ => Nat.zero_le _)
  have cardL : L.card=∑ B∈K,(roots B).card := by rw [hL,card_biUnion ed]
  have gain (B : Finset ℕ) (hB : B∈K) :
      (roots B).card+1≤(roots B).card*((roots B).card-1)+6 := by
    have g : 0<(roots B).card := card_pos.mpr (hne B hB)
    let k := (roots B).card
    change k+1≤k*(k-1)+6
    cases k with
    | zero => simp
    | succ i =>
      cases i with
      | zero => decide
      | succ j => simp [Nat.mul_add, Nat.mul_comm]; omega
  have g := sum_le_sum gain
  rw [sum_add_distrib,←cardL,sum_add_distrib,
    Finset.sum_const_nat (fun _ _ => rfl),Finset.sum_const_nat (fun _ _ => rfl)] at g
  have cn : K.card=0 := by omega
  exact card_eq_zero.mp cn


/-- At the critical order every row must lie on the exact complementary
    seam; the apparent negative rows have disjoint paid C6 banks. -/
theorem six_order30_uniform {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V 5) (ho : OutEq 6 D V) (hn : V.card=30) :
    ∀ v∈V, (ball D V v 2).card=13 ∧ (ball D V v 3).card=18 := by
  classical
  let A (u : ℕ) := (ball D V u 1).erase u
  let L := V.filter (fun u => mixedScore D V u=30)
  let K := L.image A
  let roots (B : Finset ℕ) := L.filter (fun u => A u=B)
  have rsub : ∀ B∈K, roots B⊆V := fun _ _ _ h => (mem_filter.mp (mem_filter.mp h).1).1
  have rnon : ∀ B∈K, (roots B).Nonempty := by
    intro B hB
    obtain ⟨u,ul,ub⟩ := mem_image.mp hB
    exact ⟨u,mem_filter.mpr ⟨ul,ub⟩⟩
  have partition : L=K.biUnion roots := by
    ext u
    constructor
    · intro hu
      exact mem_biUnion.mpr ⟨A u,mem_image_of_mem _ hu,mem_filter.mpr ⟨hu,rfl⟩⟩
    · intro hu
      obtain ⟨_,_,h⟩ := mem_biUnion.mp hu
      exact (mem_filter.mp h).1
  have dis : (↑K : Set (Finset ℕ)).PairwiseDisjoint roots := by
    intro a ha b hb ne
    exact disjoint_left.mpr (fun _ ha' hb' =>
      ne ((mem_filter.mp ha').2.symm.trans (mem_filter.mp hb').2))
  have lb (u) (uv : u∈V) : 30≤mixedScore D V u := by
    obtain ⟨a,b⟩ := cutoff_five_floor hf ho uv
    change 30≤(ball D V u 2).card+(ball D V u 3).card
    omega
  have shortB (u) (uv : u∈V) (sh : u∈L) : (sixPrefix hf ho uv).B.card=5 := by
    have sc := (mem_filter.mp sh).2
    change (ball D V u 2).card+(ball D V u 3).card=30 at sc
    obtain ⟨a,b⟩ := cutoff_five_floor hf ho uv
    have k := (sixPrefix hf ho uv).two
    omega
  have info (B) (hB : B∈K) : B⊆V ∧ B.card=6 ∧ ∀ v∈B, 32≤mixedScore D V v := by
    obtain ⟨u,ul,ub⟩ := mem_image.mp hB
    have uv := (mem_filter.mp ul).1
    let P := sixPrefix hf ho uv
    have eq : P.A=B := P.a_eq.trans ub
    have gain := five_spill_bank_gain hf ho uv P (shortB u uv ul)
    refine ⟨eq ▸ P.aV,eq ▸ P.ca,?_⟩
    intro v vb
    have va : v∈P.A := eq.symm ▸ vb
    have z := gain v va
    have t := (cutoff_five_floor hf ho (P.aV va)).2
    change 32≤(ball D V v 2).card+(ball D V v 3).card
    omega
  have bd : (↑K : Set (Finset ℕ)).PairwiseDisjoint (fun b => b) := by
    intro B bK C cK ne
    obtain ⟨u,ul,ub⟩ := mem_image.mp bK
    obtain ⟨v,vl,vc⟩ := mem_image.mp cK
    have uv := (mem_filter.mp ul).1
    have vv := (mem_filter.mp vl).1
    let P := sixPrefix hf ho uv
    let Q := sixPrefix hf ho vv
    have pe : P.A=B := P.a_eq.trans ub
    have qe : Q.A=C := Q.a_eq.trans vc
    have s := first_banks_equal_or_disjoint hf ho P Q (shortB u uv ul) (shortB v vv vl)
    rw [pe,qe] at s
    exact s.resolve_right ne
  have miss : ∀ B∈K, ∀ u∈roots B, (roots B).erase u⊆missingMixed D V u := by
    intro B hB u ur v vr
    obtain ⟨ne,vr⟩ := mem_erase.mp vr
    have uv := rsub B hB ur
    have vv := rsub B hB vr
    have eq : A u=A v := (mem_filter.mp ur).2.trans (mem_filter.mp vr).2.symm
    have oeq : outN D V u=outN D V v := by
      change (ball D V u 1).erase u = (ball D V v 1).erase v at eq
      rwa [erase_ball_one_eq_outN hf (by decide : 1≤5) uv,
        erase_ball_one_eq_outN hf (by decide : 1≤5) vv] at eq
    refine mem_sdiff.mpr ⟨vv,?_⟩
    intro x
    rcases mem_union.mp x with a|b
    · exact same_heads_no_reach hf (Ne.symm ne) (by decide : 2≤5) oeq a
    · exact same_heads_no_reach hf ne (by decide : 3≤5) oeq.symm (mem_filter.mp b).2
  have pay (v) (vv : v∈V) :
      31+(K.filter (fun B => v∈B)).card≤mixedScore D V v+(if v∈L then 1 else 0) := by
    let U := K.filter (fun B => v∈B)
    change 31+U.card≤mixedScore D V v+(if v∈L then 1 else 0)
    by_cases zi : U.Nonempty
    · obtain ⟨B,hB⟩ := zi
      have bk := (mem_filter.mp hB).1
      have bv := (mem_filter.mp hB).2
      have c1 : U.card≤1 := card_le_one.mpr (by
        intro C hc W hw
        obtain ⟨ck,cv⟩ := mem_filter.mp hc
        obtain ⟨wk,wv⟩ := mem_filter.mp hw
        by_contra n
        exact (disjoint_left.mp (bd ck wk n)) cv wv)
      have good := (info B bk).2.2 v bv
      omega
    · have ue : U.card=0 := card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp zi)
      have a := lb v vv
      by_cases vl : v∈L
      · simp only [ite_eq_left vl]
        omega
      · simp only [ite_eq_right vl]
        have n : mixedScore D V v≠30 := fun e => vl (mem_filter.mpr ⟨vv,e⟩)
        omega
  have k0 := no_short_banks_of_six_certificate hf hn L roots (fun b => b) partition rsub rnon dis
    (fun B h => (info B h).1) (fun B h => (info B h).2.1) miss pay
  have no : L=∅ := by rw [partition,k0]; simp
  have all (v) (vv : v∈V) : 31≤mixedScore D V v := by
    have low := lb v vv
    by_contra! lt
    have h : v∈L := mem_filter.mpr ⟨vv,by omega⟩
    simp [no] at h
  have budget := mixedScore_with_missing hf
  rw [hn] at budget
  have cnt : (∑ v∈V,mixedScore D V v)=(∑ _v∈V,(31:ℕ)) := by
    have a := sum_le_sum all
    have eq : (∑ _v∈V,(31:ℕ))=30*31 := by simp [hn]
    omega
  intro v vv
  have score := ((sum_eq_sum_iff_of_le all).mp cnt.symm v vv).symm
  change (ball D V v 2).card+(ball D V v 3).card=31 at score
  obtain ⟨a,b⟩ := cutoff_five_floor hf ho vv
  by_cases v12 : (ball D V v 2).card=12
  · let P := sixPrefix hf ho vv
    have p := P.two
    have g := five_spill_bank_gain hf ho vv P (by omega)
    obtain ⟨x,hx⟩ := card_pos.mp (show 0<P.A.card by rw [P.ca]; decide)
    have m := g x hx
    have e := ((sum_eq_sum_iff_of_le all).mp cnt.symm x (P.aV hx)).symm
    change (ball D V x 2).card+(ball D V x 3).card=31 at e
    have f := (cutoff_five_floor hf ho (P.aV hx)).2
    omega
  · omega
  

#print axioms six_order30_uniform

end LeanCH.BR.DotDegreeSix


