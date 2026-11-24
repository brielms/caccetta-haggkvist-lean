import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ6EndpointConstructors_20261121
import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ6Order42Budget_20261121
import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ4SameBank_20261121

namespace LeanCH.BR.DotDegreeSevenQ6
open Finset BRq2 BRq3 BR45 BRsGen DotDegreeSevenLow

private theorem same_spill {D : CH.Digraph} {V B T U : Finset ℕ}
    (h : SevenSpill D V B T) (g : SevenSpill D V B U) : T=U := by
  obtain ⟨b,hb⟩ := card_pos.mp (show 0<B.card by rw [h.seven]; decide)
  apply Subset.antisymm
  · intro t ht
    have k := mem_union.mp (g.keep b hb (mem_outN.mpr ⟨h.subT ht,h.full b hb t ht⟩))
    exact k.resolve_left (fun e => disjoint_left.mp h.apart e ht)
  · intro t ht
    have k := mem_union.mp (h.keep b hb (mem_outN.mpr ⟨g.subT ht,g.full b hb t ht⟩))
    exact k.resolve_left (fun e => disjoint_left.mp g.apart e ht)

private theorem twin_no_three {D : CH.Digraph} {V : Finset ℕ} {u v : ℕ}
    (hf : QFree D V 6) (ne : u≠v) (eq : outN D V u=outN D V v) :
    v∉ball D V u 3 := by
  intro m
  obtain ⟨_,j,hj,w⟩ := mem_ball.mp m
  cases j with
  | zero => cases w; exact ne rfl
  | succ k =>
    cases w with
    | step xV e tail =>
      have xN : _∈outN D V u := mem_outN.mpr ⟨xV,e⟩
      rw [eq] at xN
      exact hf v (k+1) (by omega) (by omega) (.step xV (mem_outN.mp xN).2 tail)

/-- Native bank×type partition and exact excess budget. Only the local
absence of the second-to-first return remains to be supplied here. -/
theorem order42_of_first_layer_no_return {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V 6) (ho : OutEq 7 D V) (hn : V.card≤42) (ne : V.Nonempty)
    (noReturn : ∀ u∈V, (ball D V u 2).card=15 → (ball D V u 3).card=21 →
      ∀ b∈SecondBank D V u, ∀ a∈(ball D V u 1).erase u, D b a≠true) : False := by
  classical
  let L := V.filter (fun u => (ball D V u 3).card=21)
  let kind (u : ℕ) : Bool := decide ((ball D V u 2).card=14)
  let A (u : ℕ) := (ball D V u 1).erase u
  let B (u : ℕ) := SecondBank D V u
  let T (u : ℕ) := ThirdLayer D V u
  let bank (u : ℕ) := if kind u then A u else B u
  let spill (u : ℕ) := if kind u then B u else T u
  let key (u : ℕ) := (bank u,kind u)
  let K := L.image bank
  let J := L.image key
  let roots (i : Finset ℕ × Bool) := L.filter (fun u => key u=i)
  let H := K.biUnion id
  have lv (u) (hu : u∈L) : u∈V := (mem_filter.mp hu).1
  have lt (u) (hu : u∈L) : (ball D V u 3).card=21 := (mem_filter.mp hu).2
  have sf (u) (hu : u∈L) : SevenSpill D V (bank u) (spill u) := by
    by_cases h : (ball D V u 2).card=14
    · simpa only [bank,spill,kind,decide_eq_true_eq,h,if_true,A,B] using
        first_spill_of_ball_two14 hf ho (lv u hu) h
    · have lo := floor_two14 (by decide) hf (fun v hv => (ho v hv).ge) (lv u hu)
      have up := tight_three_cap_two hf ho (lv u hu) (lt u hu)
      have eq : (ball D V u 2).card=15 := by omega
      simpa only [bank,spill,kind,decide_eq_true_eq,h,if_false,B,T,SecondBank,ThirdLayer] using
        second_spill_of_no_return hf ho (lv u hu) eq (lt u hu) (noReturn u (lv u hu) eq (lt u hu))
  have tall (b) (hb : b∈H) : b∈V.filter (fun v => 21<(ball D V v 3).card) := by
    obtain ⟨C,cK,bc⟩ := mem_biUnion.mp hb
    obtain ⟨u,ul,rfl⟩ := mem_image.mp cK
    have h := sf u ul
    exact mem_filter.mpr ⟨h.subB bc,(sevenSpill_tall hf ho h b bc).2⟩
  have bdis : (↑K : Set (Finset ℕ)).PairwiseDisjoint id := by
    intro C hc E he neq
    obtain ⟨u,ul,rfl⟩ := mem_image.mp hc
    obtain ⟨v,vl,rfl⟩ := mem_image.mp he
    have H := sf u ul
    have G := sf v vl
    exact (completeSpill_banks_disjoint_or_equal hf (by decide) H.subB G.subB
       H.seven G.seven H.one G.one H.keep G.keep H.full G.full).resolve_right neq
  have hc : H.card=7*K.card := by
    rw [show H=K.biUnion id from rfl,card_biUnion bdis]
    calc
      _ = ∑ _b∈K, (7 : ℕ) := by
        apply sum_congr rfl
        intro C hc
        obtain ⟨u,ul,rfl⟩ := mem_image.mp hc
        exact (sf u ul).seven
      _ = _ := by rw [Finset.sum_const_nat (fun _ _ => rfl),Nat.mul_comm]
  have jc : J.card≤2*K.card := by
    have sub : J⊆K.product (univ : Finset Bool) := by
      intro i hi
      obtain ⟨v,vl,rfl⟩ := mem_image.mp hi
      exact mem_product.mpr ⟨mem_image.mpr ⟨v,vl,rfl⟩,mem_univ _⟩
    have n := card_le_card sub
    simpa [card_product,Nat.mul_comm] using n
  have partition : L=J.biUnion roots := by
    ext u
    constructor
    · intro hu
      exact mem_biUnion.mpr ⟨key u,mem_image.mpr ⟨u,hu,rfl⟩,mem_filter.mpr ⟨hu,rfl⟩⟩
    · intro hu
      obtain ⟨_,_,q⟩ := mem_biUnion.mp hu
      exact (mem_filter.mp q).1
  have dis : (↑J : Set (Finset ℕ × Bool)).PairwiseDisjoint roots := by
    intro i hi j hj ne
    exact disjoint_left.mpr (fun x xi xj => ne
      (((mem_filter.mp xi).2).symm.trans (mem_filter.mp xj).2))
  have noReach (u v) (ul : u∈L) (vl : v∈L) (neq : u≠v) (e : key u=key v) :
      v∉ball D V u 3 := by
    have bb : bank u=bank v := congrArg Prod.fst e
    have kk : kind u=kind v := congrArg Prod.snd e
    by_cases h : (ball D V u 2).card=14
    · have hv : (ball D V v 2).card=14 := by simpa [kind,h] using kk.symm
      have eq : outN D V u=outN D V v := by
        rw [←erase_ball_one_eq_outN hf (by decide : 1≤6) (lv u ul),
          ←erase_ball_one_eq_outN hf (by decide : 1≤6) (lv v vl)]
        simpa [bank,kind,h,hv,A] using bb
      exact twin_no_three hf neq eq
    · have hv : (ball D V v 2).card≠14 := by simpa [kind,h] using kk.symm
      have eq : B u=B v := by simpa [bank,kind,h,hv] using bb
      have hU : SevenSpill D V (B u) (T u) := by simpa [bank,spill,kind,h] using sf u ul
      have hV : SevenSpill D V (B u) (T v) := by
        rw [eq]
        simpa [bank,spill,kind,hv] using sf v vl
      have te := same_spill hU hV
      have n2 := same_bank_no_two_q4 (hf.mono_bound (by decide : 4≤6)) ho
        (lv u ul) (lv v vl) neq eq
      intro z
      have m : v∈T u := mem_sdiff.mpr ⟨z,n2⟩
      rw [te] at m
      exact (mem_sdiff.mp m).2 (self_mem_ball (lv v vl))
  have miss (i) (_ : i∈J) (v) (hv : v∈roots i) :
      (roots i).erase v⊆V \ (ball D V v 3 ∪ reverseBall D V v 3) := by
    intro w hw
    obtain ⟨wn,wr⟩ := mem_erase.mp hw
    obtain ⟨vl,vi⟩ := mem_filter.mp hv
    obtain ⟨wl,wi⟩ := mem_filter.mp wr
    have ek := vi.trans wi.symm
    refine mem_sdiff.mpr ⟨lv w wl,?_⟩
    intro m
    rcases mem_union.mp m with m|m
    · exact noReach v w vl wl wn.symm ek m
    · exact noReach w v wl vl wn ek.symm (mem_filter.mp m).2
  exact order42_bank_budget hf ho ne hn J roots H K.card jc hc partition
    (fun i hi v hv => lv v (mem_filter.mp hv).1) dis tall miss

#print axioms order42_of_first_layer_no_return
end LeanCH.BR.DotDegreeSevenQ6
