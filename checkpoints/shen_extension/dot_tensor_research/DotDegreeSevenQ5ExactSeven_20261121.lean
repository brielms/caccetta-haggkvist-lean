import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ5ExactReturnBank_20261121
import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ5ExactLayers_20261121

namespace LeanCH.BR.DotDegreeSevenLow
open Finset BRq2 BRq3 BR45 BRsGen

/-- A mixed endpoint cannot contain two labels separated by an
internal three-step walk but unable to use the complementary reach. -/
theorem exact_mixed_forbids_asymmetric_three {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V 5) (ho : OutEq 7 D V) (n : V.card=35)
    (noLow : ∀ v∈V, 15≤(ball D V v 2).card) {x y : ℕ}
    (xV : x∈V) (yV : y∈V) (not2 : y∉ball D V x 2)
    (not3back : x∉ball D V y 3) : False := by
  apply not3back
  have h : y∈reverseBall D V x 3 := by
    rw [(saturated_mixed_endpoint hf ho n noLow x xV).1]
    exact mem_union_left _ (mem_sdiff.mpr ⟨yV,not2⟩)
  exact (mem_filter.mp h).2

theorem exact_short_walk_stays {D : CH.Digraph} {V A B : Finset ℕ}
    (keep : ∀ a∈A, outN D V a⊆A∪B)
    (noret : ∀ b∈B, ∀ a∈A, ∀ j≤2, ¬ Walk D V b a j)
    {x y k : ℕ} (hx : x∈A) (hy : y∈A) (hk : k≤3)
    (w : Walk D V x y k) : Walk D A x y k := by
  induction w with
  | refl x => exact .refl x
  | @step a b c j bv e tail ih =>
    rcases mem_union.mp (keep a hx (mem_outN.mpr ⟨bv,e⟩)) with h|h
    · exact .step h e (ih h hy (by omega))
    · exact (noret b h c hy j (by omega) tail).elim

/-- A degree-one host cannot reach more than three labels in two steps. -/
theorem exact_one_two_ball_cap {D : CH.Digraph} {A : Finset ℕ} {x : ℕ}
    (one : OutEq 1 D A) (hx : x∈A) : (ball D A x 2).card≤3 := by
  obtain ⟨a,ha⟩ := card_eq_one.mp (one x hx)
  have aN : a∈outN D A x := by rw [ha]; simp
  obtain ⟨b,hb⟩ := card_eq_one.mp (one a (mem_outN.mp aN).1)
  have H : ball D A x 2⊆{x,a,b} := by
    intro y hy
    obtain ⟨_,k,hk,w⟩ := mem_ball.mp hy
    cases k with
    | zero => cases w; simp
    | succ k =>
      cases w with
      | @step _ c _ _ cv e w =>
        have hc : c∈outN D A x := mem_outN.mpr ⟨cv,e⟩
        rw [ha,mem_singleton] at hc
        subst c
        cases k with
        | zero => cases w; simp
        | succ k =>
          cases w with
          | @step _ c _ _ cv' e' w =>
            have eq : k=0 := by omega
            subst k
            have hc : c∈outN D A a := mem_outN.mpr ⟨cv',e'⟩
            rw [hb,mem_singleton] at hc
            subst c
            cases w
            simp
  have hc := card_le_card H
  have hp := card_insert_le x ({a,b} : Finset ℕ)
  have ht := card_insert_le a ({b} : Finset ℕ)
  rw [card_singleton] at ht
  omega

/-- Contradiction for a retained seven-cycle provided its mixed reach
tensor does not admit any external short return. -/
theorem exact_mixed_forbids_retained_seven_cycle {D : CH.Digraph} {V A B : Finset ℕ}
    (hf : QFree D V 5) (ho : OutEq 7 D V) (n : V.card=35)
    (noLow : ∀ v∈V, 15≤(ball D V v 2).card)
    (aV : A⊆V) (aNe : A.Nonempty) (h6 : QFree D A 6) (one : OutEq 1 D A)
    (keep : ∀ a∈A, outN D V a⊆A∪B)
    (noret : ∀ b∈B, ∀ a∈A, ∀ j≤2, ¬ Walk D V b a j) : False := by
  classical
  obtain ⟨x,hx⟩ := aNe
  have lo := ball_one_growth h6 (fun x hx => (one x hx).ge) hx 3 (by decide)
  have up := exact_one_two_ball_cap one hx
  have ne : (ball D A x 3 \ ball D A x 2).Nonempty := by
    apply card_pos.mp
    rw [card_sdiff_of_subset (ball_mono_radius (by decide : 2≤3))]
    omega
  obtain ⟨y,hy⟩ := ne
  obtain ⟨ya,k,hk,w⟩ := mem_ball.mp (mem_sdiff.mp hy).1
  have hkk : k=3 := by
    by_contra h
    exact (mem_sdiff.mp hy).2 (mem_ball.mpr ⟨ya,k,by omega,w⟩)
  apply exact_mixed_forbids_asymmetric_three hf ho n noLow (aV hx) (aV ya)
  · intro h
    obtain ⟨_,j,hj,wj⟩ := mem_ball.mp h
    exact (mem_sdiff.mp hy).2 (mem_ball.mpr ⟨ya,j,hj,
      exact_short_walk_stays keep noret hx ya (by omega) wj⟩)
  · intro h
    obtain ⟨_,j,hj,wj⟩ := mem_ball.mp h
    exact h6 x (k+j) (by omega) (by omega)
      (w.append (exact_short_walk_stays keep noret ya hx hj wj))

/-- The chordless length-seven possibility for an exact endpoint first
layer is impossible. -/
theorem exact_endpoint_no_seven_layer {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (hf : QFree D V 5) (ho : OutEq 7 D V) (n : V.card=35)
    (noLow : ∀ v∈V, 15≤(ball D V v 2).card) (hu : u∈V)
    (h6 : QFree D (EndpointLayer1 D V u) 6)
    (one : OutEq 1 D (EndpointLayer1 D V u)) : False := by
  let A := EndpointLayer1 D V u
  let B := EndpointLayer2 D V u
  let T := EndpointLayer3 D V u
  have aV : A⊆V := outN_subset
  have bV : B⊆V := sdiff_subset.trans ball_subset
  have tV : T⊆V := sdiff_subset.trans ball_subset
  have ab : Disjoint A B := disjoint_left.mpr (by
    intro x ax bx
    exact (mem_sdiff.mp bx).2 ((mem_ball_one hu).mpr (Or.inr ax)))
  have bt : Disjoint B T := disjoint_left.mpr (by
    intro x bx tx
    exact (mem_sdiff.mp tx).2 (mem_sdiff.mp bx).1)
  have c := exact_endpoint_cards hf ho n noLow
  obtain ⟨ca,cb,ct⟩ := exact_endpoint_layer_cards hf ho hu (c u hu)
  obtain ⟨ka,kb⟩ := exact_endpoint_layer_out hf hu
  have aNe : A.Nonempty := card_pos.mp (by change 0<A.card; rw [show A.card=7 from ca]; decide)
  have cap (v) (hv : v∈V) := (c v hv).1.le
  have miss (x) (ax : x∈A) : (B \ outN D V x).card≤1 := by
    have em : outN D V x=outN D (A∪B) x := by
      ext y
      simp only [mem_outN]
      exact ⟨fun h => ⟨ka x ax (mem_outN.mpr h),h.2⟩,
        fun h => ⟨union_subset aV bV h.1,h.2⟩⟩
    have sum : 7=1+(outN D B x).card := by
      rw [← one x ax,← card_outN_union ab,←em,ho x (aV ax)]
    have e : B \ outN D V x = B \ outN D B x := by
      ext y
      simp only [mem_sdiff,mem_outN]
      exact ⟨fun h => ⟨h.1, fun h' => h.2 ⟨bV h'.1,h'.2⟩⟩,
        fun h => ⟨h.1,fun h' => h.2 ⟨h.1,h'.2⟩⟩⟩
    rw [e,card_sdiff_of_subset outN_subset]
    change B.card - (outN D B x).card ≤ 1
    change B.card=7 at cb
    omega
  have succA (x) (ax : x∈A) : ∃ y∈A, D x y=true := by
    obtain ⟨y,hy⟩ := card_pos.mp (show 0<(outN D A x).card by rw [one x ax]; decide)
    exact ⟨y,(mem_outN.mp hy).1,(mem_outN.mp hy).2⟩
  have nr (b) (bb : b∈B) (a) (aa : a∈A) (j) (hj : j≤2) :
      ¬ Walk D V b a j := by
    intro w
    by_cases jp : 0<j
    · apply exact_no_cycle_bank_returns hf ho n.le cap aV bV tV bt (by simpa [A] using ca.le)
        cb ct.le miss succA ?_ b bb a aa j jp hj w
      intro x xx y yy
      have h := kb x xx yy
      simpa only [union_assoc] using h
    · have jz : j=0 := by omega
      subst j
      cases w
      exact disjoint_left.mp ab aa bb
  exact exact_mixed_forbids_retained_seven_cycle hf ho n noLow aV aNe h6 one ka nr
#print axioms exact_mixed_forbids_asymmetric_three
#print axioms exact_short_walk_stays
#print axioms exact_one_two_ball_cap
#print axioms exact_mixed_forbids_retained_seven_cycle
#print axioms exact_endpoint_no_seven_layer

end LeanCH.BR.DotDegreeSevenLow


