import LeanCH.BR.BRWeightedOutUniformSaturation

/-! Global fixed-label arc minimum, followed by maximum own rational level.
No source subgraph restriction or real game-value object is used. -/
namespace LeanCH.BR.WeightedSD
open Finset BRq2 BRq3 BR45 BRsub Matrix FiniteCutInverse

def arcMaskGraph (S : Finset (ℕ × ℕ)) : CH.Digraph := fun x y => decide ((x,y)∈S)

theorem arcSet_mask {V : Finset ℕ} {S : Finset (ℕ × ℕ)} (hS : S⊆V×ˢV) :
    arcSet (arcMaskGraph S) V=S := by
  ext e
  simp only [arcSet,mem_filter,mem_product,arcMaskGraph,decide_eq_true_eq]
  exact ⟨fun h => h.2,fun h => ⟨mem_product.mp (hS h),h⟩⟩

theorem arcMask_sub (D : CH.Digraph) (V : Finset ℕ) (x y : ℕ)
    (h : arcMaskGraph (arcSet D V) x y=true) : D x y=true := by
  have hh : (x,y)∈arcSet D V := of_decide_eq_true h
  exact (mem_filter.mp hh).2

theorem row_arcMask (q : ℕ) (D : CH.Digraph) (V : Finset ℕ) (a : ℕ→ℚ)
    {x : ℕ} (hx : x∈V) : row q (arcMaskGraph (arcSet D V)) V a x=row q D V a x := by
  unfold row outW
  congr 2
  apply sum_congr rfl
  intro y hy
  simp [arcMaskGraph,arcSet,hx,hy]

theorem not_smallRow_arcMask {q : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hbad : ¬ SmallRow q D V) : ¬ SmallRow q (arcMaskGraph (arcSet D V)) V := by
  intro hs
  apply hbad
  intro a ha hV
  obtain ⟨x,hx,hr⟩ := hs a ha hV
  exact ⟨x,hx,by rwa [row_arcMask q D V a hx] at hr⟩

/-- Normalized equalizer levels agree, even for signed rational laws. -/
theorem equalizer_level_eq {q : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (a p : ℕ→ℚ) (ha : mass V a=1) (hp : mass V p=1) (c d : ℚ)
    (hr : ∀ x∈V,row q D V a x=c) (hc : ∀ x∈V,col q D V p x=d) : c=d := by
  have hh := mixed_equalizer_gain (R := realMatrix q D V) (S := realMatrix q D V)
    (fun i : V => (a i : ℝ)) (fun i : V => (p i : ℝ))
    (real_mass_of_rational_probability a ha) (real_mass_of_rational_probability p hp)
    (c : ℝ) (d : ℝ) (realMatrix_rational_rows a c hr) (realMatrix_rational_columns p d hc)
  simp only [sub_self,mul_zero,zero_mul,sum_const_zero] at hh
  exact_mod_cast (show (c : ℝ)=(d : ℝ) by linarith)

/-- The comparison class is ALL q-free non-SmallRow graphs on V.
The second comparison accepts any normalized row equalizer of a competitor. -/
structure NativeExtremal (q : ℕ) (D : CH.Digraph) (V : Finset ℕ) (c : ℚ) : Prop where
  free : QFree D V q
  bad : ¬ SmallRow q D V
  arc_min : ∀ E : CH.Digraph, QFree E V q → ¬ SmallRow q E V →
    (arcSet D V).card≤(arcSet E V).card
  level_max : ∀ E : CH.Digraph, QFree E V q → ¬ SmallRow q E V →
    (arcSet E V).card=(arcSet D V).card → ∀ (a : ℕ→ℚ) (d : ℚ),
    mass V a=1 → (∀ x∈V,row q E V a x=d) → d≤c

theorem NativeExtremal.critical {q : ℕ} {D : CH.Digraph} {V : Finset ℕ} {c : ℚ}
    (h : NativeExtremal q D V c) : ArcCritical q D V := by
  intro a ha b hb hab
  by_contra hbad
  have hh := h.arc_min (eraseArc D a b) (qfree_sub (eraseArc_sub D a b) h.free) hbad
  have hmem : (a,b)∈arcSet D V := mem_filter.mpr ⟨mem_product.mpr ⟨ha,hb⟩,hab⟩
  rw [arcSet_erase,card_erase_of_mem hmem] at hh
  have hp : 0<(arcSet D V).card := card_pos.mpr
    ⟨(a,b),mem_filter.mpr ⟨mem_product.mpr ⟨ha,hb⟩,hab⟩⟩
  omega

theorem exists_native_extremal {q : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hsmall : SmallerSmallRow q V.card) (hf : QFree D V q) (hbad : ¬ SmallRow q D V) :
    ∃ E : CH.Digraph, ∃ a p : ℕ→ℚ, ∃ c : ℚ,
      NativeExtremal q E V c ∧ ArcCritical q E V ∧ 1<c ∧
      (∀ x∈V,0<a x) ∧ (∀ x∈V,0<p x) ∧ mass V a=1 ∧ mass V p=1 ∧
      (∀ x∈V,row q E V a x=c) ∧ (∀ x∈V,col q E V p x=c) ∧
      ∃ H : Matrix V V ℝ, CommonInverse (realMatrix q E V) H := by
  classical
  let C := (V×ˢV).powerset.filter (fun S => QFree (arcMaskGraph S) V q ∧ ¬ SmallRow q (arcMaskGraph S) V)
  have hmem (F : CH.Digraph) (hF : QFree F V q) (hb : ¬ SmallRow q F V) : arcSet F V∈C := by
    apply mem_filter.mpr
    exact ⟨mem_powerset.mpr (filter_subset _ _),qfree_sub (arcMask_sub F V) hF,not_smallRow_arcMask hb⟩
  have hC : C.Nonempty := ⟨arcSet D V,hmem D hf hbad⟩
  have hpair : ∀ S : {S // S∈C}, ∃ c : ℚ, ∃ a p : ℕ→ℚ,
      1<c ∧ (∀ x∈V,0<a x) ∧ (∀ x∈V,0<p x) ∧ mass V a=1 ∧ mass V p=1 ∧
      (∀ x∈V,row q (arcMaskGraph S.val) V a x=c) ∧
      (∀ x∈V,col q (arcMaskGraph S.val) V p x=c) := by
    intro S
    have hh := (mem_filter.mp S.property).2
    obtain ⟨z,hz,hV,hzr⟩ := strict_witness_of_not_smallRow hh.2
    obtain ⟨a,p,c,hc,ha,hp,hm,hpm,hr,hpc⟩ :=
      strict_pair_of_proper_smallRow (hsmall.induced hh.1) hV z hz hzr
    exact ⟨c,a,p,hc,ha,hp,hm,hpm,hr,hpc⟩
  choose level hlevel using hpair
  obtain ⟨S0,hS0,hmin⟩ := C.exists_min_image Finset.card hC
  let T := C.filter (fun S => S.card=S0.card)
  have hT : T.Nonempty := ⟨S0,mem_filter.mpr ⟨hS0,rfl⟩⟩
  let f := fun S => if hs : S∈C then level ⟨S,hs⟩ else 0
  obtain ⟨S,hST,hmax⟩ := T.exists_max_image f hT
  have hSC := (mem_filter.mp hST).1
  have hScard := (mem_filter.mp hST).2
  have hSsub : S⊆V×ˢV := mem_powerset.mp (mem_filter.mp hSC).1
  have hSF := (mem_filter.mp hSC).2
  obtain ⟨a,p,hc,ha,hp,hm,hpm,hr,hpc⟩ := hlevel ⟨S,hSC⟩
  have hE : NativeExtremal q (arcMaskGraph S) V (level ⟨S,hSC⟩) := by
    refine ⟨hSF.1,hSF.2,?_,?_⟩
    · intro F hF hb
      rw [arcSet_mask hSsub,hScard]
      exact hmin _ (hmem F hF hb)
    · intro F hF hb hcount b d hbm hbr
      have hFC := hmem F hF hb
      have hFT : arcSet F V∈T := mem_filter.mpr ⟨hFC,by
        rw [arcSet_mask hSsub] at hcount
        exact hcount.trans hScard⟩
      obtain ⟨b',p',_,_,_,_,hpm',_,hpc'⟩ := hlevel ⟨arcSet F V,hFC⟩
      have hd := equalizer_level_eq b p' hbm hpm' d (level ⟨arcSet F V,hFC⟩)
        (fun x hx => by rw [row_arcMask q F V b hx]; exact hbr x hx) hpc'
      rw [hd]
      simpa [f,hFC,hSC] using hmax _ hFT
  obtain ⟨z,hz,hV,hzr⟩ := strict_witness_of_not_smallRow hSF.2
  obtain ⟨H,hH⟩ := strict_inverse_of_proper_smallRow (hsmall.induced hSF.1) z hz hzr
  exact ⟨arcMaskGraph S,a,p,level ⟨S,hSC⟩,hE,hE.critical,hc,ha,hp,hm,hpm,hr,hpc,H,hH⟩

end LeanCH.BR.WeightedSD
