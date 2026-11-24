import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ7GrowthProof_20261121
import LeanCH.BR.BRCycleReturn
import LeanCH.BR.BRShortestCycle

namespace LeanCH.BR.DotDegreeSevenQ7GrowthProof
open Finset BRq2 BRq3 BR45 BRsGen BRsub

/-- Local dense prefix calculation: the only way a minout-one 7-free
set of at most 11 labels can reach this density is to contain a bank of
eight rows of degree one in that same prefix. -/
def DenseSmallPrefix : Prop :=
  ∀ (D : CH.Digraph) (K : Finset ℕ), QFree D K 7 → K.Nonempty → K.card ≤ 11 →
    (∀ v∈K, 1 ≤ (outN D K v).card) →
    6*K.card ≤ (∑ v ∈ K,(outN D K v).card)+35 →
    ∃ C⊆K, C.card=8 ∧ ∀ v∈C,(outN D K v).card≤1

theorem noSingleton_of_densePrefix (geom : DenseSmallPrefix) : NoSingletonFragment := by
  intro D H hf hm hdef u hu k kl ku cap one
  classical
  let K := (ball D H u k).erase u
  let g := fun v => 7-(outN D H v).card
  have sub : K⊆H := (erase_subset _ _).trans ball_subset
  have nk : K.Nonempty := by
    have c := card_le_card (s:=outN D H u) (t:=K) (by
      rw [←erase_ball_one_eq_outN hf (by decide) hu]
      exact fun v hv => mem_erase.mpr ⟨(mem_erase.mp hv).1,
        ball_mono_radius (by omega : 1≤k) (mem_of_mem_erase hv)⟩)
    exact card_pos.mp (by have := (hm u hu).1; omega)
  have kcap : K.card≤11 := by
    dsimp only [K]
    rw [card_erase_of_mem (self_mem_ball (D:=D) (k:=k) hu)]
    omega
  have minK := minOut_prefix_erase (d:=1) hf hu (by omega : k+1≤7)
    (fun v hv => (hm v hv).1) (by omega)
  have loss (v) (hv : v∈K) : (outN D H v).card ≤ (outN D K v).card+1 := by
    have hn := card_le_card (outN_prefix_loss hf hu (by omega : k+1≤7) hv)
    change (outN D H v).card ≤ (outN D K v ∪ (ball D H u (k+1) \ ball D H u k)).card at hn
    have hcap := card_union_le (outN D K v) (ball D H u (k+1) \ ball D H u k)
    omega
  have gcap : (∑ v∈K,g v)≤35 := by exact (sum_le_sum_of_subset sub).trans hdef
  have sumK := sum_le_sum (s:=K) (fun v hv => show 6 ≤ (outN D K v).card+g v by
    have h := loss v hv
    dsimp only [g]
    omega)
  rw [sum_add_distrib, Finset.sum_const_nat (fun _ _ => rfl)] at sumK
  obtain ⟨C,hCK,hC,hd⟩ := geom D K (hf.mono_set sub) nk kcap minK (by
    rw [Nat.mul_comm]
    omega)
  have hCdef := sum_le_sum (s:=C) (fun v hv => show 5≤g v by
    have l := loss v (hCK hv)
    have h := hd v hv
    dsimp only [g]
    omega)
  rw [Finset.sum_const_nat (fun _ _ => rfl),hC] at hCdef
  have gc := (sum_le_sum_of_subset (hCK.trans sub) (f:=g)).trans hdef
  omega

/-- Each exterior vertex can contact a bank at most once per label.
For an interior vertex the same count loses its own label. -/
theorem contactCap {D : CH.Digraph} {K A : Finset ℕ} {v : ℕ}
    (hf : QFree D K 7) (asub : A⊆K) (hv : v∈K) :
    (inN D A v).card+(outN D A v).card≤A.card := by
  have dis : Disjoint (inN D A v) (outN D A v) :=
    disjoint_left.mpr fun x hx hy => digonfree hf (by decide) hv (asub (outN_subset hy))
      (mem_outN.mp hy).2 (mem_inN.mp hx).2
  have h := card_le_card (s:=inN D A v ∪ outN D A v) (t:=A)
    (union_subset (fun _ h => (mem_inN.mp h).1) outN_subset)
  rwa [card_union_of_disjoint dis] at h

theorem ownContactCap {D : CH.Digraph} {K A : Finset ℕ} {v : ℕ}
    (hf : QFree D K 7) (asub : A⊆K) (hv : v∈A) :
    (inN D A v).card+(outN D A v).card≤A.card-1 := by
  have dis : Disjoint (inN D A v) (outN D A v) :=
    disjoint_left.mpr fun x hx hy => digonfree hf (by decide) (asub hv)
      (asub (outN_subset hy)) (mem_outN.mp hy).2 (mem_inN.mp hx).2
  have h := card_le_card (s:=inN D A v ∪ outN D A v) (t:=A.erase v) (by
    intro x hx
    rcases mem_union.mp hx with hi | ho
    · obtain ⟨hx,h⟩ := mem_inN.mp hi
      exact mem_erase.mpr ⟨fun he => loopfree hf (by decide) (asub hv) (he ▸ h),hx⟩
    · obtain ⟨hx,h⟩ := mem_outN.mp ho
      exact mem_erase.mpr ⟨fun he => loopfree hf (by decide) (asub hv) (he ▸ h),hx⟩)
  rwa [card_union_of_disjoint dis,card_erase_of_mem hv] at h

theorem internalArcCap {D : CH.Digraph} {K A : Finset ℕ} (hf : QFree D K 7)
    (sub : A⊆K) : 2*(∑ v ∈ A,(outN D A v).card)≤A.card*(A.card-1) := by
  have h := sum_le_sum (s:=A) (fun v hv => ownContactCap hf sub hv)
  have same : (∑ v∈A,(outN D A v).card)=(∑ v∈A,(inN D A v).card) :=
    Compose.ThinRigid.sum_out_eq_sum_in D A
  rw [sum_add_distrib, ←same, Finset.sum_const_nat (fun _ _ => rfl)] at h
  rw [Nat.mul_comm]
  omega

#print axioms noSingleton_of_densePrefix
#print axioms internalArcCap
/-- Count arcs of the actual induced host by cycle arcs, exterior arcs,
and the two distinct attachment columns at every exterior label. -/
theorem cycleArcLedger {D : CH.Digraph} {K C : Finset ℕ}
    (sub : C⊆K) (reg : OutEq 1 D C) :
    (∑ v∈K,(outN D K v).card)=C.card+
      (∑ v∈K\C,(outN D (K\C) v).card)+
      ∑ v∈K\C,((inN D C v).card+(outN D C v).card) := by
  classical
  let T := K\C
  have split (v : ℕ) : (outN D K v).card=(outN D C v).card+(outN D T v).card := by
    have g := card_outN_union (D:=D) (show Disjoint C T from disjoint_sdiff) v
    rw [union_sdiff_of_subset sub] at g
    exact g
  have same := dcount C T (fun x y => D x y=true)
  change (∑ v∈C,(outN D T v).card)=(∑ v∈T,(inN D C v).card) at same
  have cyc : (∑ v∈C,(outN D C v).card)=C.card := by rw [sum_congr rfl reg]; simp
  have p := sum_sdiff sub (f:=fun v => (outN D K v).card)
  change (∑ v∈T,(outN D K v).card)+(∑ v∈C,(outN D K v).card)=_ at p
  rw [sum_congr (s₁:=T) rfl (fun v _ => split v),
      sum_congr (s₁:=C) rfl (fun v _ => split v),
      sum_add_distrib,sum_add_distrib,cyc,same] at p
  change _=C.card+(∑ v∈T,(outN D T v).card)+∑ v∈T,((inN D C v).card+(outN D C v).card)
  rw [sum_add_distrib]
  omega

theorem denseSmallPrefix : DenseSmallPrefix := by
  intro D K hf kne kcap hm hsum
  classical
  obtain ⟨p,C,hp,hpf,Csub,Cc,reg⟩ := exists_minimal_cycle_support (by decide) hf hm kne
  let T := K\C
  let a := fun v => (inN D C v).card+(outN D C v).card
  have Tsub : T⊆K := sdiff_subset
  have Tc : T.card+C.card=K.card := card_sdiff_add_card_eq_card Csub
  have ecap := internalArcCap hf Tsub
  have ledger := cycleArcLedger Csub reg
  rw [ledger] at hsum
  change 6*K.card≤C.card+(∑ v∈T,(outN D T v).card)+(∑ v∈T,a v)+35 at hsum
  have acap (v) (hv : v∈T) : a v≤C.card := contactCap hf Csub (Tsub hv)
  have sumcap := sum_le_sum acap
  rw [Finset.sum_const_nat (fun _ _ => rfl)] at sumcap
  change (∑ v∈T,a v)≤T.card*C.card at sumcap
  have small : T.card≤3 := by omega
  have c8 : C.card=8 := by
    by_contra! e
    interval_cases h : T.card <;> simp only [Nat.reduceSub,Nat.reduceMul,Nat.mul_succ,Nat.zero_mul] at * <;> omega
  have initial_contact (x) (hx : x∈T) : 4≤a x := by
    by_contra! l
    have others := sum_le_sum (s:=T.erase x) (fun v hv => acap v (mem_of_mem_erase hv))
    rw [Finset.sum_const_nat (fun _ _ => rfl),card_erase_of_mem hx,c8] at others
    have re := sum_erase_add T a hx
    interval_cases h : T.card <;> simp only [Nat.reduceSub,Nat.reduceMul,Nat.mul_succ,Nat.zero_mul] at * <;> omega
  have not_both (x) (hx : x∈T) :
      (inN D C x).card=0 ∨ (outN D C x).card=0 := by
    by_contra! h
    have c := cycle_two_sided_contact_cap (q:=7) (by decide) hf Csub (by omega) reg (Tsub hx)
      (card_pos.mp (by omega)) (card_pos.mp (by omega))
    have m := initial_contact x hx
    change 4≤(inN D C x).card+(outN D C x).card at m
    omega
  have no_receiver (x) (hx : x∈T) : (inN D C x).card=0 := by
    by_contra h
    let R := T.filter (fun v => (outN D C v).card=0)
    have rsub : R⊆T := filter_subset _ _
    have xR : x∈R := mem_filter.mpr ⟨hx,(not_both x hx).resolve_left h⟩
    obtain ⟨b,hb,bsink⟩ := exists_sink (hf.mono_set (rsub.trans Tsub)) ⟨x,xR⟩
      ((card_le_card rsub).trans (by omega))
    have hbT := rsub hb
    have b0 : (outN D C b).card=0 := (mem_filter.mp hb).2
    obtain ⟨z,hz⟩ := card_pos.mp (show 0<(outN D K b).card by have := hm b (Tsub hbT); omega)
    obtain ⟨hzK,bz⟩ := mem_outN.mp hz
    have hzC : z∉C := fun m => by
      have pos := card_pos.mpr ⟨z,mem_outN.mpr ⟨m,bz⟩⟩
      omega
    have hzT : z∈T := mem_sdiff.mpr ⟨hzK,hzC⟩
    have hzR : z∉R := fun m => bsink z m bz
    have zout : (outN D C z).Nonempty := card_pos.mp (by
      by_contra! hh
      exact hzR (mem_filter.mpr ⟨hzT,by omega⟩))
    have bin : (inN D C b).Nonempty := card_pos.mp (by
      have c := initial_contact b hbT
      change 4≤(inN D C b).card+(outN D C b).card at c
      omega)
    have cbz := cycle_reentry_window (q:=7) (t:=2) (by decide) hf Csub (by omega) reg (Tsub hbT)
      bin outN_subset zout (fun w hw =>
        ball_step (ball_of_adj hzK bz) (Csub (outN_subset hw)) (mem_outN.mp hw).2)
    have z0 : (inN D C z).card=0 :=
      (not_both z hzT).resolve_right (by have := card_pos.mpr zout; omega)
    have both : a b + a z≤4 := by dsimp only [a]; omega
    have ab := initial_contact b hbT
    have az := initial_contact z hzT
    omega
  refine ⟨C,Csub,c8,?_⟩
  intro v hv
  have no : (outN D T v).card=0 := by
    by_contra h
    obtain ⟨z,hz⟩ := card_pos.mp (show 0<(outN D T v).card by omega)
    obtain ⟨hzT,vz⟩ := mem_outN.mp hz
    have pos := card_pos.mpr ⟨v,mem_inN.mpr ⟨hv,vz⟩⟩
    have z := no_receiver z hzT
    omega
  have g := card_outN_union (D:=D) (show Disjoint C T from disjoint_sdiff) v
  rw [union_sdiff_of_subset Csub,reg v hv,no,Nat.add_zero] at g
  omega

theorem noSingletonFragment : NoSingletonFragment := noSingleton_of_densePrefix denseSmallPrefix

#print axioms denseSmallPrefix
#print axioms noSingletonFragment
theorem fragmentBaseline : FragmentBaseline :=
  fragmentBaseline_of_local (localGrowth_of_noSingleton noSingletonFragment)

theorem floor_four {D : CH.Digraph} {V : Finset ℕ} (hf : QFree D V 7)
    (ho : OutEq 7 D V) {u : ℕ} (hu : u∈V) : 28≤(ball D V u 4).card :=
  floor_four_of_baseline fragmentBaseline hf ho hu

theorem order_ge49 {D : CH.Digraph} {V : Finset ℕ} (hf : QFree D V 7)
    (ho : OutEq 7 D V) (hn : V.Nonempty) : 49≤V.card :=
  order_of_baseline fragmentBaseline hf ho hn

theorem exact_pair {D : CH.Digraph} {V : Finset ℕ} (hf : QFree D V 7)
    (ho : OutEq 7 D V) (hn : V.card=49) {u : ℕ} (hu : u∈V) :
    reverseBall D V u 4=(V\ball D V u 3)∪{u} :=
  exact_pair_of_baseline fragmentBaseline hf ho hn hu

#print axioms order_ge49
#print axioms exact_pair
end LeanCH.BR.DotDegreeSevenQ7GrowthProof



