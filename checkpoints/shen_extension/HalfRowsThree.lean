import checkpoints.shen_extension.HalfRowsSink

/-!
# Half the rows are tight at cutoff 3, `d = 3` (eleven vertices)

Lean 4.35.0. Paper: `checkpoints/shen_extension/triangle_20261118/halfcyc_Note.md`, §0, §1.2 (F4), §2
"PROVED for d = 3"; `HalfLaw_20261118.md` §2–§3.

Setting: a `3`-free digraph on `11` vertices with every outdegree at least `3`.

* `one_head` (F4): in a `3`-free digraph, if every vertex of a set `A` of at most four vertices has a head in `A`,
  then every vertex of `A` has at most one head in `A`.
* `local_bound` (local half law at `d = 3`): after trimming every outdegree to `3` or `4`, every vertex `u` has
  `out(u) + in(u) ≤ 7`, i.e. at least three non-neighbours.
* `half_trimmed`, `half_three`: at least half the rows are tight (`11 ≤ 2t`), first for the trimmed graph, then
  for every such digraph (trim via `exists_trim`).
* `tightLaw_three_three`: `TightLaw 3 3` is a theorem.
* `capstone_three_four`: the literal capstone statement at `(3,4)` through the tight-row chain.
-/

set_option linter.style.longLine false

namespace LeanCH.BR.HalfRowsThree

open LeanCH.BR.BRq2 LeanCH.BR.BRq3 LeanCH.BR.TightRow LeanCH.BR.HalfRows

variable {D : CH.Digraph} {V : Finset ℕ}

theorem mem_inN3 {u y : ℕ} : y ∈ inN D V u ↔ y ∈ V ∧ D y u = true := Finset.mem_filter

/-- Non-neighbours of `u` in `V` (other than `u`). -/
def nonNbr (D : CH.Digraph) (V : Finset ℕ) (u : ℕ) : Finset ℕ :=
  V.filter (fun z => z ≠ u ∧ ¬ D u z = true ∧ ¬ D z u = true)

/-- Parents of `u` with no head among the heads of `u`. -/
def freePar (D : CH.Digraph) (V : Finset ℕ) (u : ℕ) : Finset ℕ :=
  (inN D V u).filter (fun w => ∀ a ∈ outN D V u, ¬ D w a = true)

/-- `V` splits into `u`, its heads, its parents and its non-neighbours. -/
theorem nonNbr_card (free : QFree D V 3) {u : ℕ} (hu : u ∈ V) :
    (nonNbr D V u).card + (outN D V u).card + (inN D V u).card + 1 = V.card := by
  classical
  have d1 : Disjoint (outN D V u) (inN D V u) := by
    rw [Finset.disjoint_left]
    intro z h1 h2
    exact digonfree free (by omega) hu (mem_outN.mp h1).1 (mem_outN.mp h1).2 (mem_inN3.mp h2).2
  have d2 : u ∉ outN D V u ∪ inN D V u := by
    intro h
    rcases Finset.mem_union.mp h with h | h
    · exact loopfree free (by omega) hu (mem_outN.mp h).2
    · exact loopfree free (by omega) hu (mem_inN3.mp h).2
  have d3 : Disjoint (nonNbr D V u) (insert u (outN D V u ∪ inN D V u)) := by
    rw [Finset.disjoint_left]
    intro z h1 h2
    obtain ⟨_, zu, nuz, nzu⟩ := Finset.mem_filter.mp h1
    rcases Finset.mem_insert.mp h2 with h | h
    · exact zu h
    · rcases Finset.mem_union.mp h with h | h
      · exact nuz (mem_outN.mp h).2
      · exact nzu (mem_inN3.mp h).2
  have cover : nonNbr D V u ∪ insert u (outN D V u ∪ inN D V u) = V := by
    ext z
    constructor
    · intro h
      rcases Finset.mem_union.mp h with h | h
      · exact (Finset.mem_filter.mp h).1
      · rcases Finset.mem_insert.mp h with h | h
        · rw [h]; exact hu
        · rcases Finset.mem_union.mp h with h | h
          · exact (mem_outN.mp h).1
          · exact (mem_inN3.mp h).1
    · intro zV
      by_cases zu : z = u
      · exact Finset.mem_union_right _ (Finset.mem_insert.mpr (Or.inl zu))
      by_cases uz : D u z = true
      · exact Finset.mem_union_right _
          (Finset.mem_insert_of_mem (Finset.mem_union_left _ (mem_outN.mpr ⟨zV, uz⟩)))
      by_cases zu' : D z u = true
      · exact Finset.mem_union_right _
          (Finset.mem_insert_of_mem (Finset.mem_union_right _ (mem_inN3.mpr ⟨zV, zu'⟩)))
      exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨zV, zu, uz, zu'⟩)
  have := Finset.card_union_of_disjoint d3
  rw [cover, Finset.card_insert_of_notMem d2, Finset.card_union_of_disjoint d1] at this
  omega

/-- A head of a head of `u` is neither `u` nor a parent of `u`. -/
theorem head_conf (free : QFree D V 3) {u a z : ℕ} (hu : u ∈ V) (ha : a ∈ outN D V u)
    (hz : z ∈ outN D V a) : z ≠ u ∧ z ∉ inN D V u := by
  obtain ⟨aV, ua⟩ := mem_outN.mp ha
  obtain ⟨zV, az⟩ := mem_outN.mp hz
  refine ⟨fun e => digonfree free (by omega) hu aV ua (by rw [e] at az; exact az), fun hzi => ?_⟩
  exact free u 3 (by omega) le_rfl
    (.step aV ua (.step zV az (.step hu (mem_inN3.mp hzi).2 (.refl u))))

/-- **(F4)** On at most four vertices, if every vertex has a head inside, each vertex has at most one head inside. -/
theorem one_head (free : QFree D V 3) {A : Finset ℕ} (hA : A ⊆ V) (small : A.card ≤ 4)
    (cyc : ∀ x ∈ A, ∃ y ∈ A, D x y = true) {a b c : ℕ} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A)
    (ab : D a b = true) (ac : D a c = true) : b = c := by
  classical
  by_contra bc
  have aV := hA ha
  have bV := hA hb
  have cV := hA hc
  have nab : b ≠ a := fun e => loopfree free (by omega) aV (by rw [e] at ab; exact ab)
  have nac : c ≠ a := fun e => loopfree free (by omega) aV (by rw [e] at ac; exact ac)
  have hTV : A.erase a ⊆ V := (Finset.erase_subset a A).trans hA
  have bT : b ∈ A.erase a := Finset.mem_erase.mpr ⟨nab, hb⟩
  have cT : c ∈ A.erase a := Finset.mem_erase.mpr ⟨nac, hc⟩
  have Tcard : (A.erase a).card ≤ 3 := by
    have := Finset.card_erase_of_mem ha
    omega
  -- a sink `t` of `A - a` points to `a`
  obtain ⟨t, tT, tsink⟩ := sink_of_small free hTV ⟨b, bT⟩ Tcard
  obtain ⟨_, tA⟩ := Finset.mem_erase.mp tT
  obtain ⟨y, yA, ty⟩ := cyc t tA
  have ya : y = a := by
    by_contra h
    exact tsink y (Finset.mem_erase.mpr ⟨h, yA⟩) ty
  rw [ya] at ty
  have tV := hA tA
  have ntb : t ≠ b := fun e => digonfree free (by omega) aV bV ab (by rw [e] at ty; exact ty)
  have ntc : t ≠ c := fun e => digonfree free (by omega) aV cV ac (by rw [e] at ty; exact ty)
  -- a sink `s` of `{b, c}` has a fourth head
  have pV : ({b, c} : Finset ℕ) ⊆ V := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl <;> assumption
  obtain ⟨s, sP, ssink⟩ := sink_of_small free pV ⟨b, by simp⟩
    ((Finset.card_insert_le _ _).trans (by simp))
  have sAs : s ∈ A ∧ D a s = true := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at sP
    rcases sP with rfl | rfl
    · exact ⟨hb, ab⟩
    · exact ⟨hc, ac⟩
  obtain ⟨sA, as⟩ := sAs
  have sV := hA sA
  obtain ⟨h, hhA, sh⟩ := cyc s sA
  have hb' : h ≠ b := fun e => ssink h (by rw [e]; simp) sh
  have hc' : h ≠ c := fun e => ssink h (by rw [e]; simp) sh
  have ha' : h ≠ a := fun e => digonfree free (by omega) aV sV as (by rw [e] at sh; exact sh)
  have ht' : h ≠ t := fun e => free a 3 (by omega) le_rfl
    (.step sV as (.step tV (by rw [e] at sh; exact sh) (.step aV ty (.refl a))))
  have sub : ({b, c, t, h} : Finset ℕ) ⊆ A.erase a := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact bT
    · exact cT
    · exact tT
    · exact Finset.mem_erase.mpr ⟨ha', hhA⟩
  have k : ({b, c, t, h} : Finset ℕ).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [bc, Ne.symm ntb, Ne.symm hb']),
      Finset.card_insert_of_notMem (by simp [Ne.symm ntc, Ne.symm hc']),
      Finset.card_insert_of_notMem (by simp [Ne.symm ht']), Finset.card_singleton]
  have := Finset.card_le_card sub
  omega

/-- **Local half law at `d = 3`.** In a `3`-free digraph on `11` vertices with all outdegrees `3` or `4`, every
vertex has at most `7` neighbours (at least three non-neighbours). -/
theorem local_bound (free : QFree D V 3) (card : V.card = 11)
    (deg : ∀ x ∈ V, 3 ≤ (outN D V x).card) (cap : ∀ x ∈ V, (outN D V x).card ≤ 4)
    {u : ℕ} (hu : u ∈ V) : (outN D V u).card + (inN D V u).card ≤ 7 := by
  classical
  by_contra big
  push Not at big
  have hZ := nonNbr_card free hu
  -- heads of heads lie in the heads or the non-neighbours of `u`
  have conf : ∀ a ∈ outN D V u, outN D V a ⊆ outN D (outN D V u) a ∪ nonNbr D V u := by
    intro a ha z hz
    obtain ⟨zu, zi⟩ := head_conf free hu ha hz
    obtain ⟨zV, az⟩ := mem_outN.mp hz
    by_cases uz : D u z = true
    · exact Finset.mem_union_left _ (mem_outN.mpr ⟨mem_outN.mpr ⟨zV, uz⟩, az⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨zV, zu, uz, fun h => zi (mem_inN3.mpr ⟨zV, h⟩)⟩)
  -- so (at most two non-neighbours) every head of `u` has a head among the heads of `u`
  have cyc : ∀ a ∈ outN D V u, ∃ y ∈ outN D V u, D a y = true := by
    intro a ha
    have c1 := Finset.card_le_card (conf a ha)
    have c2 := Finset.card_union_le (outN D (outN D V u) a) (nonNbr D V u)
    have c3 := deg a (outN_subset ha)
    obtain ⟨y, hy⟩ : (outN D (outN D V u) a).Nonempty := Finset.card_pos.mp (by omega)
    exact ⟨y, (mem_outN.mp hy).1, (mem_outN.mp hy).2⟩
  have four : (outN D V u).card = 4 := by
    have := cap u hu
    have := deg u hu
    by_contra h
    obtain ⟨a, ha, hs⟩ := sink_of_small free (A := outN D V u) outN_subset
      (Finset.card_pos.mp (by omega)) (by omega)
    obtain ⟨y, hy, ay⟩ := cyc a ha
    exact hs y hy ay
  have one : ∀ a ∈ outN D V u, (outN D (outN D V u) a).card ≤ 1 := by
    intro a ha
    rw [Finset.card_le_one]
    intro b hb c hc
    exact one_head free outN_subset (by omega) cyc ha (mem_outN.mp hb).1 (mem_outN.mp hc).1
      (mem_outN.mp hb).2 (mem_outN.mp hc).2
  -- every head of `u` dominates the non-neighbours of `u`
  have Zdom : ∀ a ∈ outN D V u, ∀ z ∈ nonNbr D V u, D a z = true := by
    intro a ha z hz
    by_contra naz
    have sub : outN D V a ⊆ outN D (outN D V u) a ∪ (nonNbr D V u).erase z := by
      intro y hy
      rcases Finset.mem_union.mp (conf a ha hy) with h | h
      · exact Finset.mem_union_left _ h
      · refine Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨?_, h⟩)
        rintro rfl
        exact naz (mem_outN.mp hy).2
    have c1 := Finset.card_le_card sub
    have c2 := Finset.card_union_le (outN D (outN D V u) a) ((nonNbr D V u).erase z)
    have c3 := Finset.card_erase_of_mem hz
    have c4 := deg a (outN_subset ha)
    have c5 := one a ha
    omega
  obtain ⟨a0, ha0⟩ : (outN D V u).Nonempty := Finset.card_pos.mp (by omega)
  have Zcard : (nonNbr D V u).card = 2 := by
    have c1 := Finset.card_le_card (conf a0 ha0)
    have c2 := Finset.card_union_le (outN D (outN D V u) a0) (nonNbr D V u)
    have c4 := deg a0 (outN_subset ha0)
    have c5 := one a0 ha0
    omega
  have Icard : (inN D V u).card = 4 := by omega
  -- Z-confinement: heads of non-neighbours lie in the free parents or the non-neighbours
  have zconf : ∀ z ∈ nonNbr D V u, ∀ y ∈ outN D V z, y ∈ freePar D V u ∨ y ∈ nonNbr D V u := by
    intro z hz y hy
    obtain ⟨zV, _, _, nzu⟩ := Finset.mem_filter.mp hz
    obtain ⟨yV, zy⟩ := mem_outN.mp hy
    have yu : y ≠ u := fun e => nzu (by rw [← e]; exact zy)
    by_cases uy : D u y = true
    · exact absurd zy (fun zy' => digonfree free (by omega) yV zV
        (Zdom y (mem_outN.mpr ⟨yV, uy⟩) z hz) zy')
    by_cases yu' : D y u = true
    · left
      refine Finset.mem_filter.mpr ⟨mem_inN3.mpr ⟨yV, yu'⟩, fun a ha ya => ?_⟩
      exact free z 3 (by omega) le_rfl
        (.step yV zy (.step (outN_subset ha) ya (.step zV (Zdom a ha z hz) (.refl z))))
    · right
      exact Finset.mem_filter.mpr ⟨yV, yu, uy, yu'⟩
  by_cases hI : ∀ w ∈ inN D V u, ∀ a ∈ outN D V u, ¬ D w a = true
  · -- all four parents are free: a 3-free digraph on 6 vertices with minimum outdegree 2
    have dIZ : Disjoint (inN D V u) (nonNbr D V u) := by
      rw [Finset.disjoint_left]
      intro z h1 h2
      exact (Finset.mem_filter.mp h2).2.2.2 (mem_inN3.mp h1).2
    have Bcard : (inN D V u ∪ nonNbr D V u).card = 6 := by
      rw [Finset.card_union_of_disjoint dIZ]
      omega
    have BV : inN D V u ∪ nonNbr D V u ⊆ V :=
      Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    refine tightLaw_implies_CH (s := 1) tightLaw_three_one (free.mono_set BV) (by omega) (by omega) ?_
    intro x hx
    rcases Finset.mem_union.mp hx with hw | hz
    · have sub : outN D V x ⊆ insert u (outN D (inN D V u ∪ nonNbr D V u) x) := by
        intro y hy
        obtain ⟨yV, xy⟩ := mem_outN.mp hy
        by_cases yu : y = u
        · exact Finset.mem_insert.mpr (Or.inl yu)
        · refine Finset.mem_insert_of_mem (mem_outN.mpr ⟨?_, xy⟩)
          by_cases uy : D u y = true
          · exact absurd xy (hI x hw y (mem_outN.mpr ⟨yV, uy⟩))
          by_cases yu' : D y u = true
          · exact Finset.mem_union_left _ (mem_inN3.mpr ⟨yV, yu'⟩)
          · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨yV, yu, uy, yu'⟩)
      have c1 := Finset.card_le_card sub
      have c1' := Finset.card_insert_le u (outN D (inN D V u ∪ nonNbr D V u) x)
      have c2 := deg x (mem_inN3.mp hw).1
      omega
    · have sub : outN D V x ⊆ outN D (inN D V u ∪ nonNbr D V u) x := by
        intro y hy
        refine mem_outN.mpr ⟨?_, (mem_outN.mp hy).2⟩
        rcases zconf x hz y hy with h | h
        · exact Finset.mem_union_left _ (Finset.mem_filter.mp h).1
        · exact Finset.mem_union_right _ h
      have c1 := Finset.card_le_card sub
      have c2 := deg x (Finset.mem_filter.mp hz).1
      omega
  · -- one parent `w0` points into the heads: the three free parents carry a cycle
    push Not at hI
    obtain ⟨w0, hw0, a1, ha1, w0a⟩ := hI
    have I'sub : freePar D V u ⊆ (inN D V u).erase w0 := by
      intro w hw
      obtain ⟨wi, wfree⟩ := Finset.mem_filter.mp hw
      refine Finset.mem_erase.mpr ⟨?_, wi⟩
      rintro rfl
      exact wfree a1 ha1 w0a
    have eraseCard := Finset.card_erase_of_mem hw0
    have c3 : (freePar D V u).card ≤ 3 := by
      have := Finset.card_le_card I'sub
      omega
    -- a sink of the two non-neighbours
    obtain ⟨zs, hzs, zsink⟩ := sink_of_small free (A := nonNbr D V u) (Finset.filter_subset _ _)
      (Finset.card_pos.mp (by omega)) (by omega)
    have zsV : zs ∈ V := (Finset.mem_filter.mp hzs).1
    have sinkEq : ∀ z ∈ nonNbr D V u, (∀ y ∈ nonNbr D V u, ¬ D z y = true) →
        outN D V z = freePar D V u := by
      intro z hz hs
      have sub : outN D V z ⊆ freePar D V u := by
        intro y hy
        rcases zconf z hz y hy with h | h
        · exact h
        · exact absurd (mem_outN.mp hy).2 (hs y h)
      have := deg z (Finset.mem_filter.mp hz).1
      exact Finset.eq_of_subset_of_card_le sub (by omega)
    have I'3 : (freePar D V u).card = 3 := by
      have := deg zs zsV
      rw [sinkEq zs hzs zsink] at this
      omega
    have I'eq : freePar D V u = (inN D V u).erase w0 :=
      Finset.eq_of_subset_of_card_le I'sub (by omega)
    have toI' : ∀ z ∈ nonNbr D V u, (∀ y ∈ nonNbr D V u, ¬ D z y = true) →
        ∀ w ∈ freePar D V u, D z w = true := by
      intro z hz hs w hw
      rw [← sinkEq z hz hs] at hw
      exact (mem_outN.mp hw).2
    -- no free parent points to a non-neighbour
    have noZ : ∀ w ∈ freePar D V u, ∀ z ∈ nonNbr D V u, ¬ D w z = true := by
      intro w hw z hz wz
      have wV := (mem_inN3.mp (Finset.mem_filter.mp hw).1).1
      have zV := (Finset.mem_filter.mp hz).1
      by_cases zzs : z = zs
      · rw [zzs] at wz
        exact digonfree free (by omega) wV zsV wz (toI' zs hzs zsink w hw)
      by_cases zz : D z zs = true
      · exact free z 3 (by omega) le_rfl
          (.step zsV zz (.step wV (toI' zs hzs zsink w hw) (.step zV wz (.refl z))))
      · have zsk : ∀ y ∈ nonNbr D V u, ¬ D z y = true := by
          intro y hy zy
          have yz : y ≠ z := fun e => loopfree free (by omega) zV (by rw [e] at zy; exact zy)
          have yzs : y ≠ zs := fun e => zz (by rw [e] at zy; exact zy)
          have sub3 : ({y, z, zs} : Finset ℕ) ⊆ nonNbr D V u := by
            intro x hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl | rfl <;> assumption
          have k : ({y, z, zs} : Finset ℕ).card = 3 := by
            rw [Finset.card_insert_of_notMem (by simp [yz, yzs]),
              Finset.card_insert_of_notMem (by simp [zzs]), Finset.card_singleton]
          have := Finset.card_le_card sub3
          omega
        exact digonfree free (by omega) wV zV wz (toI' z hz zsk w hw)
    -- so every free parent has a head among the free parents
    have cycI : ∀ w ∈ freePar D V u, ∃ y ∈ freePar D V u, D w y = true := by
      intro w hw
      obtain ⟨wi, wfree⟩ := Finset.mem_filter.mp hw
      obtain ⟨wV, _⟩ := mem_inN3.mp wi
      have sub : outN D V w ⊆ insert u (insert w0 (outN D (freePar D V u) w)) := by
        intro y hy
        obtain ⟨yV, wy⟩ := mem_outN.mp hy
        by_cases yu : y = u
        · exact Finset.mem_insert.mpr (Or.inl yu)
        by_cases yw0 : y = w0
        · exact Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl yw0))
        refine Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (mem_outN.mpr ⟨?_, wy⟩))
        rw [I'eq]
        refine Finset.mem_erase.mpr ⟨yw0, ?_⟩
        by_cases uy : D u y = true
        · exact absurd wy (wfree y (mem_outN.mpr ⟨yV, uy⟩))
        by_cases yu' : D y u = true
        · exact mem_inN3.mpr ⟨yV, yu'⟩
        · exact absurd wy (noZ w hw y (Finset.mem_filter.mpr ⟨yV, yu, uy, yu'⟩))
      have c1 := Finset.card_le_card sub
      have c1' := Finset.card_insert_le u (insert w0 (outN D (freePar D V u) w))
      have c1'' := Finset.card_insert_le w0 (outN D (freePar D V u) w)
      have c2 := deg w wV
      obtain ⟨y, hy⟩ : (outN D (freePar D V u) w).Nonempty := Finset.card_pos.mp (by omega)
      exact ⟨y, (mem_outN.mp hy).1, (mem_outN.mp hy).2⟩
    have I'V : freePar D V u ⊆ V := fun w hw => (mem_inN3.mp (Finset.mem_filter.mp hw).1).1
    obtain ⟨w, hw, hs⟩ := sink_of_small free I'V (Finset.card_pos.mp (by omega)) (by omega)
    obtain ⟨y, hy, wy⟩ := cycI w hw
    exact hs y hy wy

/-- Half the rows are tight for the trimmed graph (outdegrees `3` or `4`). -/
theorem half_trimmed (free : QFree D V 3) (card : V.card = 11)
    (deg : ∀ x ∈ V, 3 ≤ (outN D V x).card) (cap : ∀ x ∈ V, (outN D V x).card ≤ 4) :
    V.card ≤ 2 * (V.filter (fun x => (outN D V x).card = 3)).card := by
  classical
  have pt : ∀ u ∈ V, (outN D V u).card + (inN D V u).card ≤ 7 :=
    fun u hu => local_bound free card deg cap hu
  have s1 := Finset.sum_le_sum pt
  rw [Finset.sum_add_distrib] at s1
  have sin : ∑ u ∈ V, (inN D V u).card = ∑ u ∈ V, (outN D V u).card :=
    sum_indeg_eq_sum_outdeg D V
  rw [sin] at s1
  simp only [Finset.sum_const] at s1
  have hs7 : V.card • (7 : ℕ) = V.card * 7 := by simp
  rw [hs7] at s1
  have lo : 4 * V.card ≤
      ∑ u ∈ V, (outN D V u).card + (V.filter (fun x => (outN D V x).card = 3)).card := by
    rw [Finset.card_filter, ← Finset.sum_add_distrib]
    have := Finset.card_nsmul_le_sum V
      (fun u => (outN D V u).card + if (outN D V u).card = 3 then 1 else 0) 4
      (fun u hu => by have := deg u hu; split_ifs <;> omega)
    simpa [mul_comm] using this
  omega

/-- **Half the rows are tight at `d = 3`**, for every `3`-free digraph on `11` vertices with outdegrees `≥ 3`. -/
theorem half_three (free : QFree D V 3) (card : V.card = 11)
    (deg : ∀ x ∈ V, 3 ≤ (outN D V x).card) :
    V.card ≤ 2 * (V.filter (fun x => (outN D V x).card = 3)).card := by
  obtain ⟨G, sub, trim⟩ := exists_trim (V := V) (G := D) (d := 3)
  have gfree : QFree G V 3 := qfree_sub sub free
  have gdeg : ∀ x ∈ V, 3 ≤ (outN G V x).card := by
    intro x hx
    have := deg x hx
    rw [trim x hx]
    omega
  have gcap : ∀ x ∈ V, (outN G V x).card ≤ 4 := by
    intro x hx
    rw [trim x hx]
    omega
  have key := half_trimmed gfree card gdeg gcap
  have same : V.filter (fun x => (outN G V x).card = 3) = V.filter (fun x => (outN D V x).card = 3) := by
    apply Finset.filter_congr
    intro x hx
    have := deg x hx
    rw [trim x hx]
    omega
  rw [same] at key
  exact key

/-- `TightLaw 3 3` is a theorem. -/
theorem tightLaw_three_three : TightLaw 3 3 := by
  intro E U free card deg
  have := half_three free (by omega) deg
  omega

/-- The literal capstone statement at `(3,4)` through the tight-row chain. -/
theorem capstone_three_four {n : ℕ} {D : CH.Digraph} (hn : 0 < n) (order : n ≤ 3 * 4)
    (loop : CH.Loopless D n) (degree : CH.MinOutdegreeAtLeast D n 4) :
    CH.HasDirectedCycleAtMost D n 3 :=
  capstone_of_tightLaw hn (by omega) order loop degree tightLaw_three_three

end LeanCH.BR.HalfRowsThree

open LeanCH.BR.HalfRowsThree in
#print axioms one_head
open LeanCH.BR.HalfRowsThree in
#print axioms local_bound
open LeanCH.BR.HalfRowsThree in
#print axioms half_three
open LeanCH.BR.HalfRowsThree in
#print axioms tightLaw_three_three
open LeanCH.BR.HalfRowsThree in
#print axioms capstone_three_four
