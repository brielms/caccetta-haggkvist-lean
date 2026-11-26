import checkpoints.shen_extension.LoneSelection

/-!
Two marked vertices in an oriented graph without directed triangles on `3t` vertices.

`TwoMark r t a b`: every vertex other than `a`, `b` has both degrees at least `t`; `a` and
`b` have out-degree at least `t - 1`, one of them at least `t`. No assumption on the
in-degrees of `a`, `b`.

* `TwoMark.common_head`: `a` and `b` have a common out-neighbour.
* `TwoMark.surplus`: `|N++(a)| + |N++(b)| ≥ d+(a) + d+(b) + 2`.
* `overload`: on at most `3t` vertices with out-degree at least `t` except at least `t - 1`
  at `x`, the incoming deficits `∑ (t - d-(v))` sum to at least two.
* `parent_deficit`: with every out-degree at least `r` on at most `3r` vertices the
  incoming deficits sum to at least four.

(Relayed paper argument, 27 November 2026.)
-/

namespace LeanCH.BR.TwoSeymour

open OAI.SeymourSecondNeighborhood
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

structure TwoMark (r : V → V → Prop) (t : ℕ) (a b : V) : Prop where
  oriented : IsOriented r
  tri : ∀ u v w, r u v → r v w → ¬ r w u
  card : Fintype.card V = 3 * t
  two : 2 ≤ t
  ne : a ≠ b
  out : ∀ v, v ≠ a → v ≠ b → t ≤ (firstNeighbors r v).card
  inn : ∀ v, v ≠ a → v ≠ b → t ≤ (firstNeighbors (rev r) v).card
  outa : t ≤ (firstNeighbors r a).card + 1
  outb : t ≤ (firstNeighbors r b).card + 1
  one : t ≤ (firstNeighbors r a).card ∨ t ≤ (firstNeighbors r b).card

/-- A nonempty set closed under taking a predecessor has at least four vertices. -/
theorem four_le_of_pred_closed (r : V → V → Prop) (hr : IsOriented r)
    (htri : ∀ u v w, r u v → r v w → ¬ r w u) (T : Finset V) (hT : T.Nonempty)
    (hpred : ∀ v ∈ T, ∃ u ∈ T, r u v) : 4 ≤ T.card := by
  classical
  obtain ⟨v0, h0⟩ := hT
  obtain ⟨v1, h1, e10⟩ := hpred v0 h0
  obtain ⟨v2, h2, e21⟩ := hpred v1 h1
  obtain ⟨v3, h3, e32⟩ := hpred v2 h2
  have n01 : v0 ≠ v1 := by
    intro h
    rw [h] at e10
    exact hr.loopless v1 e10
  have n12 : v1 ≠ v2 := by
    intro h
    rw [h] at e21
    exact hr.loopless v2 e21
  have n23 : v2 ≠ v3 := by
    intro h
    rw [h] at e32
    exact hr.loopless v3 e32
  have n02 : v0 ≠ v2 := by
    intro h
    rw [← h] at e21
    exact hr.asymmetric e10 e21
  have n13 : v1 ≠ v3 := by
    intro h
    rw [← h] at e32
    exact hr.asymmetric e21 e32
  have n03 : v0 ≠ v3 := by
    intro h
    rw [← h] at e32
    exact htri v0 v2 v1 e32 e21 e10
  have c3 : ({v3} : Finset V).card = 1 := Finset.card_singleton _
  have c2 : ({v2, v3} : Finset V).card = 2 := by
    rw [Finset.card_insert_of_notMem (by
      rw [Finset.mem_singleton]
      exact n23), c3]
  have c1 : ({v1, v2, v3} : Finset V).card = 3 := by
    rw [Finset.card_insert_of_notMem (by
      rw [Finset.mem_insert, Finset.mem_singleton]
      exact fun h => h.elim n12 n13), c2]
  have c0 : ({v0, v1, v2, v3} : Finset V).card = 4 := by
    rw [Finset.card_insert_of_notMem (by
      rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
      exact fun h => h.elim n01 (fun h => h.elim n02 n03)), c1]
  have hsub : ({v0, v1, v2, v3} : Finset V) ⊆ T := by
    intro z hz
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with hz | hz | hz | hz
    · rw [hz]
      exact h0
    · rw [hz]
      exact h1
    · rw [hz]
      exact h2
    · rw [hz]
      exact h3
  have := Finset.card_le_card hsub
  omega

namespace TwoMark

variable {r : V → V → Prop} {t : ℕ} {a b : V}

theorem symm (h : TwoMark r t a b) : TwoMark r t b a where
  oriented := h.oriented
  tri := h.tri
  card := h.card
  two := h.two
  ne := h.ne.symm
  out := fun v hb ha => h.out v ha hb
  inn := fun v hb ha => h.inn v ha hb
  outa := h.outb
  outb := h.outa
  one := h.one.symm

theorem second_le (h : TwoMark r t a b) (v : V) :
    (secondNeighbors r v).card ≤ (nonadj r v).card :=
  Finset.card_le_card (second_subset_nonadj r h.tri v)

theorem nonadj_ord (h : TwoMark r t a b) (v : V) (ha : v ≠ a) (hb : v ≠ b) :
    (nonadj r v).card + 1 ≤ t := by
  have h1 := card_partition r h.oriented v
  have h2 := h.card
  have h3 := h.out v ha hb
  have h4 := h.inn v ha hb
  omega

theorem ord_bad (h : TwoMark r t a b) (v : V) (ha : v ≠ a) (hb : v ≠ b) :
    (secondNeighbors r v).card + 1 ≤ (firstNeighbors r v).card := by
  have h1 := h.second_le v
  have h2 := h.nonadj_ord v ha hb
  have h3 := h.out v ha hb
  omega

theorem sinkless (h : TwoMark r t a b) : ∀ v, ∃ z, r v z := by
  intro v
  have hpos : 0 < (firstNeighbors r v).card := by
    have h2 := h.two
    by_cases hva : v = a
    · have h1 := h.outa
      rw [hva]
      omega
    · by_cases hvb : v = b
      · have h1 := h.outb
        rw [hvb]
        omega
      · have h1 := h.out v hva hvb
        omega
  obtain ⟨z, hz⟩ := Finset.card_pos.mp hpos
  exact ⟨z, mem_firstNeighbors.mp hz⟩

/-- With disjoint out-neighbourhoods there is no common predecessor. -/
theorem no_common_pred (h : TwoMark r t a b) (hcs : ∀ c, r a c → r b c → False)
    (u : V) (hua : r u a) (hub : r u b) : False := by
  classical
  have hr := h.oriented
  have hua' : u ≠ a := by
    intro heq
    rw [heq] at hua
    exact hr.loopless a hua
  have hub' : u ≠ b := by
    intro heq
    rw [heq] at hub
    exact hr.loopless b hub
  have hdisj : Disjoint (firstNeighbors r a) (firstNeighbors r b) := by
    apply Finset.disjoint_left.mpr
    intro c h1 h2
    exact hcs c (mem_firstNeighbors.mp h1) (mem_firstNeighbors.mp h2)
  -- a vertex among a, b outside both out-neighbourhoods
  obtain ⟨w, hwu, hwX, hwI⟩ : ∃ w, w ≠ u ∧
      w ∉ firstNeighbors r a ∪ firstNeighbors r b ∧ ¬ r w u := by
    by_cases hba : r b a
    · refine ⟨b, fun heq => hub' heq.symm, ?_, hr.asymmetric hub⟩
      intro hc
      rcases Finset.mem_union.mp hc with hc | hc
      · exact hr.asymmetric hba (mem_firstNeighbors.mp hc)
      · exact hr.loopless b (mem_firstNeighbors.mp hc)
    · refine ⟨a, fun heq => hua' heq.symm, ?_, hr.asymmetric hua⟩
      intro hc
      rcases Finset.mem_union.mp hc with hc | hc
      · exact hr.loopless a (mem_firstNeighbors.mp hc)
      · exact hba (mem_firstNeighbors.mp hc)
  have huX : u ∉ firstNeighbors r a ∪ firstNeighbors r b := by
    intro hc
    rcases Finset.mem_union.mp hc with hc | hc
    · exact hr.asymmetric hua (mem_firstNeighbors.mp hc)
    · exact hr.asymmetric hub (mem_firstNeighbors.mp hc)
  have hwY : w ∉ insert u (firstNeighbors r a ∪ firstNeighbors r b) := by
    intro hc
    rcases Finset.mem_insert.mp hc with hc | hc
    · exact hwu hc
    · exact hwX hc
  have hId : Disjoint (firstNeighbors (rev r) u)
      (insert w (insert u (firstNeighbors r a ∪ firstNeighbors r b))) := by
    apply Finset.disjoint_left.mpr
    intro z hz hzZ
    have hzu : r z u := (mem_firstNeighbors (r := rev r)).mp hz
    rcases Finset.mem_insert.mp hzZ with hzw | hzZ
    · rw [hzw] at hzu
      exact hwI hzu
    · rcases Finset.mem_insert.mp hzZ with hzu' | hzZ
      · rw [hzu'] at hzu
        exact hr.loopless u hzu
      · rcases Finset.mem_union.mp hzZ with hz1 | hz1
        · exact h.tri u a z hua (mem_firstNeighbors.mp hz1) hzu
        · exact h.tri u b z hub (mem_firstNeighbors.mp hz1) hzu
  have hcardU := Finset.card_le_card (Finset.subset_univ
    (firstNeighbors (rev r) u ∪
      insert w (insert u (firstNeighbors r a ∪ firstNeighbors r b))))
  rw [Finset.card_union_of_disjoint hId, Finset.card_insert_of_notMem hwY,
    Finset.card_insert_of_notMem huX, Finset.card_union_of_disjoint hdisj,
    Finset.card_univ] at hcardU
  have h1 := h.inn u hua' hub'
  have h2 := h.card
  have h3 := h.outa
  have h4 := h.outb
  have h5 := h.one
  omega

/-- The dual weighting after deleting the two marked vertices. -/
theorem dual (h : TwoMark r t a b) (hcs : ∀ c, r a c → r b c → False)
    (hcp : ∀ c, r c a → r c b → False) :
    ∃ P : V → ℝ, (∀ v, 0 ≤ P v) ∧ ∑ v, P v = 1 ∧ P a = 0 ∧ P b = 0 ∧
      (∀ v, P v ≠ 0 → (firstNeighbors r v).card = t ∧
        ((r a v ∧ r v b) ∨ (r b v ∧ r v a))) ∧
      (∀ u, u ≠ a → u ≠ b →
        P u + 2 * ∑ z ∈ firstNeighbors r u, P z +
          ∑ z ∈ firstNeighbors (rev r) u, P z = 1) := by
  classical
  have hr := h.oriented
  have hρ : IsOriented (sub a b (rev r)) :=
    ⟨fun v => hr.loopless v.1, fun hab hba => hr.asymmetric hba hab⟩
  have hρtri : ∀ u v w, sub a b (rev r) u v → sub a b (rev r) v w →
      ¬ sub a b (rev r) w u := fun u v w huv hvw hwu => h.tri w.1 v.1 u.1 hvw huv hwu
  -- a third vertex
  obtain ⟨z0, hz0a, hz0b⟩ : ∃ z0, z0 ≠ a ∧ z0 ≠ b := by
    have hc : 2 < (Finset.univ : Finset V).card := by
      rw [Finset.card_univ]
      have := h.card
      have := h.two
      omega
    by_contra hnone
    have hsub : (Finset.univ : Finset V) ⊆ {a, b} := by
      intro z _
      by_contra hz
      apply hnone
      refine ⟨z, ?_, ?_⟩
      · intro heq
        apply hz
        rw [heq]
        exact Finset.mem_insert_self a {b}
      · intro heq
        apply hz
        rw [heq]
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self b)
    have hle := Finset.card_le_card hsub
    have hpair : ({a, b} : Finset V).card ≤ 2 := Finset.card_le_two
    omega
  have hne : Nonempty {v : V // v ≠ a ∧ v ≠ b} := ⟨⟨z0, hz0a, hz0b⟩⟩
  have hflip : ∀ u : {v : V // v ≠ a ∧ v ≠ b},
      firstNeighbors (rev (sub a b (rev r))) u = firstNeighbors (sub a b r) u := by
    intro u
    ext z
    rw [mem_firstNeighbors, mem_firstNeighbors]
    exact Iff.rfl
  have hin : ∀ u : {v : V // v ≠ a ∧ v ≠ b},
      t ≤ (firstNeighbors (sub a b (rev r)) u).card + 1 ∧
        ((firstNeighbors (sub a b (rev r)) u).card + 1 = t → r a u.1 ∨ r b u.1) := by
    intro u
    have h1 := congrArg Finset.card (first_sub_map a b (rev r) u)
    rw [Finset.card_map] at h1
    have h2 := card_erase_two (firstNeighbors (rev r) u.1) a b h.ne
    have h3 := h.inn u.1 u.2.1 u.2.2
    by_cases hx : a ∈ firstNeighbors (rev r) u.1
    · by_cases hy : b ∈ firstNeighbors (rev r) u.1
      · exact absurd (hcs u.1 ((mem_firstNeighbors (r := rev r)).mp hx)
          ((mem_firstNeighbors (r := rev r)).mp hy)) id
      · simp only [hx, hy, ↓reduceIte] at h2
        exact ⟨by omega, fun _ => Or.inl ((mem_firstNeighbors (r := rev r)).mp hx)⟩
    · by_cases hy : b ∈ firstNeighbors (rev r) u.1
      · simp only [hx, hy, ↓reduceIte] at h2
        exact ⟨by omega, fun _ => Or.inr ((mem_firstNeighbors (r := rev r)).mp hy)⟩
      · simp only [hx, hy, ↓reduceIte] at h2
        exact ⟨by omega, fun heq => by omega⟩
  have hout : ∀ u : {v : V // v ≠ a ∧ v ≠ b},
      t ≤ (firstNeighbors (sub a b r) u).card + 1 ∧
        ((firstNeighbors (sub a b r) u).card + 1 = t →
          (firstNeighbors r u.1).card = t ∧ (r u.1 a ∨ r u.1 b)) := by
    intro u
    have h1 := congrArg Finset.card (first_sub_map a b r u)
    rw [Finset.card_map] at h1
    have h2 := card_erase_two (firstNeighbors r u.1) a b h.ne
    have h3 := h.out u.1 u.2.1 u.2.2
    by_cases hx : a ∈ firstNeighbors r u.1
    · by_cases hy : b ∈ firstNeighbors r u.1
      · exact absurd (hcp u.1 (mem_firstNeighbors.mp hx) (mem_firstNeighbors.mp hy)) id
      · simp only [hx, hy, ↓reduceIte] at h2
        exact ⟨by omega, fun _ => ⟨by omega, Or.inl (mem_firstNeighbors.mp hx)⟩⟩
    · by_cases hy : b ∈ firstNeighbors r u.1
      · simp only [hx, hy, ↓reduceIte] at h2
        exact ⟨by omega, fun _ => ⟨by omega, Or.inr (mem_firstNeighbors.mp hy)⟩⟩
      · simp only [hx, hy, ↓reduceIte] at h2
        exact ⟨by omega, fun heq => by omega⟩
  have hcardW : Fintype.card {v : V // v ≠ a ∧ v ≠ b} + 2 = 3 * t := by
    have h1 := congrArg Finset.card (univ_sub_map a b)
    rw [Finset.card_map, Finset.card_univ] at h1
    have h2 := card_erase_two (Finset.univ : Finset V) a b h.ne
    simp only [Finset.mem_univ, ↓reduceIte, Finset.card_univ] at h2
    have h3 := h.card
    omega
  have hpart : ∀ u : {v : V // v ≠ a ∧ v ≠ b},
      (firstNeighbors (sub a b (rev r)) u).card + (firstNeighbors (sub a b r) u).card +
        (nonadj (sub a b (rev r)) u).card + 3 = 3 * t := by
    intro u
    have h1 := card_partition (sub a b (rev r)) hρ u
    rw [hflip u] at h1
    omega
  have hSle : ∀ u : {v : V // v ≠ a ∧ v ≠ b},
      (secondNeighbors (sub a b (rev r)) u).card ≤ (nonadj (sub a b (rev r)) u).card :=
    fun u => Finset.card_le_card (second_subset_nonadj _ hρtri u)
  have hnoW : ∀ u : {v : V // v ≠ a ∧ v ≠ b},
      ∑ _z ∈ secondNeighbors (sub a b (rev r)) u, (1 : ℝ) ≤
        ∑ _z ∈ firstNeighbors (sub a b (rev r)) u, (1 : ℝ) := by
    intro u
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    have h1 := hSle u
    have h2 := hpart u
    have h3 := (hin u).1
    have h4 := (hout u).1
    exact_mod_cast (by omega : (secondNeighbors (sub a b (rev r)) u).card ≤
      (firstNeighbors (sub a b (rev r)) u).card)
  obtain ⟨p, hp0, hp1, hptied, hpcoord⟩ := tied_dual (sub a b (rev r)) hρ
    (fun _ => (1 : ℝ)) (fun _ => one_pos) hnoW
  have htiedfacts : ∀ v : {v : V // v ≠ a ∧ v ≠ b}, p v ≠ 0 →
      (firstNeighbors (sub a b (rev r)) v).card + 1 = t ∧
        (firstNeighbors (sub a b r) v).card + 1 = t ∧
        secondNeighbors (sub a b (rev r)) v = nonadj (sub a b (rev r)) v := by
    intro v hv
    have htie := hptied v hv
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at htie
    have htieN : (secondNeighbors (sub a b (rev r)) v).card =
        (firstNeighbors (sub a b (rev r)) v).card := by exact_mod_cast htie
    have h1 := hSle v
    have h2 := hpart v
    have h3 := (hin v).1
    have h4 := (hout v).1
    refine ⟨by omega, by omega, ?_⟩
    exact Finset.eq_of_subset_of_card_le (second_subset_nonadj _ hρtri v) (by omega)
  let P : V → ℝ := fun v => if hv : v ≠ a ∧ v ≠ b then p ⟨v, hv⟩ else 0
  have hPsub : ∀ w : {v : V // v ≠ a ∧ v ≠ b}, P w.1 = p w := by
    intro w
    show (if hv : w.1 ≠ a ∧ w.1 ≠ b then p ⟨w.1, hv⟩ else 0) = p w
    rw [dif_pos w.2]
  have hPa : P a = 0 := by
    show (if hv : a ≠ a ∧ a ≠ b then p ⟨a, hv⟩ else 0) = 0
    rw [dif_neg (fun hc => hc.1 rfl)]
  have hPb : P b = 0 := by
    show (if hv : b ≠ a ∧ b ≠ b then p ⟨b, hv⟩ else 0) = 0
    rw [dif_neg (fun hc => hc.2 rfl)]
  have hP0 : ∀ v, 0 ≤ P v := by
    intro v
    by_cases hv : v ≠ a ∧ v ≠ b
    · have h1 := hPsub ⟨v, hv⟩
      rw [h1]
      exact hp0 _
    · show 0 ≤ (if hv : v ≠ a ∧ v ≠ b then p ⟨v, hv⟩ else 0)
      rw [dif_neg hv]
  have htransfer : ∀ A : Finset {v : V // v ≠ a ∧ v ≠ b},
      ∑ w ∈ A, p w = ∑ z ∈ A.map (subEmb a b), P z := by
    intro A
    rw [Finset.sum_map]
    apply Finset.sum_congr rfl
    intro w _
    exact (hPsub w).symm
  have herase : ∀ A : Finset V, ∑ z ∈ (A.erase a).erase b, P z = ∑ z ∈ A, P z := by
    intro A
    rw [Finset.sum_erase _ hPb, Finset.sum_erase _ hPa]
  have hfirstP : ∀ (q : V → V → Prop) (u : {v : V // v ≠ a ∧ v ≠ b}),
      ∑ w ∈ firstNeighbors (sub a b q) u, p w = ∑ z ∈ firstNeighbors q u.1, P z := by
    intro q u
    rw [htransfer, first_sub_map, herase]
  have hPsum : ∑ v, P v = 1 := by
    rw [← herase Finset.univ, ← univ_sub_map, ← htransfer]
    exact hp1
  refine ⟨P, hP0, hPsum, hPa, hPb, ?_, ?_⟩
  · intro v hv
    have hvc : v ≠ a ∧ v ≠ b := by
      by_contra hc
      apply hv
      show (if hv : v ≠ a ∧ v ≠ b then p ⟨v, hv⟩ else 0) = 0
      rw [dif_neg hc]
    have hpv : p ⟨v, hvc⟩ ≠ 0 := by
      have h1 := hPsub ⟨v, hvc⟩
      rw [← h1]
      exact hv
    obtain ⟨hi, ho, _⟩ := htiedfacts ⟨v, hvc⟩ hpv
    have hI := (hin ⟨v, hvc⟩).2 hi
    obtain ⟨hOc, hO⟩ := (hout ⟨v, hvc⟩).2 ho
    refine ⟨hOc, ?_⟩
    rcases hI with hxv | hyv
    · rcases hO with hvx | hvy
      · exact absurd hvx (hr.asymmetric hxv)
      · exact Or.inl ⟨hxv, hvy⟩
    · rcases hO with hvx | hvy
      · exact Or.inr ⟨hyv, hvx⟩
      · exact absurd hvy (hr.asymmetric hyv)
  · intro u hux huy
    have hpartsum := sum_partition (sub a b (rev r)) hρ p ⟨u, hux, huy⟩
    rw [hp1, hflip] at hpartsum
    have hcoord := hpcoord ⟨u, hux, huy⟩
    have hR : Finset.univ.filter (fun v : {v : V // v ≠ a ∧ v ≠ b} =>
        (⟨u, hux, huy⟩ : {v : V // v ≠ a ∧ v ≠ b}) ∈ firstNeighbors (sub a b (rev r)) v) =
          firstNeighbors (sub a b r) ⟨u, hux, huy⟩ := by
      ext v
      rw [Finset.mem_filter, mem_firstNeighbors, mem_firstNeighbors]
      exact ⟨fun hc => hc.2, fun hc => ⟨Finset.mem_univ _, hc⟩⟩
    have hL : ∑ v ∈ Finset.univ.filter (fun v : {v : V // v ≠ a ∧ v ≠ b} =>
        (⟨u, hux, huy⟩ : {v : V // v ≠ a ∧ v ≠ b}) ∈ secondNeighbors (sub a b (rev r)) v),
          p v = ∑ v ∈ nonadj (sub a b (rev r)) ⟨u, hux, huy⟩, p v := by
      have hA := Finset.sum_filter (s := (Finset.univ : Finset {v : V // v ≠ a ∧ v ≠ b}))
        (fun v => (⟨u, hux, huy⟩ : {v : V // v ≠ a ∧ v ≠ b}) ∈
          secondNeighbors (sub a b (rev r)) v) p
      have hB : ∑ v ∈ nonadj (sub a b (rev r)) ⟨u, hux, huy⟩, p v =
          ∑ v, if v ∈ nonadj (sub a b (rev r)) ⟨u, hux, huy⟩ then p v else 0 := by
        rw [Finset.sum_ite_mem, Finset.univ_inter]
      rw [hA, hB]
      apply Finset.sum_congr rfl
      intro v _
      by_cases hpv : p v = 0
      · simp only [hpv, ite_self]
      · obtain ⟨_, _, hS⟩ := htiedfacts v hpv
        have hiff : (⟨u, hux, huy⟩ : {v : V // v ≠ a ∧ v ≠ b}) ∈
            secondNeighbors (sub a b (rev r)) v ↔
              v ∈ nonadj (sub a b (rev r)) ⟨u, hux, huy⟩ := by
          rw [hS, mem_nonadj, mem_nonadj]
          constructor
          · rintro ⟨c1, c2, c3⟩
            exact ⟨fun h' => c1 h'.symm, c3, c2⟩
          · rintro ⟨c1, c2, c3⟩
            exact ⟨fun h' => c1 h'.symm, c3, c2⟩
        by_cases hw : (⟨u, hux, huy⟩ : {v : V // v ≠ a ∧ v ≠ b}) ∈
            secondNeighbors (sub a b (rev r)) v
        · simp only [hw, hiff.mp hw, ↓reduceIte]
        · have hw' : v ∉ nonadj (sub a b (rev r)) ⟨u, hux, huy⟩ :=
            fun h' => hw (hiff.mpr h')
          simp only [hw, hw', ↓reduceIte]
    rw [hL, hR] at hcoord
    have e1 := hfirstP (rev r) ⟨u, hux, huy⟩
    have e2 := hfirstP r ⟨u, hux, huy⟩
    have e3 := hPsub ⟨u, hux, huy⟩
    simp only at e1 e2 e3
    rw [← e1, ← e2, e3]
    linarith

/-- The dual weighting cannot vanish on the out-neighbours of `a`. -/
theorem side (h : TwoMark r t a b) (P : V → ℝ) (hP0 : ∀ v, 0 ≤ P v)
    (hP1 : ∑ v, P v = 1) (hPa : P a = 0)
    (hsupp : ∀ v, P v ≠ 0 → (firstNeighbors r v).card = t ∧
      ((r a v ∧ r v b) ∨ (r b v ∧ r v a)))
    (hone : ∀ u, u ≠ a → u ≠ b →
      P u + 2 * ∑ z ∈ firstNeighbors r u, P z +
        ∑ z ∈ firstNeighbors (rev r) u, P z = 1)
    (hα : ∑ z ∈ firstNeighbors r a, P z = 0) : False := by
  classical
  have hr := h.oriented
  have hOa0 : ∀ z ∈ firstNeighbors r a, P z = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun z _ => hP0 z)).mp hα
  have hsupp' : ∀ v, P v ≠ 0 → r b v ∧ r v a := by
    intro v hv
    rcases (hsupp v hv).2 with ⟨hav, _⟩ | hc
    · exact absurd (hOa0 v (mem_firstNeighbors.mpr hav)) hv
    · exact hc
  obtain ⟨c, hc⟩ : ∃ c, P c ≠ 0 := by
    by_contra hnone
    have hall : ∀ v ∈ (Finset.univ : Finset V), P v = 0 := by
      intro v _
      by_contra hv
      exact hnone ⟨v, hv⟩
    rw [Finset.sum_eq_zero hall] at hP1
    exact zero_ne_one hP1
  obtain ⟨hbc, hca⟩ := hsupp' c hc
  have hnab : ¬ r a b := fun hab => h.tri a b c hab hbc hca
  have hall : ∀ e, r a e → ∀ v, P v ≠ 0 → r v e := by
    intro e hae v hv
    have hea : e ≠ a := by
      intro heq
      rw [heq] at hae
      exact hr.loopless a hae
    have heb : e ≠ b := by
      intro heq
      rw [heq] at hae
      exact hnab hae
    have h1 := hone e hea heb
    have hPe : P e = 0 := hOa0 e (mem_firstNeighbors.mpr hae)
    have hOe : ∑ z ∈ firstNeighbors r e, P z = 0 := by
      apply Finset.sum_eq_zero
      intro z hz
      by_contra hPz
      exact h.tri a e z hae (mem_firstNeighbors.mp hz) (hsupp' z hPz).2
    have hIe : ∑ z ∈ firstNeighbors (rev r) e, P z = 1 := by
      rw [hPe, hOe] at h1
      linarith
    by_contra hve
    have hvI : v ∉ firstNeighbors (rev r) e := fun hc' =>
      hve ((mem_firstNeighbors (r := rev r)).mp hc')
    have h2 : ∑ z ∈ insert v (firstNeighbors (rev r) e), P z ≤ ∑ z, P z :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun z _ _ => hP0 z)
    rw [Finset.sum_insert hvI, hIe, hP1] at h2
    have h3 := lt_of_le_of_ne (hP0 v) (Ne.symm hv)
    linarith
  have hOsupp : ∀ v, P v ≠ 0 → firstNeighbors r v = insert a (firstNeighbors r a) := by
    intro v hv
    have hsub : insert a (firstNeighbors r a) ⊆ firstNeighbors r v := by
      intro z hz
      rcases Finset.mem_insert.mp hz with hza | hz
      · rw [hza]
        exact mem_firstNeighbors.mpr (hsupp' v hv).2
      · exact mem_firstNeighbors.mpr (hall z (mem_firstNeighbors.mp hz) v hv)
    have haO : a ∉ firstNeighbors r a := fun hc' => hr.loopless a (mem_firstNeighbors.mp hc')
    have hcard : (firstNeighbors r v).card ≤ (insert a (firstNeighbors r a)).card := by
      rw [Finset.card_insert_of_notMem haO]
      have h1 := (hsupp v hv).1
      have h2 := h.outa
      omega
    exact (Finset.eq_of_subset_of_card_le hsub hcard).symm
  have hca' : c ≠ a := by
    intro heq
    rw [heq] at hca
    exact hr.loopless a hca
  have hcb : c ≠ b := by
    intro heq
    rw [heq] at hbc
    exact hr.loopless b hbc
  have hOc : ∑ z ∈ firstNeighbors r c, P z = 0 := by
    rw [hOsupp c hc]
    have haO : a ∉ firstNeighbors r a := fun hc' => hr.loopless a (mem_firstNeighbors.mp hc')
    rw [Finset.sum_insert haO, hPa, hα]
    ring
  have hIc : ∑ z ∈ firstNeighbors (rev r) c, P z = 0 := by
    apply Finset.sum_eq_zero
    intro z hz
    by_contra hPz
    have hzc : r z c := (mem_firstNeighbors (r := rev r)).mp hz
    have hcO : c ∈ firstNeighbors r z := mem_firstNeighbors.mpr hzc
    rw [hOsupp z hPz] at hcO
    rcases Finset.mem_insert.mp hcO with hca2 | hcO
    · exact hca' hca2
    · exact hr.asymmetric (mem_firstNeighbors.mp hcO) hca
  have hPc : P c = 1 := by
    have h1 := hone c hca' hcb
    rw [hOc, hIc] at h1
    linarith
  obtain ⟨u, hu, hub⟩ := Finset.exists_mem_ne (s := firstNeighbors (rev r) c)
    (by have := h.inn c hca' hcb; have := h.two; omega) b
  have huc : r u c := (mem_firstNeighbors (r := rev r)).mp hu
  have hua : u ≠ a := by
    intro heq
    rw [heq] at huc
    exact hr.asymmetric huc hca
  have h1 := hone u hua hub
  have h2 : P c ≤ ∑ z ∈ firstNeighbors r u, P z :=
    Finset.single_le_sum (fun z _ => hP0 z) (mem_firstNeighbors.mpr huc)
  have h3 : 0 ≤ ∑ z ∈ firstNeighbors (rev r) u, P z :=
    Finset.sum_nonneg (fun z _ => hP0 z)
  have h4 := hP0 u
  linarith

/-- **The two marked vertices have a common out-neighbour.** -/
theorem common_head (h : TwoMark r t a b) : ∃ c, r a c ∧ r b c := by
  classical
  by_contra hnone
  have hcs : ∀ c, r a c → r b c → False := fun c hac hbc => hnone ⟨c, hac, hbc⟩
  have hcp := h.no_common_pred hcs
  have hr := h.oriented
  have hne : Nonempty V := ⟨a⟩
  obtain ⟨P, hP0, hP1, hPa, hPb, hsupp, hone⟩ := h.dual hcs hcp
  by_cases hα : ∑ z ∈ firstNeighbors r a, P z = 0
  · exact h.side P hP0 hP1 hPa hsupp hone hα
  by_cases hβ : ∑ z ∈ firstNeighbors r b, P z = 0
  · exact h.symm.side P hP0 hP1 hPb
      (fun v hv => ⟨(hsupp v hv).1, (hsupp v hv).2.symm⟩)
      (fun u hub hua => hone u hua hub) hβ
  have hαpos : 0 < ∑ z ∈ firstNeighbors r a, P z :=
    lt_of_le_of_ne (Finset.sum_nonneg (fun z _ => hP0 z)) (Ne.symm hα)
  have hβpos : 0 < ∑ z ∈ firstNeighbors r b, P z :=
    lt_of_le_of_ne (Finset.sum_nonneg (fun z _ => hP0 z)) (Ne.symm hβ)
  have hQ1 : ∀ u, u ≠ a → u ≠ b →
      ∑ z ∈ secondNeighbors r u, P z ≤ ∑ z ∈ firstNeighbors r u, P z := by
    intro u hua hub
    have h1 := sum_partition r hr P u
    have h2 : ∑ z ∈ secondNeighbors r u, P z ≤ ∑ z ∈ nonadj r u, P z :=
      Finset.sum_le_sum_of_subset_of_nonneg (second_subset_nonadj r h.tri u)
        (fun z _ _ => hP0 z)
    have h3 := hone u hua hub
    linarith
  have hSa0 : ∑ z ∈ secondNeighbors r a, P z = 0 := by
    apply Finset.sum_eq_zero
    intro z hz
    by_contra hPz
    obtain ⟨_, hnot, e, hae, hez⟩ := mem_secondNeighbors.mp hz
    rcases (hsupp z hPz).2 with ⟨haz, _⟩ | ⟨_, hza⟩
    · exact hnot haz
    · exact h.tri a e z hae hez hza
  have hSb0 : ∑ z ∈ secondNeighbors r b, P z = 0 := by
    apply Finset.sum_eq_zero
    intro z hz
    by_contra hPz
    obtain ⟨_, hnot, e, hbe, hez⟩ := mem_secondNeighbors.mp hz
    rcases (hsupp z hPz).2 with ⟨_, hzb⟩ | ⟨hbz, _⟩
    · exact h.tri b e z hbe hez hzb
    · exact hnot hbz
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = ((Fintype.card V : ℝ) + 1) /
      (∑ z ∈ firstNeighbors r a, P z) + ((Fintype.card V : ℝ) + 1) /
      (∑ z ∈ firstNeighbors r b, P z) := ⟨_, rfl⟩
  have hNpos : (0 : ℝ) < (Fintype.card V : ℝ) + 1 := by positivity
  have hLpos : 0 < L := by
    rw [hL]
    exact add_pos (div_pos hNpos hαpos) (div_pos hNpos hβpos)
  have hLα : (Fintype.card V : ℝ) + 1 ≤ L * ∑ z ∈ firstNeighbors r a, P z := by
    rw [hL, add_mul, div_mul_cancel₀ _ hα]
    have : 0 ≤ ((Fintype.card V : ℝ) + 1) / (∑ z ∈ firstNeighbors r b, P z) *
        ∑ z ∈ firstNeighbors r a, P z :=
      mul_nonneg (div_nonneg hNpos.le hβpos.le) hαpos.le
    linarith
  have hLβ : (Fintype.card V : ℝ) + 1 ≤ L * ∑ z ∈ firstNeighbors r b, P z := by
    rw [hL, add_mul, div_mul_cancel₀ _ hβ]
    have : 0 ≤ ((Fintype.card V : ℝ) + 1) / (∑ z ∈ firstNeighbors r a, P z) *
        ∑ z ∈ firstNeighbors r b, P z :=
      mul_nonneg (div_nonneg hNpos.le hαpos.le) hβpos.le
    linarith
  have hsumw : ∀ A : Finset V, ∑ z ∈ A, (1 + L * P z) =
      (A.card : ℝ) + L * ∑ z ∈ A, P z := by
    intro A
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, Finset.mul_sum]
  have hcardle : ∀ A : Finset V, (A.card : ℝ) ≤ Fintype.card V := by
    intro A
    exact_mod_cast Finset.card_le_univ A
  obtain ⟨v, hv⟩ := weighted_good_real r hr (fun z => 1 + L * P z)
    (fun z => by have := mul_nonneg hLpos.le (hP0 z); linarith)
  rw [hsumw, hsumw] at hv
  by_cases hva : v = a
  · rw [hva, hSa0] at hv
    have h1 := hcardle (secondNeighbors r a)
    have h2 : (0 : ℝ) ≤ ((firstNeighbors r a).card : ℝ) := Nat.cast_nonneg _
    linarith
  · by_cases hvb : v = b
    · rw [hvb, hSb0] at hv
      have h1 := hcardle (secondNeighbors r b)
      have h2 : (0 : ℝ) ≤ ((firstNeighbors r b).card : ℝ) := Nat.cast_nonneg _
      linarith
    · have h1 := mul_le_mul_of_nonneg_left (hQ1 v hva hvb) hLpos.le
      have h2 : ((secondNeighbors r v).card : ℝ) + 1 ≤ ((firstNeighbors r v).card : ℝ) := by
        exact_mod_cast h.ord_bad v hva hvb
      linarith

/-- Core of the surplus bound: `a` cannot have surplus at most one while `b` has none. -/
theorem surplus_core [Nonempty V] (h : TwoMark r t a b)
    (ha : (secondNeighbors r a).card ≤ (firstNeighbors r a).card + 1)
    (hb : (secondNeighbors r b).card ≤ (firstNeighbors r b).card) : False := by
  classical
  have hr := h.oriented
  obtain ⟨c, hac, hbc⟩ := h.common_head
  have hcO : c ∈ firstNeighbors r a := mem_firstNeighbors.mpr hac
  have hmpos : 0 < (firstNeighbors r a).card := Finset.card_pos.mpr ⟨c, hcO⟩
  have hmR : (0 : ℝ) < ((firstNeighbors r a).card : ℝ) := by exact_mod_cast hmpos
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = 1 / (2 * ((firstNeighbors r a).card : ℝ)) := ⟨_, rfl⟩
  have hηpos : 0 < η := by
    rw [hη]
    positivity
  have hη2 : ((firstNeighbors r a).card : ℝ) * η = 1 / 2 := by
    rw [hη]
    field_simp
  have hexp : (((firstNeighbors r a).card : ℝ) - 1) * η =
      ((firstNeighbors r a).card : ℝ) * η - η := by ring
  let δ : V → ℝ := fun z =>
    if z = c then 1 - (((firstNeighbors r a).card : ℝ) - 1) * η
    else if z ∈ firstNeighbors r a then η else 0
  have hδc : δ c = 1 - (((firstNeighbors r a).card : ℝ) - 1) * η := by
    simp only [δ, if_true]
  have hδO : ∀ z ∈ firstNeighbors r a, z ≠ c → δ z = η := by
    intro z hz hzc
    simp only [δ, hzc, hz, if_false, if_true]
  have hδout : ∀ z, z ∉ firstNeighbors r a → δ z = 0 := by
    intro z hz
    have hzc : z ≠ c := by
      intro heq
      rw [heq] at hz
      exact hz hcO
    simp only [δ, hzc, hz, if_false]
  have hδnn : ∀ z, 0 ≤ δ z := by
    intro z
    by_cases hzc : z = c
    · rw [hzc, hδc]
      linarith
    · by_cases hz : z ∈ firstNeighbors r a
      · rw [hδO z hz hzc]
        exact hηpos.le
      · rw [hδout z hz]
  have hδpos : ∀ z ∈ firstNeighbors r a, 0 < δ z := by
    intro z hz
    by_cases hzc : z = c
    · rw [hzc, hδc]
      linarith
    · rw [hδO z hz hzc]
      exact hηpos
  have hδsum : ∑ z ∈ firstNeighbors r a, δ z = 1 := by
    have h1 := Finset.add_sum_erase (firstNeighbors r a) δ hcO
    have h2 : ∑ z ∈ (firstNeighbors r a).erase c, δ z =
        (((firstNeighbors r a).card : ℝ) - 1) * η := by
      have hc : ∀ z ∈ (firstNeighbors r a).erase c, δ z = η := fun z hz =>
        hδO z (Finset.mem_erase.mp hz).2 (Finset.mem_erase.mp hz).1
      rw [Finset.sum_congr rfl hc, Finset.sum_const, nsmul_eq_mul]
      have hcard := Finset.card_erase_add_one hcO
      have hcast : (((firstNeighbors r a).erase c).card : ℝ) + 1 =
          ((firstNeighbors r a).card : ℝ) := by exact_mod_cast hcard
      have hcast' : (((firstNeighbors r a).erase c).card : ℝ) =
          ((firstNeighbors r a).card : ℝ) - 1 := by linarith
      rw [hcast']
    rw [hδc] at h1
    linarith
  have hle1 : ∀ A : Finset V, ∑ z ∈ A, δ z ≤ 1 := by
    intro A
    have h1 := sum_le_of_support (A := A) (B := firstNeighbors r a) δ hδnn
      (fun z _ hz => hδout z hz)
    linarith
  have hsumw : ∀ A : Finset V, ∑ z ∈ A, (1 + δ z) = (A.card : ℝ) + ∑ z ∈ A, δ z := by
    intro A
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
  have haR : ((secondNeighbors r a).card : ℝ) ≤ ((firstNeighbors r a).card : ℝ) + 1 := by
    exact_mod_cast ha
  have hbR : ((secondNeighbors r b).card : ℝ) ≤ ((firstNeighbors r b).card : ℝ) := by
    exact_mod_cast hb
  have cOrd : ∀ v, v ≠ a → v ≠ b →
      ((secondNeighbors r v).card : ℝ) + 1 ≤ ((firstNeighbors r v).card : ℝ) := by
    intro v hva hvb
    exact_mod_cast h.ord_bad v hva hvb
  have hSa0 : ∑ z ∈ secondNeighbors r a, δ z = 0 :=
    Finset.sum_eq_zero (fun z hz => hδout z (fun hzO =>
      Finset.disjoint_left.mp (first_second_disjoint r a) hzO hz))
  have hstrictb : ∑ z ∈ secondNeighbors r b, (1 + δ z) <
      ∑ z ∈ firstNeighbors r b, (1 + δ z) := by
    rw [hsumw, hsumw]
    have hcS : c ∉ secondNeighbors r b := fun hc =>
      Finset.disjoint_left.mp (first_second_disjoint r b) (mem_firstNeighbors.mpr hbc) hc
    have h1 := sum_add_le_of_support (A := secondNeighbors r b) (B := firstNeighbors r a)
      δ hδnn (fun z _ hz => hδout z hz) c hcO hcS
    have h2 : δ c ≤ ∑ z ∈ firstNeighbors r b, δ z :=
      Finset.single_le_sum (fun z _ => hδnn z) (mem_firstNeighbors.mpr hbc)
    rw [hδc] at h1 h2
    linarith
  have hno : ∀ v, ∑ z ∈ secondNeighbors r v, (1 + δ z) ≤
      ∑ z ∈ firstNeighbors r v, (1 + δ z) := by
    intro v
    by_cases hva : v = a
    · rw [hva, hsumw, hsumw, hSa0, hδsum]
      linarith
    · by_cases hvb : v = b
      · rw [hvb]
        exact hstrictb.le
      · rw [hsumw, hsumw]
        have c1 := cOrd v hva hvb
        have h1 := hle1 (secondNeighbors r v)
        have h2 : 0 ≤ ∑ z ∈ firstNeighbors r v, δ z :=
          Finset.sum_nonneg (fun z _ => hδnn z)
        linarith
  obtain ⟨T, hTne, hTtied, hTpred⟩ := tied_cycle r hr h.sinkless (fun z => 1 + δ z)
    (fun z => by have := hδnn z; linarith) hno
  have hspecial : ∀ v ∈ T, v ≠ a → nonadj r v = firstNeighbors r a := by
    intro v hvT hva
    have htie := hTtied v hvT
    have hvb : v ≠ b := by
      intro hvb
      rw [hvb] at htie
      linarith
    rw [hsumw, hsumw] at htie
    have c1 := cOrd v hva hvb
    have hSle := hle1 (secondNeighbors r v)
    have hOnn : 0 ≤ ∑ z ∈ firstNeighbors r v, δ z :=
      Finset.sum_nonneg (fun z _ => hδnn z)
    have hS1 : ∑ z ∈ secondNeighbors r v, δ z = 1 := by linarith
    have hsub : firstNeighbors r a ⊆ secondNeighbors r v := by
      intro z hz
      by_contra hzS
      have h1 := sum_add_le_of_support (A := secondNeighbors r v)
        (B := firstNeighbors r a) δ hδnn (fun z _ hz => hδout z hz) z hz hzS
      have h2 := hδpos z hz
      linarith
    have hsub' : firstNeighbors r a ⊆ nonadj r v :=
      hsub.trans (second_subset_nonadj r h.tri v)
    have hcard : (nonadj r v).card ≤ (firstNeighbors r a).card := by
      have h1 := h.nonadj_ord v hva hvb
      have h2 := h.outa
      omega
    exact (Finset.eq_of_subset_of_card_le hsub' hcard).symm
  have hT1special : ∀ v ∈ T.erase a, nonadj r v = firstNeighbors r a := fun v hv =>
    hspecial v (Finset.mem_erase.mp hv).2 (Finset.mem_erase.mp hv).1
  have hnotO : ∀ v ∈ T.erase a, v ∉ firstNeighbors r a := by
    intro v hv hvO
    rw [← hT1special v hv] at hvO
    exact (mem_nonadj.mp hvO).1 rfl
  have hT1pred : ∀ v ∈ T.erase a, ∃ u ∈ T.erase a, r u v := by
    intro v hv
    obtain ⟨u, hu, huv⟩ := hTpred v (Finset.mem_erase.mp hv).2
    refine ⟨u, Finset.mem_erase.mpr ⟨?_, hu⟩, huv⟩
    intro hua
    rw [hua] at huv
    exact hnotO v hv (mem_firstNeighbors.mpr huv)
  have hT1ne : (T.erase a).Nonempty := by
    obtain ⟨v, hv⟩ := hTne
    by_cases hva : v = a
    · obtain ⟨u, hu, hua⟩ := hTpred v hv
      rw [hva] at hua
      refine ⟨u, Finset.mem_erase.mpr ⟨?_, hu⟩⟩
      intro heq
      rw [heq] at hua
      exact hr.loopless a hua
    · exact ⟨v, Finset.mem_erase.mpr ⟨hva, hv⟩⟩
  apply no_tournament_sourceless r hr h.tri (T.erase a) hT1ne ?_ hT1pred
  intro u hu v hv huv
  by_contra hnon
  have hn1 : ¬ r u v := fun h' => hnon (Or.inl h')
  have hn2 : ¬ r v u := fun h' => hnon (Or.inr h')
  have hvM : v ∈ nonadj r u := mem_nonadj.mpr ⟨fun h' => huv h'.symm, hn1, hn2⟩
  rw [hT1special u hu] at hvM
  exact hnotO v hv hvM

/-- **The two marked vertices carry at least two units of surplus.** -/
theorem surplus (h : TwoMark r t a b) :
    (firstNeighbors r a).card + (firstNeighbors r b).card + 2 ≤
      (secondNeighbors r a).card + (secondNeighbors r b).card := by
  classical
  have hne : Nonempty V := ⟨a⟩
  by_contra hlt
  obtain ⟨u, v, huv, hu, hv⟩ := exists_two_goodVertices r h.oriented h.sinkless
  have hgood : ∀ w, GoodVertex r w → w = a ∨ w = b := by
    intro w hw
    by_contra hc
    have hwa : w ≠ a := fun heq => hc (Or.inl heq)
    have hwb : w ≠ b := fun heq => hc (Or.inr heq)
    have := h.ord_bad w hwa hwb
    unfold GoodVertex at hw
    omega
  have hga : GoodVertex r a := by
    rcases hgood u hu with hua | hub
    · rw [← hua]
      exact hu
    · rcases hgood v hv with hva | hvb
      · rw [← hva]
        exact hv
      · exact absurd (hub.trans hvb.symm) huv
  have hgb : GoodVertex r b := by
    rcases hgood u hu with hua | hub
    · rcases hgood v hv with hva | hvb
      · exact absurd (hua.trans hva.symm) huv
      · rw [← hvb]
        exact hv
    · rw [← hub]
      exact hu
  unfold GoodVertex at hga hgb
  by_cases hb0 : (secondNeighbors r b).card ≤ (firstNeighbors r b).card
  · exact h.surplus_core (by omega) hb0
  · exact h.symm.surplus_core (by omega) (by omega)

end TwoMark

omit [DecidableEq V] in
theorem pair_le_sum (f : V → ℕ) (u v : V) (huv : u ≠ v) : f u + f v ≤ ∑ z, f z := by
  classical
  have h1 : ∑ z ∈ ({u, v} : Finset V), f z ≤ ∑ z, f z :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  rw [Finset.sum_pair huv] at h1
  exact h1

/-- **Whole-bank overload.** -/
theorem overload {r : V → V → Prop} {t : ℕ} {x : V} (hr : IsOriented r)
    (htri : ∀ u v w, r u v → r v w → ¬ r w u) (hcard : Fintype.card V ≤ 3 * t)
    (ht : 2 ≤ t) (houtx : t ≤ (firstNeighbors r x).card + 1)
    (hout : ∀ v, v ≠ x → t ≤ (firstNeighbors r v).card) :
    2 ≤ ∑ v, (t - (firstNeighbors (rev r) v).card) := by
  classical
  have hne : Nonempty V := ⟨x⟩
  by_contra hlt
  have hsum : ∑ v, (t - (firstNeighbors (rev r) v).card) ≤ 1 := by omega
  have hone : ∀ v, t ≤ (firstNeighbors (rev r) v).card + 1 := by
    intro v
    have := Finset.single_le_sum (f := fun v => t - (firstNeighbors (rev r) v).card)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ v)
    omega
  have hunique : ∀ u v, u ≠ v → (firstNeighbors (rev r) u).card < t →
      (firstNeighbors (rev r) v).card < t → False := by
    intro u v huv hu hv
    have := pair_le_sum (fun v => t - (firstNeighbors (rev r) v).card) u v huv
    omega
  have hsl : ∀ v, ∃ z, r v z := by
    intro v
    have hpos : 0 < (firstNeighbors r v).card := by
      by_cases hv : v = x
      · rw [hv]
        omega
      · have := hout v hv
        omega
    obtain ⟨z, hz⟩ := Finset.card_pos.mp hpos
    exact ⟨z, mem_firstNeighbors.mp hz⟩
  obtain ⟨u, v, huv, hu, hv⟩ := exists_two_goodVertices r hr hsl
  -- a good vertex other than `x` is short of in-arcs, on exactly `3t` vertices
  have key : ∀ w, w ≠ x → GoodVertex r w →
      (firstNeighbors (rev r) w).card < t ∧ Fintype.card V = 3 * t ∧
        t ≤ (firstNeighbors r w).card := by
    intro w hwx hgood
    unfold GoodVertex at hgood
    have h1 := card_partition r hr w
    have h2 := Finset.card_le_card (second_subset_nonadj r htri w)
    have h3 := hout w hwx
    have h4 := hone w
    refine ⟨by omega, by omega, h3⟩
  -- the pair (x, y)
  have main : ∀ y, y ≠ x → GoodVertex r y → GoodVertex r x → False := by
    intro y hyx hgy hgx
    obtain ⟨hyin, hc, hyout⟩ := key y hyx hgy
    have hmark : TwoMark r t x y := by
      refine ⟨hr, htri, hc, ht, fun h => hyx h.symm, ?_, ?_, houtx, by omega, Or.inr hyout⟩
      · intro w hwx _
        exact hout w hwx
      · intro w _ hwy
        by_contra hw
        exact hunique w y hwy (by omega) hyin
    have hs := hmark.surplus
    have hx1 := card_partition r hr x
    have hx2 := Finset.card_le_card (second_subset_nonadj r htri x)
    have hy1 := card_partition r hr y
    have hy2 := Finset.card_le_card (second_subset_nonadj r htri y)
    have hxin : t ≤ (firstNeighbors (rev r) x).card := by
      by_contra hxlt
      exact hunique x y (fun h => hyx h.symm) (by omega) hyin
    have hyin' := hone y
    omega
  by_cases hux : u = x
  · rw [hux] at hu huv
    exact main v (fun h => huv h.symm) hv hu
  · by_cases hvx : v = x
    · rw [hvx] at hv
      exact main u hux hu hv
    · exact hunique u v huv (key u hux hu).1 (key v hvx hv).1

/-- **The parent needs four units of incoming deficit.** -/
theorem parent_deficit {r : V → V → Prop} {t : ℕ} [Nonempty V] (hr : IsOriented r)
    (htri : ∀ u v w, r u v → r v w → ¬ r w u) (hcard : Fintype.card V ≤ 3 * t)
    (ht : 2 ≤ t) (hout : ∀ v, t ≤ (firstNeighbors r v).card) :
    4 ≤ ∑ v, (t - (firstNeighbors (rev r) v).card) := by
  classical
  by_contra hlt
  have hsum : ∑ v, (t - (firstNeighbors (rev r) v).card) ≤ 3 := by omega
  have hsl : ∀ v, ∃ z, r v z := by
    intro v
    have hpos : 0 < (firstNeighbors r v).card := by
      have := hout v
      omega
    obtain ⟨z, hz⟩ := Finset.card_pos.mp hpos
    exact ⟨z, mem_firstNeighbors.mp hz⟩
  -- the surplus of a vertex is below its incoming deficit
  have hscore : ∀ w, (secondNeighbors r w).card + (firstNeighbors (rev r) w).card + 1 +
      (firstNeighbors r w).card ≤ 3 * t := by
    intro w
    have h1 := card_partition r hr w
    have h2 := Finset.card_le_card (second_subset_nonadj r htri w)
    omega
  have hgooddef : ∀ w, GoodVertex r w → (firstNeighbors (rev r) w).card < t := by
    intro w hw
    unfold GoodVertex at hw
    have h1 := hscore w
    have h2 := hout w
    omega
  obtain ⟨u, v, huv, hu, hv⟩ := exists_two_goodVertices r hr hsl
  have hud := hgooddef u hu
  have hvd := hgooddef v hv
  have hpair := pair_le_sum (fun v => t - (firstNeighbors (rev r) v).card) u v huv
  by_cases hthird : ∃ w, w ≠ u ∧ w ≠ v ∧ (firstNeighbors (rev r) w).card < t
  · -- three deficient vertices: no strict vertex, and the ties sit on at most three vertices
    obtain ⟨w, hwu, hwv, hwd⟩ := hthird
    let D : Finset V := Finset.univ.filter (fun z => (firstNeighbors (rev r) z).card < t)
    have hDsum : ∑ z ∈ D, (t - (firstNeighbors (rev r) z).card) ≤ 3 :=
      (Finset.sum_le_sum_of_subset (Finset.subset_univ D)).trans hsum
    have hDone : ∀ z ∈ D, 1 ≤ t - (firstNeighbors (rev r) z).card := by
      intro z hz
      have := (Finset.mem_filter.mp hz).2
      omega
    have hDcard : D.card ≤ 3 := by
      have h1 := Finset.card_nsmul_le_sum D (fun z => t - (firstNeighbors (rev r) z).card) 1
        hDone
      simp only [smul_eq_mul, mul_one] at h1
      omega
    have hD3 : 3 ≤ D.card := by
      have hsub : ({u, v, w} : Finset V) ⊆ D := by
        intro z hz
        rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hz
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ z, ?_⟩
        rcases hz with hz | hz | hz
        · rw [hz]
          exact hud
        · rw [hz]
          exact hvd
        · rw [hz]
          exact hwd
      have c2 : ({v, w} : Finset V).card = 2 := Finset.card_pair (fun h => hwv h.symm)
      have c3 : ({u, v, w} : Finset V).card = 3 := by
        rw [Finset.card_insert_of_notMem (by
          rw [Finset.mem_insert, Finset.mem_singleton]
          exact fun h => h.elim huv (fun h => hwu h.symm)), c2]
      have := Finset.card_le_card hsub
      omega
    have hDeq : ∀ z ∈ D, t - (firstNeighbors (rev r) z).card = 1 := by
      intro z hz
      by_contra hne1
      have hz2 : 2 ≤ t - (firstNeighbors (rev r) z).card := by
        have := hDone z hz
        omega
      have h1 := Finset.add_sum_erase D (fun z => t - (firstNeighbors (rev r) z).card) hz
      have h2 := Finset.card_nsmul_le_sum (D.erase z)
        (fun z => t - (firstNeighbors (rev r) z).card) 1
        (fun y hy => hDone y (Finset.mem_erase.mp hy).2)
      simp only [smul_eq_mul, mul_one] at h2
      have h3 := Finset.card_erase_add_one hz
      omega
    have hnostrict : ∀ z, (secondNeighbors r z).card ≤ (firstNeighbors r z).card := by
      intro z
      have h1 := hscore z
      have h2 := hout z
      by_cases hz : z ∈ D
      · have := hDeq z hz
        omega
      · have hzd : ¬ (firstNeighbors (rev r) z).card < t := fun hc =>
          hz (Finset.mem_filter.mpr ⟨Finset.mem_univ z, hc⟩)
        omega
    obtain ⟨T, hTne, hTtied, hTpred⟩ := tied_cycle r hr hsl (fun _ => (1 : ℝ))
      (fun _ => one_pos) (by
        intro z
        simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
        exact_mod_cast hnostrict z)
    have hTD : T ⊆ D := by
      intro z hz
      have htie := hTtied z hz
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at htie
      have htieN : (secondNeighbors r z).card = (firstNeighbors r z).card := by
        exact_mod_cast htie
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ z, ?_⟩
      apply hgooddef z
      unfold GoodVertex
      omega
    have h4 := four_le_of_pred_closed r hr htri T hTne hTpred
    have h5 := Finset.card_le_card hTD
    omega
  · -- exactly two deficient vertices
    have hothers : ∀ w, w ≠ u → w ≠ v → t ≤ (firstNeighbors (rev r) w).card := by
      intro w hwu hwv
      by_contra hw
      exact hthird ⟨w, hwu, hwv, by omega⟩
    have hsu := hscore u
    have hsv := hscore v
    unfold GoodVertex at hu hv
    have hou := hout u
    have hov := hout v
    have hc : Fintype.card V = 3 * t := by
      have h1 := card_partition r hr u
      have h2 := Finset.card_le_card (second_subset_nonadj r htri u)
      by_contra hne3
      have hlt3 : Fintype.card V + 1 ≤ 3 * t := by omega
      -- then both good vertices have deficit at least two
      have h3 := card_partition r hr v
      have h4 := Finset.card_le_card (second_subset_nonadj r htri v)
      omega
    have hmark : TwoMark r t u v :=
      ⟨hr, htri, hc, ht, huv, fun w _ _ => hout w, hothers, by omega, by omega, Or.inl hou⟩
    have hs := hmark.surplus
    omega

end LeanCH.BR.TwoSeymour

#print axioms LeanCH.BR.TwoSeymour.TwoMark.common_head
#print axioms LeanCH.BR.TwoSeymour.TwoMark.surplus
#print axioms LeanCH.BR.TwoSeymour.overload
#print axioms LeanCH.BR.TwoSeymour.parent_deficit
