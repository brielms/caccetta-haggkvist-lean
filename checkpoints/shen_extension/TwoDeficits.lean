import checkpoints.shen_extension.TwoDeficitBasics

/-!
Two deficits at different vertices.

An oriented graph without directed triangles on `3t` vertices (`t ≥ 2`) cannot have
out-degree `t - 1` at `x`, in-degree `t - 1` at `y ≠ x`, and all other in- and out-degrees
equal to `t`.

Proof (relayed paper argument, 27 November 2026):
1. `x` and `y` have no common successor (`no_common_succ`), and by reversal no common
   predecessor: put one unit of weight on the successors of `x`, mostly on the common one;
   the tied vertices are then `x` and a set of pairwise adjacent vertices that `x` does
   not point to, which has no cycle, against `tied_cycle`.
2. After deleting `x` and `y`, the reversed graph has no strict vertex at unit weights;
   `tied_dual` gives a probability weighting `P` with
   `P u + 2 P(O(u)) + P(I(u)) = 1` at every remaining `u`, supported on vertices between
   `x` and `y` (`dual`).
3. With weights `1 + L P` only `y` can tie unless `P` vanishes on the successors of `x`;
   then every supported vertex points to `x` and to all successors of `x`, so `P` is a
   point mass, and an in-neighbour of that point violates the identity (`final`).
-/

namespace LeanCH.BR.TwoSeymour

open OAI.SeymourSecondNeighborhood
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

structure TwoDef (r : V → V → Prop) (t : ℕ) (x y : V) : Prop where
  oriented : IsOriented r
  tri : ∀ a b c, r a b → r b c → ¬ r c a
  card : Fintype.card V = 3 * t
  two : 2 ≤ t
  ne : x ≠ y
  outx : (firstNeighbors r x).card + 1 = t
  out : ∀ v, v ≠ x → (firstNeighbors r v).card = t
  iny : (firstNeighbors (rev r) y).card + 1 = t
  inn : ∀ v, v ≠ y → (firstNeighbors (rev r) v).card = t

namespace TwoDef

variable {r : V → V → Prop} {t : ℕ} {x y : V}

theorem flip (h : TwoDef r t x y) : TwoDef (rev r) t y x where
  oriented := ⟨fun v => h.oriented.loopless v,
    fun hab hba => h.oriented.asymmetric hab hba⟩
  tri := fun a b c hab hbc hca => h.tri c b a hbc hab hca
  card := h.card
  two := h.two
  ne := h.ne.symm
  outx := h.iny
  out := h.inn
  iny := h.outx
  inn := h.out

theorem nonadj_x (h : TwoDef r t x y) : (nonadj r x).card = t := by
  have h1 := card_partition r h.oriented x
  have h2 := h.card
  have h3 := h.outx
  have h4 := h.inn x h.ne
  omega

theorem nonadj_y (h : TwoDef r t x y) : (nonadj r y).card = t := by
  have h1 := card_partition r h.oriented y
  have h2 := h.card
  have h3 := h.out y h.ne.symm
  have h4 := h.iny
  omega

theorem nonadj_ord (h : TwoDef r t x y) (v : V) (hx : v ≠ x) (hy : v ≠ y) :
    (nonadj r v).card + 1 = t := by
  have h1 := card_partition r h.oriented v
  have h2 := h.card
  have h3 := h.out v hx
  have h4 := h.inn v hy
  omega

theorem second_le (h : TwoDef r t x y) (v : V) :
    (secondNeighbors r v).card ≤ (nonadj r v).card :=
  Finset.card_le_card (second_subset_nonadj r h.tri v)

theorem sinkless (h : TwoDef r t x y) : ∀ v, ∃ z, r v z := by
  intro v
  have hpos : 0 < (firstNeighbors r v).card := by
    by_cases hv : v = x
    · have h1 := h.outx
      have h2 := h.two
      rw [hv]
      omega
    · have h1 := h.out v hv
      have h2 := h.two
      omega
  obtain ⟨z, hz⟩ := Finset.card_pos.mp hpos
  exact ⟨z, mem_firstNeighbors.mp hz⟩

/-- Step 1: the two exceptional vertices have no common successor. -/
theorem no_common_succ [Nonempty V] (h : TwoDef r t x y) (c : V) (hxc : r x c)
    (hyc : r y c) : False := by
  classical
  have hr := h.oriented
  have hτ : (2 : ℝ) ≤ (t : ℝ) := by exact_mod_cast h.two
  have hcO : c ∈ firstNeighbors r x := mem_firstNeighbors.mpr hxc
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = 1 / (2 * (t : ℝ)) := ⟨_, rfl⟩
  have hηpos : 0 < η := by
    rw [hη]
    positivity
  have hη2 : (t : ℝ) * η = 1 / 2 := by
    rw [hη]
    field_simp
  have hexp : ((t : ℝ) - 2) * η = (t : ℝ) * η - 2 * η := by ring
  let δ : V → ℝ := fun z =>
    if z = c then 1 - ((t : ℝ) - 2) * η else if z ∈ firstNeighbors r x then η else 0
  have hδc : δ c = 1 - ((t : ℝ) - 2) * η := by
    simp only [δ, if_true]
  have hδO : ∀ z ∈ firstNeighbors r x, z ≠ c → δ z = η := by
    intro z hz hzc
    simp only [δ, hzc, hz, if_false, if_true]
  have hδout : ∀ z, z ∉ firstNeighbors r x → δ z = 0 := by
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
    · by_cases hz : z ∈ firstNeighbors r x
      · rw [hδO z hz hzc]
        exact hηpos.le
      · rw [hδout z hz]
  have hδpos : ∀ z ∈ firstNeighbors r x, 0 < δ z := by
    intro z hz
    by_cases hzc : z = c
    · rw [hzc, hδc]
      linarith
    · rw [hδO z hz hzc]
      exact hηpos
  have hδsum : ∑ z ∈ firstNeighbors r x, δ z = 1 := by
    have h1 := Finset.add_sum_erase (firstNeighbors r x) δ hcO
    have h2 : ∑ z ∈ (firstNeighbors r x).erase c, δ z = ((t : ℝ) - 2) * η := by
      have hc : ∀ z ∈ (firstNeighbors r x).erase c, δ z = η := fun z hz =>
        hδO z (Finset.mem_erase.mp hz).2 (Finset.mem_erase.mp hz).1
      rw [Finset.sum_congr rfl hc, Finset.sum_const, nsmul_eq_mul]
      have hcard := Finset.card_erase_add_one hcO
      have hox := h.outx
      have hnat : ((firstNeighbors r x).erase c).card + 2 = t := by omega
      have hcast : (((firstNeighbors r x).erase c).card : ℝ) + 2 = (t : ℝ) := by
        exact_mod_cast hnat
      have hcast' : (((firstNeighbors r x).erase c).card : ℝ) = (t : ℝ) - 2 := by linarith
      rw [hcast']
    rw [hδc] at h1
    linarith
  have hle1 : ∀ A : Finset V, ∑ z ∈ A, δ z ≤ 1 := by
    intro A
    have h1 := sum_le_of_support (A := A) (B := firstNeighbors r x) δ hδnn
      (fun z _ hz => hδout z hz)
    linarith
  have hsumw : ∀ A : Finset V, ∑ z ∈ A, (1 + δ z) = (A.card : ℝ) + ∑ z ∈ A, δ z := by
    intro A
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
  have cOx : ((firstNeighbors r x).card : ℝ) + 1 = t := by exact_mod_cast h.outx
  have cSx : ((secondNeighbors r x).card : ℝ) ≤ t := by
    have h1 := h.second_le x
    have h2 := h.nonadj_x
    exact_mod_cast (by omega : (secondNeighbors r x).card ≤ t)
  have cSy : ((secondNeighbors r y).card : ℝ) ≤ t := by
    have h1 := h.second_le y
    have h2 := h.nonadj_y
    exact_mod_cast (by omega : (secondNeighbors r y).card ≤ t)
  have cOy : ((firstNeighbors r y).card : ℝ) = t := by exact_mod_cast h.out y h.ne.symm
  have cOrd : ∀ v, v ≠ x → v ≠ y →
      ((secondNeighbors r v).card : ℝ) + 1 ≤ t ∧ ((firstNeighbors r v).card : ℝ) = t := by
    intro v hvx hvy
    have h1 := h.second_le v
    have h2 := h.nonadj_ord v hvx hvy
    refine ⟨?_, by exact_mod_cast h.out v hvx⟩
    exact_mod_cast (by omega : (secondNeighbors r v).card + 1 ≤ t)
  have hSx0 : ∑ z ∈ secondNeighbors r x, δ z = 0 :=
    Finset.sum_eq_zero (fun z hz => hδout z (fun hzO =>
      Finset.disjoint_left.mp (first_second_disjoint r x) hzO hz))
  have hstricty : ∑ z ∈ secondNeighbors r y, (1 + δ z) <
      ∑ z ∈ firstNeighbors r y, (1 + δ z) := by
    rw [hsumw, hsumw]
    have hcS : c ∉ secondNeighbors r y := fun hc =>
      Finset.disjoint_left.mp (first_second_disjoint r y) (mem_firstNeighbors.mpr hyc) hc
    have h1 := sum_add_le_of_support (A := secondNeighbors r y) (B := firstNeighbors r x)
      δ hδnn (fun z _ hz => hδout z hz) c hcO hcS
    have h2 : δ c ≤ ∑ z ∈ firstNeighbors r y, δ z :=
      Finset.single_le_sum (fun z _ => hδnn z) (mem_firstNeighbors.mpr hyc)
    rw [hδc] at h1 h2
    linarith
  have hno : ∀ v, ∑ z ∈ secondNeighbors r v, (1 + δ z) ≤
      ∑ z ∈ firstNeighbors r v, (1 + δ z) := by
    intro v
    by_cases hvx : v = x
    · rw [hvx, hsumw, hsumw, hSx0, hδsum]
      linarith
    · by_cases hvy : v = y
      · rw [hvy]
        exact hstricty.le
      · rw [hsumw, hsumw]
        obtain ⟨c1, c2⟩ := cOrd v hvx hvy
        have h1 := hle1 (secondNeighbors r v)
        have h2 : 0 ≤ ∑ z ∈ firstNeighbors r v, δ z :=
          Finset.sum_nonneg (fun z _ => hδnn z)
        linarith
  obtain ⟨T, hTne, hTtied, hTpred⟩ := tied_cycle r hr h.sinkless (fun z => 1 + δ z)
    (fun z => by have := hδnn z; linarith) hno
  have hspecial : ∀ v ∈ T, v ≠ x → nonadj r v = firstNeighbors r x := by
    intro v hvT hvx
    have htie := hTtied v hvT
    have hvy : v ≠ y := by
      intro hvy
      rw [hvy] at htie
      linarith
    rw [hsumw, hsumw] at htie
    obtain ⟨c1, c2⟩ := cOrd v hvx hvy
    have hSle := hle1 (secondNeighbors r v)
    have hOnn : 0 ≤ ∑ z ∈ firstNeighbors r v, δ z :=
      Finset.sum_nonneg (fun z _ => hδnn z)
    have hS1 : ∑ z ∈ secondNeighbors r v, δ z = 1 := by linarith
    have hScard : ((secondNeighbors r v).card : ℝ) + 1 = t := by linarith
    have hsub : firstNeighbors r x ⊆ secondNeighbors r v := by
      intro z hz
      by_contra hzS
      have h1 := sum_add_le_of_support (A := secondNeighbors r v)
        (B := firstNeighbors r x) δ hδnn (fun z _ hz => hδout z hz) z hz hzS
      have h2 := hδpos z hz
      linarith
    have hScardN : (secondNeighbors r v).card + 1 = t := by exact_mod_cast hScard
    have hSeq : firstNeighbors r x = secondNeighbors r v :=
      Finset.eq_of_subset_of_card_le hsub (by have := h.outx; omega)
    have hMeq : secondNeighbors r v = nonadj r v :=
      Finset.eq_of_subset_of_card_le (second_subset_nonadj r h.tri v)
        (by have := h.nonadj_ord v hvx hvy; omega)
    rw [← hMeq, ← hSeq]
  have hT1special : ∀ v ∈ T.erase x, nonadj r v = firstNeighbors r x := fun v hv =>
    hspecial v (Finset.mem_erase.mp hv).2 (Finset.mem_erase.mp hv).1
  have hnotO : ∀ v ∈ T.erase x, v ∉ firstNeighbors r x := by
    intro v hv hvO
    rw [← hT1special v hv] at hvO
    exact (mem_nonadj.mp hvO).1 rfl
  have hT1pred : ∀ v ∈ T.erase x, ∃ u ∈ T.erase x, r u v := by
    intro v hv
    obtain ⟨u, hu, huv⟩ := hTpred v (Finset.mem_erase.mp hv).2
    refine ⟨u, Finset.mem_erase.mpr ⟨?_, hu⟩, huv⟩
    intro hux
    rw [hux] at huv
    exact hnotO v hv (mem_firstNeighbors.mpr huv)
  have hT1ne : (T.erase x).Nonempty := by
    obtain ⟨v, hv⟩ := hTne
    by_cases hvx : v = x
    · obtain ⟨u, hu, hux⟩ := hTpred v hv
      rw [hvx] at hux
      refine ⟨u, Finset.mem_erase.mpr ⟨?_, hu⟩⟩
      intro heq
      rw [heq] at hux
      exact hr.loopless x hux
    · exact ⟨v, Finset.mem_erase.mpr ⟨hvx, hv⟩⟩
  apply no_tournament_sourceless r hr h.tri (T.erase x) hT1ne ?_ hT1pred
  intro a ha b hb hab
  by_contra hnon
  have hn1 : ¬ r a b := fun h' => hnon (Or.inl h')
  have hn2 : ¬ r b a := fun h' => hnon (Or.inr h')
  have hbM : b ∈ nonadj r a := mem_nonadj.mpr ⟨fun h' => hab h'.symm, hn1, hn2⟩
  rw [hT1special a ha] at hbM
  exact hnotO b hb hbM

/-- Step 2: the dual weighting after deleting the two exceptional vertices. -/
theorem dual (h : TwoDef r t x y) (hcs : ∀ c, r x c → r y c → False)
    (hcp : ∀ c, r c x → r c y → False) :
    ∃ P : V → ℝ, (∀ v, 0 ≤ P v) ∧ ∑ v, P v = 1 ∧ P x = 0 ∧ P y = 0 ∧
      (∀ v, P v ≠ 0 → (r x v ∧ r v y) ∨ (r y v ∧ r v x)) ∧
      (∀ u, u ≠ x → u ≠ y →
        P u + 2 * ∑ z ∈ firstNeighbors r u, P z +
          ∑ z ∈ firstNeighbors (rev r) u, P z = 1) := by
  classical
  have hr := h.oriented
  have hρ : IsOriented (sub x y (rev r)) :=
    ⟨fun a => hr.loopless a.1, fun hab hba => hr.asymmetric hba hab⟩
  have hρtri : ∀ a b c, sub x y (rev r) a b → sub x y (rev r) b c →
      ¬ sub x y (rev r) c a := fun a b c hab hbc hca => h.tri c.1 b.1 a.1 hbc hab hca
  obtain ⟨z0, hz0, hz0x⟩ := Finset.exists_mem_ne (s := firstNeighbors r y)
    (by have := h.out y h.ne.symm; have := h.two; omega) x
  have hz0y : z0 ≠ y := by
    intro heq
    have h1 := mem_firstNeighbors.mp hz0
    rw [heq] at h1
    exact hr.loopless y h1
  have hne : Nonempty {v : V // v ≠ x ∧ v ≠ y} := ⟨⟨z0, hz0x, hz0y⟩⟩
  have hcardW : Fintype.card {v : V // v ≠ x ∧ v ≠ y} + 2 = 3 * t := by
    have h1 := congrArg Finset.card (univ_sub_map x y)
    rw [Finset.card_map, Finset.card_univ] at h1
    have h2 := card_erase_two (Finset.univ : Finset V) x y h.ne
    simp only [Finset.mem_univ, ↓reduceIte, Finset.card_univ] at h2
    have h3 := h.card
    omega
  have hflip : ∀ u : {v : V // v ≠ x ∧ v ≠ y},
      firstNeighbors (rev (sub x y (rev r))) u = firstNeighbors (sub x y r) u := by
    intro u
    ext z
    rw [mem_firstNeighbors, mem_firstNeighbors]
    exact Iff.rfl
  -- degrees after the deletion
  have hin : ∀ u : {v : V // v ≠ x ∧ v ≠ y},
      t ≤ (firstNeighbors (sub x y (rev r)) u).card + 1 ∧
        ((firstNeighbors (sub x y (rev r)) u).card + 1 = t → r x u.1 ∨ r y u.1) := by
    intro u
    have h1 := congrArg Finset.card (first_sub_map x y (rev r) u)
    rw [Finset.card_map] at h1
    have h2 := card_erase_two (firstNeighbors (rev r) u.1) x y h.ne
    have h3 := h.inn u.1 u.2.2
    by_cases hx : x ∈ firstNeighbors (rev r) u.1
    · by_cases hy : y ∈ firstNeighbors (rev r) u.1
      · exact absurd (hcs u.1 ((mem_firstNeighbors (r := rev r)).mp hx)
          ((mem_firstNeighbors (r := rev r)).mp hy)) id
      · simp only [hx, hy, ↓reduceIte] at h2
        exact ⟨by omega, fun _ => Or.inl ((mem_firstNeighbors (r := rev r)).mp hx)⟩
    · by_cases hy : y ∈ firstNeighbors (rev r) u.1
      · simp only [hx, hy, ↓reduceIte] at h2
        exact ⟨by omega, fun _ => Or.inr ((mem_firstNeighbors (r := rev r)).mp hy)⟩
      · simp only [hx, hy, ↓reduceIte] at h2
        exact ⟨by omega, fun heq => by omega⟩
  have hout : ∀ u : {v : V // v ≠ x ∧ v ≠ y},
      t ≤ (firstNeighbors (sub x y r) u).card + 1 ∧
        ((firstNeighbors (sub x y r) u).card + 1 = t → r u.1 x ∨ r u.1 y) := by
    intro u
    have h1 := congrArg Finset.card (first_sub_map x y r u)
    rw [Finset.card_map] at h1
    have h2 := card_erase_two (firstNeighbors r u.1) x y h.ne
    have h3 := h.out u.1 u.2.1
    by_cases hx : x ∈ firstNeighbors r u.1
    · by_cases hy : y ∈ firstNeighbors r u.1
      · exact absurd (hcp u.1 (mem_firstNeighbors.mp hx) (mem_firstNeighbors.mp hy)) id
      · simp only [hx, hy, ↓reduceIte] at h2
        exact ⟨by omega, fun _ => Or.inl (mem_firstNeighbors.mp hx)⟩
    · by_cases hy : y ∈ firstNeighbors r u.1
      · simp only [hx, hy, ↓reduceIte] at h2
        exact ⟨by omega, fun _ => Or.inr (mem_firstNeighbors.mp hy)⟩
      · simp only [hx, hy, ↓reduceIte] at h2
        exact ⟨by omega, fun heq => by omega⟩
  have hpart : ∀ u : {v : V // v ≠ x ∧ v ≠ y},
      (firstNeighbors (sub x y (rev r)) u).card + (firstNeighbors (sub x y r) u).card +
        (nonadj (sub x y (rev r)) u).card + 3 = 3 * t := by
    intro u
    have h1 := card_partition (sub x y (rev r)) hρ u
    rw [hflip u] at h1
    omega
  have hSle : ∀ u : {v : V // v ≠ x ∧ v ≠ y},
      (secondNeighbors (sub x y (rev r)) u).card ≤ (nonadj (sub x y (rev r)) u).card :=
    fun u => Finset.card_le_card (second_subset_nonadj _ hρtri u)
  have hnoW : ∀ u : {v : V // v ≠ x ∧ v ≠ y},
      ∑ _z ∈ secondNeighbors (sub x y (rev r)) u, (1 : ℝ) ≤
        ∑ _z ∈ firstNeighbors (sub x y (rev r)) u, (1 : ℝ) := by
    intro u
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    have h1 := hSle u
    have h2 := hpart u
    have h3 := (hin u).1
    have h4 := (hout u).1
    exact_mod_cast (by omega : (secondNeighbors (sub x y (rev r)) u).card ≤
      (firstNeighbors (sub x y (rev r)) u).card)
  obtain ⟨p, hp0, hp1, hptied, hpcoord⟩ := tied_dual (sub x y (rev r)) hρ
    (fun _ => (1 : ℝ)) (fun _ => one_pos) hnoW
  -- structure at a supported vertex
  have htiedfacts : ∀ v : {v : V // v ≠ x ∧ v ≠ y}, p v ≠ 0 →
      (firstNeighbors (sub x y (rev r)) v).card + 1 = t ∧
        (firstNeighbors (sub x y r) v).card + 1 = t ∧
        secondNeighbors (sub x y (rev r)) v = nonadj (sub x y (rev r)) v := by
    intro v hv
    have htie := hptied v hv
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at htie
    have htieN : (secondNeighbors (sub x y (rev r)) v).card =
        (firstNeighbors (sub x y (rev r)) v).card := by exact_mod_cast htie
    have h1 := hSle v
    have h2 := hpart v
    have h3 := (hin v).1
    have h4 := (hout v).1
    refine ⟨by omega, by omega, ?_⟩
    exact Finset.eq_of_subset_of_card_le (second_subset_nonadj _ hρtri v) (by omega)
  -- extension by zero
  let P : V → ℝ := fun v => if hv : v ≠ x ∧ v ≠ y then p ⟨v, hv⟩ else 0
  have hPsub : ∀ w : {v : V // v ≠ x ∧ v ≠ y}, P w.1 = p w := by
    intro w
    show (if hv : w.1 ≠ x ∧ w.1 ≠ y then p ⟨w.1, hv⟩ else 0) = p w
    rw [dif_pos w.2]
  have hPx : P x = 0 := by
    show (if hv : x ≠ x ∧ x ≠ y then p ⟨x, hv⟩ else 0) = 0
    rw [dif_neg (fun hc => hc.1 rfl)]
  have hPy : P y = 0 := by
    show (if hv : y ≠ x ∧ y ≠ y then p ⟨y, hv⟩ else 0) = 0
    rw [dif_neg (fun hc => hc.2 rfl)]
  have hP0 : ∀ v, 0 ≤ P v := by
    intro v
    by_cases hv : v ≠ x ∧ v ≠ y
    · have := hPsub ⟨v, hv⟩
      simp only at this
      rw [this]
      exact hp0 _
    · show 0 ≤ (if hv : v ≠ x ∧ v ≠ y then p ⟨v, hv⟩ else 0)
      rw [dif_neg hv]
  have htransfer : ∀ A : Finset {v : V // v ≠ x ∧ v ≠ y},
      ∑ w ∈ A, p w = ∑ z ∈ A.map (subEmb x y), P z := by
    intro A
    rw [Finset.sum_map]
    apply Finset.sum_congr rfl
    intro w _
    exact (hPsub w).symm
  have herase : ∀ A : Finset V, ∑ z ∈ (A.erase x).erase y, P z = ∑ z ∈ A, P z := by
    intro A
    rw [Finset.sum_erase _ hPy, Finset.sum_erase _ hPx]
  have hfirstP : ∀ (q : V → V → Prop) (u : {v : V // v ≠ x ∧ v ≠ y}),
      ∑ w ∈ firstNeighbors (sub x y q) u, p w = ∑ z ∈ firstNeighbors q u.1, P z := by
    intro q u
    rw [htransfer, first_sub_map, herase]
  have hPsum : ∑ v, P v = 1 := by
    rw [← herase Finset.univ, ← univ_sub_map, ← htransfer]
    exact hp1
  refine ⟨P, hP0, hPsum, hPx, hPy, ?_, ?_⟩
  · intro v hv
    have hvc : v ≠ x ∧ v ≠ y := by
      by_contra hc
      apply hv
      show (if hv : v ≠ x ∧ v ≠ y then p ⟨v, hv⟩ else 0) = 0
      rw [dif_neg hc]
    have hpv : p ⟨v, hvc⟩ ≠ 0 := by
      have h1 := hPsub ⟨v, hvc⟩
      simp only at h1
      rw [← h1]
      exact hv
    obtain ⟨hi, ho, _⟩ := htiedfacts ⟨v, hvc⟩ hpv
    have hI := (hin ⟨v, hvc⟩).2 hi
    have hO := (hout ⟨v, hvc⟩).2 ho
    simp only at hI hO
    rcases hI with hxv | hyv
    · rcases hO with hvx | hvy
      · exact absurd hvx (hr.asymmetric hxv)
      · exact Or.inl ⟨hxv, hvy⟩
    · rcases hO with hvx | hvy
      · exact Or.inr ⟨hyv, hvx⟩
      · exact absurd hvy (hr.asymmetric hyv)
  · intro u hux huy
    have hpartsum := sum_partition (sub x y (rev r)) hρ p ⟨u, hux, huy⟩
    rw [hp1, hflip] at hpartsum
    have hcoord := hpcoord ⟨u, hux, huy⟩
    have hR : Finset.univ.filter (fun v : {v : V // v ≠ x ∧ v ≠ y} =>
        (⟨u, hux, huy⟩ : {v : V // v ≠ x ∧ v ≠ y}) ∈ firstNeighbors (sub x y (rev r)) v) =
          firstNeighbors (sub x y r) ⟨u, hux, huy⟩ := by
      ext v
      rw [Finset.mem_filter, mem_firstNeighbors, mem_firstNeighbors]
      exact ⟨fun hc => hc.2, fun hc => ⟨Finset.mem_univ _, hc⟩⟩
    have hL : ∑ v ∈ Finset.univ.filter (fun v : {v : V // v ≠ x ∧ v ≠ y} =>
        (⟨u, hux, huy⟩ : {v : V // v ≠ x ∧ v ≠ y}) ∈ secondNeighbors (sub x y (rev r)) v),
          p v = ∑ v ∈ nonadj (sub x y (rev r)) ⟨u, hux, huy⟩, p v := by
      have hA := Finset.sum_filter (s := (Finset.univ : Finset {v : V // v ≠ x ∧ v ≠ y}))
        (fun v => (⟨u, hux, huy⟩ : {v : V // v ≠ x ∧ v ≠ y}) ∈
          secondNeighbors (sub x y (rev r)) v) p
      have hB : ∑ v ∈ nonadj (sub x y (rev r)) ⟨u, hux, huy⟩, p v =
          ∑ v, if v ∈ nonadj (sub x y (rev r)) ⟨u, hux, huy⟩ then p v else 0 := by
        rw [Finset.sum_ite_mem, Finset.univ_inter]
      rw [hA, hB]
      apply Finset.sum_congr rfl
      intro v _
      by_cases hpv : p v = 0
      · simp only [hpv, ite_self]
      · obtain ⟨_, _, hS⟩ := htiedfacts v hpv
        have hiff : (⟨u, hux, huy⟩ : {v : V // v ≠ x ∧ v ≠ y}) ∈
            secondNeighbors (sub x y (rev r)) v ↔
              v ∈ nonadj (sub x y (rev r)) ⟨u, hux, huy⟩ := by
          rw [hS, mem_nonadj, mem_nonadj]
          constructor
          · rintro ⟨a, b, c⟩
            exact ⟨fun h' => a h'.symm, c, b⟩
          · rintro ⟨a, b, c⟩
            exact ⟨fun h' => a h'.symm, c, b⟩
        by_cases hw : (⟨u, hux, huy⟩ : {v : V // v ≠ x ∧ v ≠ y}) ∈
            secondNeighbors (sub x y (rev r)) v
        · simp only [hw, hiff.mp hw, ↓reduceIte]
        · have hw' : v ∉ nonadj (sub x y (rev r)) ⟨u, hux, huy⟩ :=
            fun h' => hw (hiff.mpr h')
          simp only [hw, hw', ↓reduceIte]
    rw [hL, hR] at hcoord
    have e1 := hfirstP (rev r) ⟨u, hux, huy⟩
    have e2 := hfirstP r ⟨u, hux, huy⟩
    have e3 := hPsub ⟨u, hux, huy⟩
    simp only at e1 e2 e3
    rw [← e1, ← e2, e3]
    linarith

/-- Step 3: the dual weighting cannot exist. -/
theorem final [Nonempty V] (h : TwoDef r t x y) (P : V → ℝ) (hP0 : ∀ v, 0 ≤ P v)
    (hP1 : ∑ v, P v = 1) (hPx : P x = 0)
    (hsupp : ∀ v, P v ≠ 0 → (r x v ∧ r v y) ∨ (r y v ∧ r v x))
    (hone : ∀ u, u ≠ x → u ≠ y →
      P u + 2 * ∑ z ∈ firstNeighbors r u, P z +
        ∑ z ∈ firstNeighbors (rev r) u, P z = 1) : False := by
  classical
  have hr := h.oriented
  have hQ1 : ∀ u, u ≠ x → u ≠ y →
      ∑ z ∈ secondNeighbors r u, P z ≤ ∑ z ∈ firstNeighbors r u, P z := by
    intro u hux huy
    have h1 := sum_partition r hr P u
    have h2 : ∑ z ∈ secondNeighbors r u, P z ≤ ∑ z ∈ nonadj r u, P z :=
      Finset.sum_le_sum_of_subset_of_nonneg (second_subset_nonadj r h.tri u)
        (fun z _ _ => hP0 z)
    have h3 := hone u hux huy
    linarith
  have hSx0 : ∑ z ∈ secondNeighbors r x, P z = 0 := by
    apply Finset.sum_eq_zero
    intro z hz
    by_contra hPz
    obtain ⟨_, hnot, a, hxa, haz⟩ := mem_secondNeighbors.mp hz
    rcases hsupp z hPz with ⟨hxz, _⟩ | ⟨_, hzx⟩
    · exact hnot hxz
    · exact h.tri x a z hxa haz hzx
  have hSy0 : ∑ z ∈ secondNeighbors r y, P z = 0 := by
    apply Finset.sum_eq_zero
    intro z hz
    by_contra hPz
    obtain ⟨_, hnot, a, hya, haz⟩ := mem_secondNeighbors.mp hz
    rcases hsupp z hPz with ⟨_, hzy⟩ | ⟨hyz, _⟩
    · exact h.tri y a z hya haz hzy
    · exact hnot hyz
  have cOx : ((firstNeighbors r x).card : ℝ) + 1 = t := by exact_mod_cast h.outx
  have cSx : ((secondNeighbors r x).card : ℝ) ≤ t := by
    have h1 := h.second_le x
    have h2 := h.nonadj_x
    exact_mod_cast (by omega : (secondNeighbors r x).card ≤ t)
  have cSy : ((secondNeighbors r y).card : ℝ) ≤ t := by
    have h1 := h.second_le y
    have h2 := h.nonadj_y
    exact_mod_cast (by omega : (secondNeighbors r y).card ≤ t)
  have cOy : ((firstNeighbors r y).card : ℝ) = t := by exact_mod_cast h.out y h.ne.symm
  have cOrd : ∀ v, v ≠ x → v ≠ y →
      ((secondNeighbors r v).card : ℝ) + 1 ≤ t ∧ ((firstNeighbors r v).card : ℝ) = t := by
    intro v hvx hvy
    have h1 := h.second_le v
    have h2 := h.nonadj_ord v hvx hvy
    refine ⟨?_, by exact_mod_cast h.out v hvx⟩
    exact_mod_cast (by omega : (secondNeighbors r v).card + 1 ≤ t)
  -- the weighting vanishes on the successors of `x`
  have hα : ∑ z ∈ firstNeighbors r x, P z = 0 := by
    by_contra hne
    have hαnn : 0 ≤ ∑ z ∈ firstNeighbors r x, P z := Finset.sum_nonneg (fun z _ => hP0 z)
    have hαpos : 0 < ∑ z ∈ firstNeighbors r x, P z := lt_of_le_of_ne hαnn (Ne.symm hne)
    obtain ⟨L, hL⟩ : ∃ L : ℝ, L = 2 / ∑ z ∈ firstNeighbors r x, P z := ⟨_, rfl⟩
    have hLpos : 0 < L := by
      rw [hL]
      exact div_pos two_pos hαpos
    have hLα : L * ∑ z ∈ firstNeighbors r x, P z = 2 := by
      rw [hL]
      exact div_mul_cancel₀ 2 hne
    have hsumw : ∀ A : Finset V, ∑ z ∈ A, (1 + L * P z) =
        (A.card : ℝ) + L * ∑ z ∈ A, P z := by
      intro A
      rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, Finset.mul_sum]
    have hstrictx : ∑ z ∈ secondNeighbors r x, (1 + L * P z) <
        ∑ z ∈ firstNeighbors r x, (1 + L * P z) := by
      rw [hsumw, hsumw, hSx0, hLα]
      linarith
    have hley : ∑ z ∈ secondNeighbors r y, (1 + L * P z) ≤
        ∑ z ∈ firstNeighbors r y, (1 + L * P z) := by
      rw [hsumw, hsumw, hSy0]
      have h1 : 0 ≤ L * ∑ z ∈ firstNeighbors r y, P z :=
        mul_nonneg hLpos.le (Finset.sum_nonneg (fun z _ => hP0 z))
      linarith
    have hstrictord : ∀ v, v ≠ x → v ≠ y → ∑ z ∈ secondNeighbors r v, (1 + L * P z) <
        ∑ z ∈ firstNeighbors r v, (1 + L * P z) := by
      intro v hvx hvy
      rw [hsumw, hsumw]
      obtain ⟨c1, c2⟩ := cOrd v hvx hvy
      have h1 := mul_le_mul_of_nonneg_left (hQ1 v hvx hvy) hLpos.le
      linarith
    have hno : ∀ v, ∑ z ∈ secondNeighbors r v, (1 + L * P z) ≤
        ∑ z ∈ firstNeighbors r v, (1 + L * P z) := by
      intro v
      by_cases hvx : v = x
      · rw [hvx]
        exact hstrictx.le
      · by_cases hvy : v = y
        · rw [hvy]
          exact hley
        · exact (hstrictord v hvx hvy).le
    obtain ⟨T, hTne, hTtied, hTpred⟩ := tied_cycle r hr h.sinkless (fun z => 1 + L * P z)
      (fun z => by have := mul_nonneg hLpos.le (hP0 z); linarith) hno
    have hTy : ∀ v ∈ T, v = y := by
      intro v hv
      have htie := hTtied v hv
      by_contra hvy
      by_cases hvx : v = x
      · rw [hvx] at htie
        linarith
      · have := hstrictord v hvx hvy
        linarith
    obtain ⟨v, hv⟩ := hTne
    obtain ⟨u, hu, huv⟩ := hTpred v hv
    rw [hTy v hv, hTy u hu] at huv
    exact hr.loopless y huv
  have hOx0 : ∀ z ∈ firstNeighbors r x, P z = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun z _ => hP0 z)).mp hα
  have hsupp' : ∀ v, P v ≠ 0 → r y v ∧ r v x := by
    intro v hv
    rcases hsupp v hv with ⟨hxv, _⟩ | hc
    · exact absurd (hOx0 v (mem_firstNeighbors.mpr hxv)) hv
    · exact hc
  obtain ⟨b, hb⟩ : ∃ b, P b ≠ 0 := by
    by_contra hnone
    have hall : ∀ v ∈ (Finset.univ : Finset V), P v = 0 := by
      intro v _
      by_contra hv
      exact hnone ⟨v, hv⟩
    rw [Finset.sum_eq_zero hall] at hP1
    exact zero_ne_one hP1
  obtain ⟨hyb, hbx⟩ := hsupp' b hb
  have hnxy : ¬ r x y := fun hxy => h.tri x y b hxy hyb hbx
  -- every supported vertex points to every successor of `x`
  have hall : ∀ c, r x c → ∀ v, P v ≠ 0 → r v c := by
    intro c hxc v hv
    have hcx : c ≠ x := by
      intro heq
      rw [heq] at hxc
      exact hr.loopless x hxc
    have hcy : c ≠ y := by
      intro heq
      rw [heq] at hxc
      exact hnxy hxc
    have h1 := hone c hcx hcy
    have hPc : P c = 0 := hOx0 c (mem_firstNeighbors.mpr hxc)
    have hOc : ∑ z ∈ firstNeighbors r c, P z = 0 := by
      apply Finset.sum_eq_zero
      intro z hz
      by_contra hPz
      exact h.tri x c z hxc (mem_firstNeighbors.mp hz) (hsupp' z hPz).2
    have hIc : ∑ z ∈ firstNeighbors (rev r) c, P z = 1 := by
      rw [hPc, hOc] at h1
      linarith
    by_contra hvc
    have hvI : v ∉ firstNeighbors (rev r) c := fun hc =>
      hvc ((mem_firstNeighbors (r := rev r)).mp hc)
    have h2 : ∑ z ∈ insert v (firstNeighbors (rev r) c), P z ≤ ∑ z, P z :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun z _ _ => hP0 z)
    rw [Finset.sum_insert hvI, hIc, hP1] at h2
    have h3 := lt_of_le_of_ne (hP0 v) (Ne.symm hv)
    linarith
  -- the out-neighbourhood of a supported vertex
  have hOsupp : ∀ v, P v ≠ 0 → firstNeighbors r v = insert x (firstNeighbors r x) := by
    intro v hv
    have hvx : v ≠ x := by
      intro heq
      have h1 := (hsupp' v hv).2
      rw [heq] at h1
      exact hr.loopless x h1
    have hsub : insert x (firstNeighbors r x) ⊆ firstNeighbors r v := by
      intro z hz
      rcases Finset.mem_insert.mp hz with hzx | hz
      · rw [hzx]
        exact mem_firstNeighbors.mpr (hsupp' v hv).2
      · exact mem_firstNeighbors.mpr (hall z (mem_firstNeighbors.mp hz) v hv)
    have hxO : x ∉ firstNeighbors r x := fun hc => hr.loopless x (mem_firstNeighbors.mp hc)
    have hcard : (firstNeighbors r v).card ≤ (insert x (firstNeighbors r x)).card := by
      rw [Finset.card_insert_of_notMem hxO]
      have h1 := h.out v hvx
      have h2 := h.outx
      omega
    exact (Finset.eq_of_subset_of_card_le hsub hcard).symm
  have hbx' : b ≠ x := by
    intro heq
    rw [heq] at hbx
    exact hr.loopless x hbx
  have hby : b ≠ y := by
    intro heq
    rw [heq] at hyb
    exact hr.loopless y hyb
  have hOb : ∑ z ∈ firstNeighbors r b, P z = 0 := by
    rw [hOsupp b hb]
    have hxO : x ∉ firstNeighbors r x := fun hc => hr.loopless x (mem_firstNeighbors.mp hc)
    rw [Finset.sum_insert hxO, hPx, hα]
    ring
  have hIb : ∑ z ∈ firstNeighbors (rev r) b, P z = 0 := by
    apply Finset.sum_eq_zero
    intro z hz
    by_contra hPz
    have hzb : r z b := (mem_firstNeighbors (r := rev r)).mp hz
    have hbO : b ∈ firstNeighbors r z := mem_firstNeighbors.mpr hzb
    rw [hOsupp z hPz] at hbO
    rcases Finset.mem_insert.mp hbO with hbx2 | hbO
    · exact hbx' hbx2
    · exact hr.asymmetric (mem_firstNeighbors.mp hbO) hbx
  have hPb : P b = 1 := by
    have h1 := hone b hbx' hby
    rw [hOb, hIb] at h1
    linarith
  -- an in-neighbour of `b` other than `y`
  obtain ⟨u, hu, huy⟩ := Finset.exists_mem_ne (s := firstNeighbors (rev r) b)
    (by have := h.inn b hby; have := h.two; omega) y
  have hub : r u b := (mem_firstNeighbors (r := rev r)).mp hu
  have hux : u ≠ x := by
    intro heq
    rw [heq] at hub
    exact hr.asymmetric hub hbx
  have h1 := hone u hux huy
  have h2 : P b ≤ ∑ z ∈ firstNeighbors r u, P z :=
    Finset.single_le_sum (fun z _ => hP0 z) (mem_firstNeighbors.mpr hub)
  have h3 : 0 ≤ ∑ z ∈ firstNeighbors (rev r) u, P z :=
    Finset.sum_nonneg (fun z _ => hP0 z)
  have h4 := hP0 u
  linarith

end TwoDef

/-- **Two deficits at different vertices are impossible.** -/
theorem two_deficits {r : V → V → Prop} {t : ℕ} {x y : V} (h : TwoDef r t x y) : False := by
  have hne : Nonempty V := ⟨x⟩
  have hcs : ∀ c, r x c → r y c → False := fun c => h.no_common_succ c
  have hcp : ∀ c, r c x → r c y → False := fun c hcx hcy => h.flip.no_common_succ c hcy hcx
  obtain ⟨P, hP0, hP1, hPx, _, hsupp, hone⟩ := h.dual hcs hcp
  exact h.final P hP0 hP1 hPx hsupp hone

end LeanCH.BR.TwoSeymour

#print axioms LeanCH.BR.TwoSeymour.two_deficits
