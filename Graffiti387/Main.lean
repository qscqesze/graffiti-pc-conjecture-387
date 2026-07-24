import Graffiti387.Polynomial
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Order.Lattice.Nat

/-!
# A machine-checked proof of Graffiti.pc Conjecture 387

The theorem is stated for every nonempty finite simple graph; connectedness is
not assumed.
-/

namespace Graffiti387

open Finset

noncomputable section

variable {V : Type*} [Fintype V]

local instance : DecidableEq V := Classical.decEq V

/-- `D` 2-dominates `G` when every vertex outside `D` has at least two
neighbors in `D`. -/
def TwoDominates (G : SimpleGraph V) [DecidableRel G.Adj] (D : Finset V) : Prop :=
  ∀ v ∉ D, 2 ≤ (D.filter fun w ↦ G.Adj v w).card

/-- The 2-domination number, defined as the infimum of the cardinalities of
all 2-dominating sets. -/
def twoDominationNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  sInf {k : ℕ | ∃ D : Finset V, D.card = k ∧ TwoDominates G D}

/-- The nonneighbors of `v`, excluding `v` itself. -/
def nonneighbors (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : Finset V :=
  Finset.univ.filter fun w ↦ w ≠ v ∧ ¬ G.Adj v w

lemma neighborFinset_card_add_nonneighbors_card
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    (G.neighborFinset v).card + (nonneighbors G v).card = Fintype.card V - 1 := by
  have hpart := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.erase v) (fun w ↦ G.Adj v w)
  have hneighbor : (Finset.univ.erase v).filter (fun w ↦ G.Adj v w) =
      G.neighborFinset v := by
    ext w
    constructor
    · intro hw
      exact (SimpleGraph.mem_neighborFinset G v w).mpr (Finset.mem_filter.mp hw).2
    · intro hw
      have hadj := (SimpleGraph.mem_neighborFinset G v w).mp hw
      exact Finset.mem_filter.mpr ⟨
        Finset.mem_erase.mpr ⟨(G.ne_of_adj hadj).symm, Finset.mem_univ w⟩, hadj⟩
  have hnonneighbor : (Finset.univ.erase v).filter (fun w ↦ ¬G.Adj v w) =
      nonneighbors G v := by
    ext w
    simp [nonneighbors]
  rw [hneighbor, hnonneighbor,
    Finset.card_erase_of_mem (Finset.mem_univ v)] at hpart
  exact hpart

lemma nonadjacent_in_subset_nonneighbors
    (G : SimpleGraph V) [DecidableRel G.Adj] {D : Finset V} {v : V}
    (hv : v ∉ D) :
    D.filter (fun w ↦ ¬G.Adj v w) ⊆ nonneighbors G v := by
  intro w hw
  have hw' := Finset.mem_filter.mp hw
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ w, by
    refine ⟨?_, hw'.2⟩
    intro hwv
    exact hv (hwv ▸ hw'.1)⟩

omit [Fintype V] in
lemma twoDominates_of_nonneighbor_bound
    (G : SimpleGraph V) [DecidableRel G.Adj] {D : Finset V} {t : ℕ}
    (hD : D.card = t + 2)
    (hbound : ∀ v ∉ D, (D.filter fun w ↦ ¬G.Adj v w).card ≤ t) :
    TwoDominates G D := by
  intro v hv
  have hpart := Finset.card_filter_add_card_filter_not
    (s := D) (fun w ↦ G.Adj v w)
  have hb := hbound v hv
  rw [hD] at hpart
  omega

lemma nonneighbors_card_le_of_degree_ge
    (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℕ) {v : V}
    (hm : m ≤ G.degree v) :
    (nonneighbors G v).card ≤ Fintype.card V - 1 - m := by
  have hpartition := neighborFinset_card_add_nonneighbors_card G v
  rw [SimpleGraph.card_neighborFinset_eq_degree] at hpartition
  omega

/-- If all vertices of degree below `m` fit into a set of size
`|V| - m + 1`, that set can be completed to a 2-dominating set of the
claimed size. -/
lemma exists_twoDominating_of_few_low_degree
    (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℕ)
    (hmpos : 1 ≤ m) (hm : m ≤ Fintype.card V - 1)
    (hfew : (Finset.univ.filter fun v ↦ G.degree v < m).card ≤
      Fintype.card V - 1 - m + 1) :
    ∃ D : Finset V,
      D.card = Fintype.card V - m + 1 ∧ TwoDominates G D := by
  classical
  let t := Fintype.card V - 1 - m
  let B := Finset.univ.filter fun v ↦ G.degree v < m
  have htcard : t + 2 ≤ Fintype.card V := by
    dsimp [t]
    omega
  have hBcard : B.card ≤ t + 2 := by
    dsimp [B, t] at *
    omega
  obtain ⟨D, hBD, -, hDcard⟩ := Finset.exists_subsuperset_card_eq
    (Finset.subset_univ B) hBcard htcard
  refine ⟨D, ?_, twoDominates_of_nonneighbor_bound G hDcard ?_⟩
  · dsimp [t] at hDcard ⊢
    omega
  · intro v hv
    have hvB : v ∉ B := fun hvB ↦ hv (hBD hvB)
    have hvhigh : m ≤ G.degree v := by
      simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at hvB
      omega
    exact (Finset.card_le_card
      (nonadjacent_in_subset_nonneighbors G hv)).trans
      (nonneighbors_card_le_of_degree_ge G m hvhigh)

/-- The polynomial-circuit argument for the complementary case, when there
are many vertices on both sides of the degree threshold. -/
lemma exists_twoDominating_of_many_low_degree
    (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℕ)
    (hmpos : 1 ≤ m) (hm : m ≤ Fintype.card V - 1)
    (hmany : Fintype.card V - 1 - m + 2 ≤
      (Finset.univ.filter fun v ↦ G.degree v < m).card)
    (hmajor : (Finset.univ.filter fun v ↦ G.degree v < m).card ≤
      (Finset.univ.filter fun v ↦ m ≤ G.degree v).card) :
    ∃ D : Finset V,
      D.card = Fintype.card V - m + 1 ∧ TwoDominates G D := by
  classical
  let t := Fintype.card V - 1 - m
  let H := Finset.univ.filter fun v ↦ m ≤ G.degree v
  let B := Finset.univ.filter fun v ↦ G.degree v < m
  let eH : H ↪ V := Function.Embedding.subtype _
  let eB : B ↪ V := Function.Embedding.subtype _
  let N : H → Finset B := fun i ↦
    Finset.univ.filter fun z ↦ ¬G.Adj (i : V) (z : V)
  have hNcard : ∀ i, (N i).card ≤ t := by
    intro i
    have hi : m ≤ G.degree (i : V) := by
      exact (Finset.mem_filter.mp i.property).2
    have hmap : (N i).map eB ⊆ nonneighbors G i := by
      intro w hw
      obtain ⟨z, hzN, rfl⟩ := Finset.mem_map.mp hw
      have hzlow : G.degree (z : V) < m :=
        (Finset.mem_filter.mp z.property).2
      have hne : (z : V) ≠ (i : V) := by
        intro hzi
        rw [hzi] at hzlow
        omega
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne, (Finset.mem_filter.mp hzN).2⟩
    calc
      (N i).card = ((N i).map eB).card := (Finset.card_map eB).symm
      _ ≤ (nonneighbors G i).card := Finset.card_le_card hmap
      _ ≤ t := nonneighbors_card_le_of_degree_ge G m hi
  have htB : t ≤ Fintype.card B := by
    rw [Fintype.card_coe]
    dsimp [B, t] at *
    omega
  have hAexists : ∀ i : H, ∃ A : Finset B,
      N i ⊆ A ∧ A ⊆ Finset.univ ∧ A.card = t := by
    intro i
    exact Finset.exists_subsuperset_card_eq
      (Finset.subset_univ (N i)) (hNcard i) htB
  choose A hNA hAuniv hAcard using hAexists
  have htH : t + 2 ≤ Fintype.card H := by
    rw [Fintype.card_coe]
    dsimp [H, B, t] at *
    omega
  have htBtwo : t + 2 ≤ Fintype.card B := by
    rw [Fintype.card_coe]
    dsimp [B, t] at *
    omega
  obtain ⟨C, Y, hCY, hCtwo, hselect⟩ :=
    polynomialCircuitSelection A t hAcard htH htBtwo
  let D := C.map eH ∪ Y.map eB
  have hdisjoint : Disjoint (C.map eH) (Y.map eB) := by
    rw [Finset.disjoint_left]
    intro v hvC hvY
    obtain ⟨i, hiC, hiv⟩ := Finset.mem_map.mp hvC
    obtain ⟨z, hzY, hzv⟩ := Finset.mem_map.mp hvY
    have hi : m ≤ G.degree (i : V) :=
      (Finset.mem_filter.mp i.property).2
    have hz : G.degree (z : V) < m :=
      (Finset.mem_filter.mp z.property).2
    have hiz : (i : V) = (z : V) := hiv.trans hzv.symm
    rw [hiz] at hi
    omega
  have hDcard : D.card = t + 2 := by
    dsimp [D]
    rw [Finset.card_union_of_disjoint hdisjoint, Finset.card_map,
      Finset.card_map, hCY]
  refine ⟨D, ?_, twoDominates_of_nonneighbor_bound G hDcard ?_⟩
  · dsimp [t] at hDcard ⊢
    omega
  · intro v hvD
    by_cases hvB : v ∈ B
    · let z : B := ⟨v, hvB⟩
      have hzY : z ∉ Y := by
        intro hzY
        apply hvD
        exact Finset.mem_union_right _ (Finset.mem_map.mpr ⟨z, hzY, rfl⟩)
      have hsel := hselect z hzY
      let E := (C.filter fun i ↦ z ∈ A i).map eH ∪ Y.map eB
      have hsub : D.filter (fun w ↦ ¬G.Adj v w) ⊆ E := by
        intro w hw
        obtain ⟨hwD, hnadj⟩ := Finset.mem_filter.mp hw
        rcases Finset.mem_union.mp hwD with hwC | hwY
        · obtain ⟨i, hiC, hiw⟩ := Finset.mem_map.mp hwC
          have hziN : z ∈ N i := by
            apply Finset.mem_filter.mpr
            refine ⟨Finset.mem_univ z, ?_⟩
            intro hadj
            apply hnadj
            have := G.adj_symm hadj
            simpa [z, eH] using (hiw ▸ this)
          exact Finset.mem_union_left _ (Finset.mem_map.mpr
            ⟨i, Finset.mem_filter.mpr ⟨hiC, hNA i hziN⟩, hiw⟩)
        · exact Finset.mem_union_right _ hwY
      calc
        (D.filter fun w ↦ ¬G.Adj v w).card ≤ E.card :=
          Finset.card_le_card hsub
        _ ≤ (C.filter fun i ↦ z ∈ A i).card + Y.card := by
          simpa [E] using Finset.card_union_le
            ((C.filter fun i ↦ z ∈ A i).map eH) (Y.map eB)
        _ ≤ t := by omega
    · have hvhigh : m ≤ G.degree v := by
        simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at hvB
        omega
      exact (Finset.card_le_card
        (nonadjacent_in_subset_nonneighbors G hvD)).trans
        (nonneighbors_card_le_of_degree_ge G m hvhigh)

/-- Threshold form of the graph theorem.  At least as many vertices have
degree at least `m` as have degree below `m`. -/
theorem exists_twoDominating_of_highDegree_majority
    (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℕ)
    (hm : m ≤ Fintype.card V - 1)
    (hmajor : (Finset.univ.filter fun v ↦ G.degree v < m).card ≤
      (Finset.univ.filter fun v ↦ m ≤ G.degree v).card) :
    ∃ D : Finset V,
      D.card ≤ Fintype.card V - m + 1 ∧ TwoDominates G D := by
  classical
  by_cases hmzero : m = 0
  · subst m
    refine ⟨Finset.univ, by simp, ?_⟩
    intro v hv
    simp at hv
  · have hmpos : 1 ≤ m := by omega
    by_cases hfew : (Finset.univ.filter fun v ↦ G.degree v < m).card ≤
        Fintype.card V - 1 - m + 1
    · obtain ⟨D, hDcard, hD⟩ :=
        exists_twoDominating_of_few_low_degree G m hmpos hm hfew
      exact ⟨D, hDcard.le, hD⟩
    · have hmany : Fintype.card V - 1 - m + 2 ≤
          (Finset.univ.filter fun v ↦ G.degree v < m).card := by
        omega
      obtain ⟨D, hDcard, hD⟩ :=
        exists_twoDominating_of_many_low_degree G m hmpos hm hmany hmajor
      exact ⟨D, hDcard.le, hD⟩

/-- The upper median degree, equivalently the degree in position
`floor(|V| / 2) + 1` when degrees are sorted increasingly.  This threshold
definition avoids choosing a particular sorted list. -/
def upperMedianDegree (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  Nat.findGreatest
    (fun m ↦ (Fintype.card V + 1) / 2 ≤
      (Finset.univ.filter fun v ↦ m ≤ G.degree v).card)
    (Fintype.card V - 1)

lemma upperMedianDegree_le
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    upperMedianDegree G ≤ Fintype.card V - 1 := by
  exact Nat.findGreatest_le _

lemma upperMedianDegree_high_count
    [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (Fintype.card V + 1) / 2 ≤
      (Finset.univ.filter fun v ↦ upperMedianDegree G ≤ G.degree v).card := by
  have hcardpos : 1 ≤ Fintype.card V := Fintype.card_pos
  have hzero : (Fintype.card V + 1) / 2 ≤
      (Finset.univ.filter fun v ↦ 0 ≤ G.degree v).card := by
    simp
    omega
  simpa only [upperMedianDegree] using
    (Nat.findGreatest_spec
      (P := fun m ↦ (Fintype.card V + 1) / 2 ≤
        (Finset.univ.filter fun v ↦ m ≤ G.degree v).card)
      (m := 0) (n := Fintype.card V - 1) (Nat.zero_le _) hzero)

lemma upperMedianDegree_majority
    [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (Finset.univ.filter fun v ↦ G.degree v < upperMedianDegree G).card ≤
      (Finset.univ.filter fun v ↦ upperMedianDegree G ≤ G.degree v).card := by
  let H := Finset.univ.filter fun v ↦ upperMedianDegree G ≤ G.degree v
  let B := Finset.univ.filter fun v ↦ G.degree v < upperMedianDegree G
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := Finset.univ) (fun v ↦ upperMedianDegree G ≤ G.degree v)
  have hBH : B.card + H.card = Fintype.card V := by
    dsimp [B, H]
    rw [Nat.add_comm]
    simpa only [Finset.card_univ, not_le] using hpartition
  have hhigh : (Fintype.card V + 1) / 2 ≤ H.card := by
    exact upperMedianDegree_high_count G
  dsimp [B, H] at *
  omega

/-- Graffiti.pc Conjecture 387.  The proof is stronger than the original
connected-graph statement: it holds for every nonempty finite simple graph. -/
theorem graffiti_pc_387
    [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ D : Finset V,
      D.card ≤ Fintype.card V - upperMedianDegree G + 1 ∧
      TwoDominates G D := by
  exact exists_twoDominating_of_highDegree_majority G (upperMedianDegree G)
    (upperMedianDegree_le G) (upperMedianDegree_majority G)

/-- The customary numerical formulation using the 2-domination number. -/
theorem twoDominationNumber_le
    [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    twoDominationNumber G ≤ Fintype.card V - upperMedianDegree G + 1 := by
  obtain ⟨D, hcard, hdom⟩ := graffiti_pc_387 G
  have hmem : D.card ∈ {k : ℕ | ∃ E : Finset V,
      E.card = k ∧ TwoDominates G E} := ⟨D, rfl, hdom⟩
  exact (Nat.sInf_le hmem).trans hcard

end

end Graffiti387
