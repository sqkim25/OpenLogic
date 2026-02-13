# COMPRESSION-PLAN: Per-Section Compression Decisions

## CH-BST: Set-Theoretic Foundations (Level-0)

---

### Chapter: sets

### sfr/set/bas — Extensionality
- **Action**: KEEP
- **Lean Chapter**: CH-BST
- **Lean Section**: BST.1: Sets and Membership
- **Rationale**: Sole defining occurrence of PRIM-BST001 (Set identity / Extensionality), PRIM-BST002 (Membership ∈), and PRIM-BST004 (Empty set ∅). Signal is CORE-DEF only; every downstream BST concept depends on this section.
- **Content Directives**:
  - Formal items to preserve: `\begin{defn}[Extensionality]`; informal definitions of set, membership (∈), empty set (∅), and set-builder notation {x | φ(x)}
  - Formal items to drop: none
  - Prose: preserve — foundational definitions require full context
  - Examples: keep best 1 of 3 — retain the `{a, a, b} = {a, b} = {b, a}` extensionality example (self-contained, directly instantiates PRIM-BST001, minimal prerequisites); cut novice/math tagged examples
  - Proofs: N/A (no proofs in this section)

---

### sfr/set/sub — Subsets and Power Sets
- **Action**: KEEP
- **Lean Chapter**: CH-BST
- **Lean Section**: BST.1: Sets and Membership
- **Rationale**: Sole defining occurrence of PRIM-BST003 (Subset ⊆) and PRIM-BST015 (Power Set 𝒫). Signal is CORE-DEF only. Both primitives are heavily referenced in cardinality (THM-BST001) and throughout later domains.
- **Content Directives**:
  - Formal items to preserve: `\begin{defn}[Subset]`; `\begin{prop}` (A = B iff A ⊆ B and B ⊆ A — stepping stone linking PRIM-BST001 to PRIM-BST003); `\begin{defn}[Power Set]`
  - Formal items to drop: `\begin{defn}[forallxina]` — pedagogical (bounded quantifier notation); drop but add one-line remark noting the convention
  - Prose: compress to intro + definitions only; cut the extended discussion connecting extensionality to mutual subsets (keep the proposition itself)
  - Examples: keep best 1 of 2 — retain the `𝒫({a,b,c})` example (canonical, directly instantiates PRIM-BST015); cut the ∈ vs ⊆ example (pedagogical)
  - Proofs: N/A (proposition is immediate; no extended proof)

---

### sfr/set/imp — Some Important Sets
- **Action**: CONDENSE
- **Lean Chapter**: CH-BST
- **Lean Section**: BST.1: Sets and Membership (for ℕ); BST.4: Sequences and Numbers (for A*, A^ω)
- **Rationale**: Introduces PRIM-BST012 (ℕ), PRIM-BST010 (Finite Sequence A*), PRIM-BST011 (Infinite Sequence A^ω). Signal is CORE-DEF + PEDAGOGICAL. The ℤ, ℚ, ℝ introductions are pedagogical context only. However, sfr/set/pai is the primary for PRIM-BST010; this section's A* content will MERGE-INTO sfr/set/pai.
- **Content Directives**:
  - Formal items to preserve: Definition of ℕ (PRIM-BST012); definition of A^ω (PRIM-BST011)
  - Formal items to drop: ℤ, ℚ, ℝ definitions — pedagogical only, not in taxonomy; ℤ⁺ and Bin = {0,1} — minor notational conveniences, can be introduced inline elsewhere
  - Prose: compress to intro + definition only — one sentence introducing ℕ as the set of natural numbers, one sentence for A^ω as infinite sequences. Cut extended discussion of number set hierarchy.
  - Examples: cut all — the examples are pedagogical (number set inclusions)
  - Proofs: N/A

---

### sfr/set/uni — Unions and Intersections
- **Action**: KEEP
- **Lean Chapter**: CH-BST
- **Lean Section**: BST.1: Sets and Membership
- **Rationale**: Sole defining occurrence of PRIM-BST005 (Union ∪, Intersection ∩, general ⋃, general ⋂). Signal is CORE-DEF only. Union and intersection operations are used pervasively.
- **Content Directives**:
  - Formal items to preserve: `\begin{defn}[Union]`; `\begin{defn}[Intersection]` (including disjoint definition); `\begin{defn}` (general ⋃A); `\begin{defn}` (general ⋂A)
  - Formal items to drop: `\begin{defn}[Difference]` — set difference A∖B is not in the taxonomy (OL-ONLY: pedagogical); retain one-line mention as notation
  - Prose: compress to intro + definitions only; cut extended explanations and Venn diagram references
  - Examples: keep best 1 — retain the `⋃{{a,b},{a,d,e},{a,d}} = {a,b,d,e}` example (illustrates general union/intersection simultaneously, self-contained)
  - Proofs: N/A

---

### sfr/set/pai — Pairs, Tuples, Cartesian Products
- **Action**: ABSORB:sfr/set/imp(PRIM-BST010)
- **Lean Chapter**: CH-BST
- **Lean Section**: BST.1: Sets and Membership (for PRIM-BST006, PRIM-BST007); BST.4: Sequences and Numbers (for PRIM-BST010)
- **Rationale**: Sole defining occurrence of PRIM-BST006 (Ordered Pair, Wiener-Kuratowski) and PRIM-BST007 (Cartesian Product). Also primary for PRIM-BST010 (Finite Sequence A*) per COMPRESSION-TARGET #1 — absorbs the A* content that sfr/set/imp also introduces. Signal is CORE-DEF + STEPPING-STONE.
- **Content Directives**:
  - Formal items to preserve: `\begin{defn}[Ordered pair, wienerkuratowski]` (PRIM-BST006); `\begin{defn}[Cartesian product]` (PRIM-BST007); n-tuple recursive definition; A* (words) example as definition of PRIM-BST010
  - Formal items to drop: `\begin{prop}[cardnmprod]` (|A×B| = |A|·|B|) — stepping stone only, not needed for lean text; its proof is instructive but not required for dependency chain
  - Prose: compress to intro + definitions only; preserve the remark that ⟨a,b⟩ = {{a},{a,b}} reduces pairs to sets
  - Examples: keep the A* (words) example — canonical for PRIM-BST010 and self-contained; cut the A×B enumeration example (pedagogical)
  - Proofs: cut `\begin{proof}` of cardnmprod — stepping stone only

---

### sfr/set/rus — Russell's Paradox
- **Action**: CUT
- **Lean Chapter**: CH-BST
- **Lean Section**: N/A
- **Rationale**: Introduces no taxonomy items. Signal is PEDAGOGICAL + TANGENTIAL. The theorem (R = {x | x ∉ x} cannot exist) is pedagogically important but not formally required in the BST taxonomy. The discussion motivates axiomatic set theory but our lean text treats set theory naively (as does OL). Content can be referenced via a footnote from sfr/set/bas if needed.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: `\begin{thm}[Russell's Paradox]` — pedagogical/tangential; no taxonomy ID
  - Prose: replace with cross-ref footnote in sfr/set/bas noting the limitation of naive comprehension
  - Examples: cut all
  - Proofs: cut all

---

### sfr/set/prf — Proofs about Sets
- **Action**: CUT
- **Lean Chapter**: CH-BST
- **Lean Section**: N/A
- **Rationale**: Introduces no taxonomy items. Signal is PEDAGOGICAL only. Section is marked INACTIVE in OL (superseded by content/methods/proofs). Contains only a worked example of the absorption law as a pedagogical proof demonstration.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: `\begin{prop}[Absorption]` — purely pedagogical worked example
  - Prose: cut all
  - Examples: cut all
  - Proofs: cut all

---

### Chapter: relations

### sfr/rel/set — Relations as Sets
- **Action**: KEEP
- **Lean Chapter**: CH-BST
- **Lean Section**: BST.2: Relations
- **Rationale**: Sole defining occurrence of PRIM-BST008 (Binary Relation as subset of A²). Signal is CORE-DEF only. Every subsequent relation-dependent concept (DEF-BST004, DEF-BST005) depends on this definition.
- **Content Directives**:
  - Formal items to preserve: `\begin{defn}[Binary relation]`; Id(A) identity relation definition (inline)
  - Formal items to drop: none
  - Prose: compress to intro + definition only; cut the extended explain block leading into the definition (but preserve the one-line motivation connecting pairs to relations)
  - Examples: keep best 1 — retain the matrix layout of ℕ² with identity/less-than/greater-than relations (canonical, directly instantiates PRIM-BST008, self-contained); cut the remark about empty/universal relations (add one-line note)
  - Proofs: N/A

---

### sfr/rel/ref — Philosophical Reflections
- **Action**: CUT
- **Lean Chapter**: CH-BST
- **Lean Section**: N/A
- **Rationale**: Introduces no taxonomy items. Signal is PEDAGOGICAL only. Purely philosophical discussion (Benacerraf-style arguments against set-theoretic reductionism). No formal definitions or theorems.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: N/A (no formal items)
  - Prose: cut all
  - Examples: cut all
  - Proofs: cut all

---

### sfr/rel/prp — Special Properties of Relations
- **Action**: KEEP
- **Lean Chapter**: CH-BST
- **Lean Section**: BST.2: Relations
- **Rationale**: Defines seven relation properties (reflexivity, transitivity, symmetry, anti-symmetry, connectivity, irreflexivity, asymmetry) that are prerequisites for DEF-BST004 (Equivalence Relation) and DEF-BST005 (Partial Order). Signal is CORE-DEF. All seven are GAP-CANDIDATES but function as building blocks for taxonomy items.
- **Content Directives**:
  - Formal items to preserve: All seven `\begin{defn}` blocks: Reflexivity, Transitivity, Symmetry, Anti-symmetry, Connectivity, Irreflexivity, Asymmetry
  - Formal items to drop: none — all are necessary building blocks
  - Prose: compress to intro + definitions only; cut the extended explain block about symmetric vs anti-symmetric (retain one-line clarifying remark)
  - Examples: cut all — the examples are pedagogical; the definitions are self-explanatory
  - Proofs: N/A

---

### sfr/rel/eqv — Equivalence Relations
- **Action**: KEEP
- **Lean Chapter**: CH-BST
- **Lean Section**: BST.2: Relations
- **Rationale**: Sole defining occurrence of DEF-BST004 (Equivalence Relation). Also introduces equivalence class and quotient (GAP-CANDIDATES). Signal is CORE-DEF + CORE-THM. The partition theorem (Rxy iff [x]_R = [y]_R) is a key structural result.
- **Content Directives**:
  - Formal items to preserve: `\begin{defn}[Equivalence relation]` (DEF-BST004); `\begin{defn}[equivalenceclass]` (equivalence class [x]_R and quotient A/R); `\begin{prop}` (Rxy iff [x]_R = [y]_R)
  - Formal items to drop: none
  - Prose: compress to intro + definitions only; the partition discussion is essential motivation
  - Examples: keep best 1 — retain modular arithmetic ≡_n example (canonical, self-contained, directly shows equivalence classes)
  - Proofs: preserve full — the partition proof is short and structurally important (uses reflexivity, symmetry, transitivity, extensionality)

---

### sfr/rel/ord — Orders
- **Action**: CONDENSE
- **Lean Chapter**: CH-BST
- **Lean Section**: BST.2: Relations
- **Rationale**: Sole defining occurrence of DEF-BST005 (Partial Order). Also defines preorder, linear order, strict order, strict linear order (GAP-CANDIDATES). Signal is CORE-DEF + CORE-THM. The strict↔partial conversion propositions are stepping stones. The extensionality proposition is pedagogical.
- **Content Directives**:
  - Formal items to preserve: `\begin{defn}[Preorder]`; `\begin{defn}[Partial order]` (DEF-BST005); `\begin{defn}[Linear order]`; `\begin{defn}[Strict order]`; `\begin{defn}[Strict linear order]`; `\begin{prop}[stricttopartial]` (reflexive closure construction)
  - Formal items to drop: `\begin{prop}[partialtostrict]` — converse construction, pedagogical (proof left as exercise); `\begin{prop}[extensionality-strictlinearorders]` — pedagogical
  - Prose: compress to intro + definitions only; cut extended examples
  - Examples: keep best 1 of 5 — retain ⊆ on power sets (canonical partial order, directly instantiates DEF-BST005, uses PRIM-BST003/015); cut ≤ on ℕ (too trivial), divisibility, extension, no-longer-than examples
  - Proofs: preserve sketch only for stricttopartial — the 3-part structure (reflexive, anti-symmetric, transitive) is useful as a template; cut detailed proof of partialtostrict and extensionality-strictlinearorders

---

### sfr/rel/grp — Graphs
- **Action**: CUT
- **Lean Chapter**: CH-BST
- **Lean Section**: N/A
- **Rationale**: Introduces no taxonomy items. Signal is PEDAGOGICAL only. Directed graphs are just relations with explicit vertex sets — this adds no new formal content beyond PRIM-BST008. The concept is tangential to logic foundations.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: `\begin{defn}[Directed graph]` — pedagogical, no taxonomy ID
  - Prose: cut all
  - Examples: cut all
  - Proofs: N/A

---

### sfr/rel/tre — Trees
- **Action**: CONDENSE
- **Lean Chapter**: CH-BST
- **Lean Section**: BST.2: Relations
- **Rationale**: Introduces tree (GAP-CANDIDATE) which is heavily used in derivation systems, completeness proofs, and syntax trees throughout SYN/DED domains. Signal is CORE-DEF + STEPPING-STONE. König's lemma is stated without proof (pedagogical). Trees are downstream of DEF-BST005.
- **Content Directives**:
  - Formal items to preserve: `\begin{defn}[Tree]` (set-theoretic definition as partial order with root); `\begin{defn}[Successors]`; `\begin{defn}[Branches]`
  - Formal items to drop: `\begin{prop}` (unique predecessor) — pedagogical; `\begin{defn}` (infinite/finite/finitely branching) — compress to one-line note; `\begin{prop}[König's lemma]` — stated without proof, pedagogical
  - Prose: compress to intro + definitions only
  - Examples: keep best 1 — retain {0,1}* binary tree example (canonical, self-contained, connects to PRIM-BST010)
  - Proofs: N/A (no proofs given)

---

### sfr/rel/ops — Operations on Relations
- **Action**: CONDENSE
- **Lean Chapter**: CH-BST
- **Lean Section**: BST.2: Relations
- **Rationale**: Defines six operations on relations — all GAP-CANDIDATES. Signal is CORE-DEF. Transitive closure is particularly important for computational semantics and derivation chains. All are building blocks for later domains.
- **Content Directives**:
  - Formal items to preserve: `\begin{defn}[relationoperations]` — all four: Inverse (R⁻¹), Relative Product (R|S), Restriction (R↾A), Application (R[A]); `\begin{defn}[Transitive closure]` (R⁺ and R*)
  - Formal items to drop: none — all six operations are needed
  - Prose: compress to intro + definitions only; cut extended explanations
  - Examples: cut all — pedagogical (successor relation on ℤ); definitions are self-explanatory with formal notation
  - Proofs: N/A

---

### Chapter: functions

### sfr/fun/bas — Basics
- **Action**: KEEP
- **Lean Chapter**: CH-BST
- **Lean Section**: BST.3: Functions
- **Rationale**: Sole defining occurrence of PRIM-BST009 (Function f:A→B, domain, codomain, range). Signal is CORE-DEF only. Every function-related concept (DEF-BST001–003) depends on this.
- **Content Directives**:
  - Formal items to preserve: `\begin{defn}[Function]` (PRIM-BST009) — including domain, codomain, arguments, values, range
  - Formal items to drop: none
  - Prose: preserve — the definition needs its surrounding context for clarity; compress the extensionality-for-functions remark to one line
  - Examples: keep best 1 of 6 — retain the successor function f(x) = x+1 example (minimal prerequisites, directly instantiates PRIM-BST009, shows domain/codomain/range distinction); cut multiplication, square root, student/grades, by-cases, and examplefunext examples
  - Proofs: N/A

---

### sfr/fun/kin — Kinds of Functions
- **Action**: KEEP
- **Lean Chapter**: CH-BST
- **Lean Section**: BST.3: Functions
- **Rationale**: Sole defining occurrence of DEF-BST001 (Injection), DEF-BST002 (Surjection), DEF-BST003 (Bijection). Signal is CORE-DEF only. These three definitions are heavily used in cardinality theory (PRIM-BST016, THM-BST001–003).
- **Content Directives**:
  - Formal items to preserve: `\begin{defn}[surjective function]` (DEF-BST002); `\begin{defn}[injective function]` (DEF-BST001); `\begin{defn}[bijection]` (DEF-BST003)
  - Formal items to drop: none
  - Prose: compress to intro + definitions only; cut explain blocks about how to show surjectivity/injectivity and the induced surjection remark
  - Examples: keep best 1 of the combined example block — retain the four-function example (constant, identity, successor, halving) as it illustrates all four combinations of injective/surjective; cut figure references
  - Proofs: N/A

---

### sfr/fun/rel — Functions as Relations
- **Action**: CONDENSE
- **Lean Chapter**: CH-BST
- **Lean Section**: BST.3: Functions
- **Rationale**: Bridges PRIM-BST009 and PRIM-BST008. Signal is PEDAGOGICAL + STEPPING-STONE. The graph concept enables treating functions as sets of pairs — this is infrastructure for the function-relation identification used elsewhere. The graph and functional-relation proposition are stepping stones.
- **Content Directives**:
  - Formal items to preserve: `\begin{defn}[Graph of a function]` — stepping stone connecting PRIM-BST009 to PRIM-BST008
  - Formal items to drop: `\begin{prop}[prop:graph-function]` — pedagogical (converse direction); `\begin{defn}[defn:funimage]` (restriction, image) — pedagogical, can be noted inline in sfr/rel/ops cross-ref
  - Prose: compress to intro + definition only; one sentence noting that functions can be identified with functional relations
  - Examples: cut all
  - Proofs: cut all

---

### sfr/fun/inv — Inverses of Functions
- **Action**: KEEP
- **Lean Chapter**: CH-BST
- **Lean Section**: BST.3: Functions
- **Rationale**: Connects DEF-BST001 (Injection), DEF-BST002 (Surjection), DEF-BST003 (Bijection) to invertibility. Signal is CORE-THM + STEPPING-STONE. The bijection-inverse theorem is structurally important for cardinality (equinumerosity symmetry). Axiom of Choice mention is a key dependency note.
- **Content Directives**:
  - Formal items to preserve: `\begin{defn}` (inverse); `\begin{prop}` (injective → left inverse); `\begin{prop}` (surjective → right inverse); `\begin{prop}[prop:bijection-inverse]` (bijection has unique inverse)
  - Formal items to drop: `\begin{prop}[prop:left-right]` — pedagogical (left = right inverse; follows from above); `\begin{prop}[prop:inverse-unique]` — pedagogical (immediate corollary of left-right)
  - Prose: compress to intro + definitions + theorem statements; note the Axiom of Choice dependency for surjective right inverse in one sentence
  - Examples: cut all — successor example is pedagogical motivation
  - Proofs: preserve sketch only — for injective→left inverse (construction by cases) and bijection→inverse (combine left+right); cut detailed proof of surjective→right inverse (defers to AC)

---

### sfr/fun/cmp — Composition of Functions
- **Action**: KEEP
- **Lean Chapter**: CH-BST
- **Lean Section**: BST.3: Functions
- **Rationale**: Defines composition (g∘f), which is used in equinumerosity transitivity proof and throughout. Signal is CORE-DEF + STEPPING-STONE. Composition preserving injection/surjection are key structural results.
- **Content Directives**:
  - Formal items to preserve: `\begin{defn}[Composition]` (g∘f)(x) = g(f(x))
  - Formal items to drop: none
  - Prose: compress to intro + definition only; one sentence noting composition preserves injection and surjection (problems state this)
  - Examples: keep best 1 — retain f(x)=x+1, g(x)=2x example (minimal, self-contained, directly instantiates composition)
  - Proofs: N/A (composition preserving inj/surj are exercises)

---

### sfr/fun/iso — Isomorphism
- **Action**: CUT
- **Lean Chapter**: CH-BST
- **Lean Section**: N/A
- **Rationale**: Introduces no taxonomy items. Signal is PEDAGOGICAL + TANGENTIAL. Isomorphism (structure-preserving bijection) is important for model theory but not primitive to BST. Can be introduced when needed in SEM domain.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: `\begin{defn}[Isomorphism]` — tangential to BST; belongs in SEM/MET domain if needed
  - Prose: cut all
  - Examples: cut all
  - Proofs: N/A

---

### sfr/fun/par — Partial Functions
- **Action**: CUT
- **Lean Chapter**: CH-BST
- **Lean Section**: N/A
- **Rationale**: Introduces no taxonomy items. Signal is PEDAGOGICAL + TANGENTIAL. Partial functions are important for computation (CMP domain) but not primitive to BST. Can be introduced when needed in CMP domain.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: `\begin{defn}[partial function]` — tangential to BST; `\begin{defn}[Graph of partial function]` — pedagogical; `\begin{prop}` — pedagogical
  - Prose: cut all
  - Examples: cut all
  - Proofs: cut all

---

### Chapter: inductive-defs-proofs

### sfr/ind/int — Introduction (Induction)
- **Action**: CONDENSE + ABSORB:{sfr/infinite/induction}
- **Lean Chapter**: CH-BST
- **Lean Section**: BST.5: Induction and Recursion
- **Rationale**: Sole primary defining occurrence of PRIM-BST013 (Mathematical Induction on ℕ) and PRIM-BST014 (Structural Induction on formulas). Signal is CORE-DEF + PEDAGOGICAL. The closure/preservation stepping stones are pedagogical scaffolding. Per COMPRESSION-TARGET #2, this is primary for PRIM-BST013; sfr/infinite/induction merges into this.
- **Content Directives**:
  - Formal items to preserve: `\begin{defn}[Induction on ℕ]` (PRIM-BST013); `\begin{defn}[Induction on formulas]` (PRIM-BST014)
  - Formal items to drop: `\begin{defn}` (closure under function) — stepping stone, compress to one-line prerequisite remark; `\begin{defn}` (preserved under function) — stepping stone, compress to one-line prerequisite remark
  - Prose: compress to intro + definitions only; cut the extended worked example (sum of first n naturals) — pedagogical; retain the formula induction "recipe" outline (it is the operational content of PRIM-BST014)
  - Examples: cut all (sum of first n naturals is pedagogical)
  - Proofs: N/A

---

### Chapter: size-of-sets

### sfr/siz/int — Introduction
- **Action**: CUT
- **Lean Chapter**: CH-BST
- **Lean Section**: N/A
- **Rationale**: Introduces no taxonomy items. Signal is PEDAGOGICAL only. Purely motivational prose with no formal definitions or theorems. The motivation for cardinality is provided by the definitions themselves.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: N/A (no formal items)
  - Prose: cut all
  - Examples: cut all
  - Proofs: N/A

---

### sfr/siz/enm — Enumerations and Enumerable Sets
- **Action**: ABSORB:sfr/siz/enm-alt
- **Lean Chapter**: CH-BST
- **Lean Section**: BST.6: Cardinality
- **Rationale**: Primary defining occurrence of PRIM-BST016 (Enumerability/Countability) and THM-BST002 (ℕ is countably infinite). Signal is CORE-DEF + CORE-THM. Per COMPRESSION-TARGET #3, this is primary for PRIM-BST016; sfr/siz/enm-alt merges into this. Absorbs the alternative formulation.
- **Content Directives**:
  - Formal items to preserve: Informal definition of enumeration; `\begin{defn}[Enumeration, formally]` (surjection ℤ⁺→A); `\begin{defn}[defn:enumerable]` (PRIM-BST016); `\begin{cor}[cor:enum-nat]` (THM-BST002: ℕ enumerable)
  - Formal items to drop: `\begin{prop}[prop:enum-shift]` — infrastructure (ℤ⁺ vs ℕ index shift), compress to one-line remark; `\begin{prop}[prop:enum-bij]` — infrastructure (surjection↔bijection equivalence), compress to one-line remark noting equivalence; `\begin{cor}[cor:enum-nat-bij]` — infrastructure corollary, subsume into remark; `\begin{prop}` (enumeration without repetitions) — pedagogical
  - Prose: compress to intro + definitions only; note the surjection/bijection equivalence in one line (absorbing sfr/siz/enm-alt's perspective)
  - Examples: keep best 1 — retain the ℤ enumeration via hopping (0, 1, −1, 2, −2, ...) — canonical, self-contained, shows infinite set enumeration; cut ℤ⁺ identity, even/odd examples
  - Proofs: preserve sketch only for cor:enum-nat — state that identity function enumerates ℕ (one line)

---

### sfr/siz/zigzag — Cantor's Zig-Zag Method
- **Action**: KEEP
- **Lean Chapter**: CH-BST
- **Lean Section**: BST.6: Cardinality
- **Rationale**: Canonical instantiation of THM-BST003 (Countable Union of Countable Sets — ℕ×ℕ enumerable). Signal is CORE-THM + STEPPING-STONE. The zig-zag technique is the foundational method for all countability closure results.
- **Content Directives**:
  - Formal items to preserve: `\begin{prop}[natsquaredenumerable]` (THM-BST003: ℕ×ℕ enumerable); generalization to ℕⁿ
  - Formal items to drop: none
  - Prose: preserve — the zig-zag array and diagonal traversal explanation is essential to understanding the technique
  - Examples: preserve the zig-zag array with position numbers — this IS the proof technique, not merely an example
  - Proofs: preserve full — the proof is the zig-zag construction itself, which is the core content

---

### sfr/siz/pai — Pairing Functions and Codes
- **Action**: CONDENSE
- **Lean Chapter**: CH-BST
- **Lean Section**: BST.6: Cardinality
- **Rationale**: Provides explicit formula for zig-zag enumeration. Signal is STEPPING-STONE only. The pairing function formula is a useful technique but not a primitive or theorem in the taxonomy.
- **Content Directives**:
  - Formal items to preserve: Pairing function definition and explicit formula g(n,m) = ((n+m)(n+m+1))/2 + n
  - Formal items to drop: none — only one formal item
  - Prose: compress to intro + definition only; cut extended problem applications
  - Examples: cut all (problems applying pairing to ℚ, Bin*, etc. are exercises)
  - Proofs: N/A

---

### sfr/siz/pai-alt — An Alternative Pairing Function
- **Action**: CUT
- **Lean Chapter**: CH-BST
- **Lean Section**: N/A
- **Rationale**: Introduces no taxonomy items. Signal is PEDAGOGICAL only. Alternative pairing functions (2ⁿ(2m+1)−1, 2ⁿ3ᵐ) are pedagogical variations; the canonical pairing function in sfr/siz/pai suffices.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: both alternative pairing examples — pedagogical
  - Prose: cut all
  - Examples: cut all
  - Proofs: N/A

---

### sfr/siz/nen — Non-enumerable Sets
- **Action**: ABSORB:sfr/siz/nen-alt
- **Lean Chapter**: CH-BST
- **Lean Section**: BST.6: Cardinality
- **Rationale**: Proves specific non-enumerability results (Bin^ω, 𝒫(ℤ⁺)) that are stepping stones to THM-BST001 (Cantor's Theorem in sfr/siz/car). Signal is STEPPING-STONE + CORE-THM. Per COMPRESSION-TARGET #4, this is primary for the specific instances; sfr/siz/nen-alt and sfr/siz/car are handled separately.
- **Content Directives**:
  - Formal items to preserve: `\begin{thm}[thm:nonenum-bin-omega]` (Bin^ω non-enumerable — canonical diagonal argument); `\begin{thm}[thm:nonenum-pownat]` (𝒫(ℤ⁺) non-enumerable)
  - Formal items to drop: none
  - Prose: compress — retain the diagonal method explanation for Bin^ω (this is the canonical presentation of diagonalization); cut the extended step-by-step walkthrough; retain the array visualization
  - Examples: preserve the diagonal array — it IS the proof method
  - Proofs: preserve full for thm:nonenum-bin-omega (canonical diagonal argument — this is the authoritative presentation of diagonalization for the lean text); preserve sketch only for thm:nonenum-pownat (follows same pattern, reference back to Bin^ω diagonal)

---

### sfr/siz/red — Reduction
- **Action**: CONDENSE + ABSORB:{sfr/siz/red-alt}
- **Lean Chapter**: CH-BST
- **Lean Section**: BST.6: Cardinality
- **Rationale**: Demonstrates the reduction proof technique. Signal is STEPPING-STONE only. The technique is useful but the specific proof (alternative proof of thm:nonenum-pownat via Bin^ω) is redundant given sfr/siz/nen already proves it.
- **Content Directives**:
  - Formal items to preserve: The reduction technique statement (if A is non-enumerable and there exists an injection A→B, then B is non-enumerable)
  - Formal items to drop: Alternative proof of thm:nonenum-pownat — redundant with sfr/siz/nen
  - Prose: compress to one paragraph stating the reduction principle
  - Examples: cut all
  - Proofs: cut — the specific application is redundant

---

### sfr/siz/equ — Equinumerosity
- **Action**: CONDENSE
- **Lean Chapter**: CH-BST
- **Lean Section**: BST.6: Cardinality
- **Rationale**: Defines equinumerosity (≈) as notation for bijection-based size comparison. Signal is CORE-DEF. The equivalence relation proof is infrastructure. This is a notational bridge between DEF-BST003 and PRIM-BST016.
- **Content Directives**:
  - Formal items to preserve: `\begin{defn}[comparisondef]` (A ≈ B iff bijection f: A→B)
  - Formal items to drop: `\begin{prop}[equinumerosityisequi]` — infrastructure (equinumerosity is equivalence relation); compress to one-line remark; unnamed prop about enumerable preservation — infrastructure, compress to one-line remark
  - Prose: compress to intro + definition only; cut Frege quotation (pedagogical)
  - Examples: cut all
  - Proofs: cut full proof of equivalence relation property — state as remark (follows from identity, inverse, composition of bijections)

---

### sfr/siz/car — Sets of Different Sizes, and Cantor's Theorem
- **Action**: KEEP
- **Lean Chapter**: CH-BST
- **Lean Section**: BST.6: Cardinality
- **Rationale**: Sole defining occurrence of THM-BST001 (Cantor's Theorem: |A| < |𝒫(A)|). Signal is CORE-THM + CORE-DEF. This is the culminating theorem of BST cardinality theory. Per COMPRESSION-TARGET #4, this is the primary for THM-BST001; sfr/siz/nen and sfr/siz/nen-alt provide stepping stones.
- **Content Directives**:
  - Formal items to preserve: `\begin{defn}` (A ≤ B via injection); `\begin{defn}` (A < B: injection but no bijection); `\begin{thm}[thm:cantor]` (THM-BST001: |A| < |𝒫(A)|)
  - Formal items to drop: none
  - Prose: compress to intro + definitions + theorem; retain the comparison to Russell's Paradox in one line (cross-ref only)
  - Examples: N/A
  - Proofs: preserve full — the diagonal/anti-diagonal construction {x ∈ A : x ∉ g(x)} is the core technique; this is the authoritative proof of THM-BST001

---

### sfr/siz/sb — The Notion of Size, and Schröder-Bernstein
- **Action**: CONDENSE
- **Lean Chapter**: CH-BST
- **Lean Section**: BST.6: Cardinality
- **Rationale**: States Schröder-Bernstein (GAP-CANDIDATE) without proof. Signal is STEPPING-STONE only. The theorem is important for cardinality comparison but not in the current taxonomy. Proof is deferred to sfr/infinite/card-sb.
- **Content Directives**:
  - Formal items to preserve: `\begin{thm}[thm:schroder-bernstein]` statement (if A ≤ B and B ≤ A then A ≈ B)
  - Formal items to drop: none — only one formal item
  - Prose: compress to theorem statement + one sentence explaining importance for cardinality comparison + cross-ref to sfr/infinite/card-sb for proof
  - Examples: cut all
  - Proofs: N/A (proof deferred)

---

### sfr/siz/enm-alt — Enumerations and Enumerable Sets (alternative)
- **Action**: MERGE-INTO:sfr/siz/enm
- **Lean Chapter**: CH-BST
- **Lean Section**: BST.6: Cardinality
- **Rationale**: Alternative formulation of PRIM-BST016 using bijections. Signal is CORE-DEF but REDUNDANT with sfr/siz/enm. Per COMPRESSION-TARGET #3, sfr/siz/enm is primary; this section's bijection-based perspective is absorbed as a one-line remark in sfr/siz/enm.
- **Content Directives**:
  - Formal items to preserve: none standalone — bijection equivalence is noted in sfr/siz/enm
  - Formal items to drop: both defn blocks — redundant with sfr/siz/enm
  - Prose: replace with cross-ref to sfr/siz/enm
  - Examples: cut all
  - Proofs: cut all

---

### sfr/siz/nen-alt — Non-enumerable Sets (alternative)
- **Action**: MERGE-INTO:sfr/siz/nen
- **Lean Chapter**: CH-BST
- **Lean Section**: BST.6: Cardinality
- **Rationale**: Same theorems as sfr/siz/nen adapted for bijection-based definitions. Signal is STEPPING-STONE + REDUNDANT-WITH:sfr/siz/nen. Per COMPRESSION-TARGET #4, sfr/siz/nen is primary.
- **Content Directives**:
  - Formal items to preserve: none standalone — content subsumed by sfr/siz/nen
  - Formal items to drop: both theorem blocks — redundant
  - Prose: replace with cross-ref to sfr/siz/nen
  - Examples: cut all
  - Proofs: cut all

---

### sfr/siz/red-alt — Reduction (alternative)
- **Action**: MERGE-INTO:sfr/siz/red
- **Lean Chapter**: CH-BST
- **Lean Section**: BST.6: Cardinality
- **Rationale**: Same reduction proof adapted for nen-alt formulation. Signal is STEPPING-STONE. Redundant with sfr/siz/red. Since sfr/siz/red is condensed, this merges into it.
- **Content Directives**:
  - Formal items to preserve: none standalone
  - Formal items to drop: alternative proof — redundant
  - Prose: replace with cross-ref to sfr/siz/red
  - Examples: cut all
  - Proofs: cut all

---

### Chapter: infinite

### sfr/infinite/hilbert — Hilbert's Hotel
- **Action**: CONDENSE
- **Lean Chapter**: CH-BST
- **Lean Section**: BST.6: Cardinality
- **Rationale**: Defines Dedekind infinite (GAP-CANDIDATE). Signal is CORE-DEF + PEDAGOGICAL. The Dedekind infinite concept bridges cardinality and the algebraic characterization of ℕ. The Hilbert's hotel metaphor is pedagogical.
- **Content Directives**:
  - Formal items to preserve: `\begin{defn}[defn:DedekindInfinite]` (Dedekind infinite: injection from A to proper subset of A)
  - Formal items to drop: none — only one formal item
  - Prose: compress to intro + definition only; cut Hilbert's hotel metaphor (pedagogical) and historical context
  - Examples: cut all
  - Proofs: N/A

---

### sfr/infinite/dedekind — Dedekind Algebras
- **Action**: CONDENSE
- **Lean Chapter**: CH-BST
- **Lean Section**: BST.5: Induction and Recursion
- **Rationale**: Develops Dedekind algebras as set-theoretic characterization of ℕ. Signal is STEPPING-STONE only. The closure machinery is reused in sfr/infinite/card-sb. All concepts are GAP-CANDIDATES.
- **Content Directives**:
  - Formal items to preserve: `\begin{defn}[Closure]` (f-closed set + closure of o under f); Dedekind algebra definition (three properties: 0 not successor, successor injective, closure)
  - Formal items to drop: `\begin{lem}[closureproperties]` — stepping stone, compress to one-line remark; `\begin{thm}[thm:DedekindInfiniteAlgebra]` — stepping stone (Dedekind infinite → Dedekind algebra), compress to one-line remark
  - Prose: compress to intro + definitions only
  - Examples: cut all
  - Proofs: cut all — stepping stone proofs

---

### sfr/infinite/induction — Dedekind Algebras and Arithmetical Induction
- **Action**: MERGE-INTO:sfr/ind/int
- **Lean Chapter**: CH-BST
- **Lean Section**: BST.5: Induction and Recursion
- **Rationale**: Provides set-theoretic justification for PRIM-BST013 (Mathematical Induction). Signal is STEPPING-STONE + PEDAGOGICAL. Per COMPRESSION-TARGET #2, sfr/ind/int is primary for PRIM-BST013; this section's set-theoretic grounding is absorbed as a remark.
- **Content Directives**:
  - Formal items to preserve: none standalone — set-theoretic justification noted as remark in sfr/ind/int
  - Formal items to drop: `\begin{thm}[thm:dedinfiniteinduction]` — stepping stone; `\begin{cor}[natinductionschema]` — stepping stone
  - Prose: replace with cross-ref to sfr/ind/int; note the set-theoretic grounding in one sentence
  - Examples: cut all
  - Proofs: cut all

---

### sfr/infinite/dedekindsproof — Dedekind's "Proof" of the Existence of an Infinite Set
- **Action**: CUT
- **Lean Chapter**: CH-BST
- **Lean Section**: N/A
- **Rationale**: Introduces no taxonomy items. Signal is PEDAGOGICAL + TANGENTIAL. Purely philosophical discussion of Dedekind's controversial existence proof. No formal results.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: N/A (no formal items)
  - Prose: cut all
  - Examples: cut all
  - Proofs: N/A

---

### sfr/infinite/card-sb — Appendix: Proving Schröder-Bernstein
- **Action**: CONDENSE
- **Lean Chapter**: CH-BST
- **Lean Section**: BST.6: Cardinality
- **Rationale**: Proves Schröder-Bernstein theorem (GAP-CANDIDATE stated in sfr/siz/sb). Signal is STEPPING-STONE. Uses closure machinery from sfr/infinite/dedekind. The theorem itself is important for cardinality comparison.
- **Content Directives**:
  - Formal items to preserve: Full proof of Schröder-Bernstein using closure construction
  - Formal items to drop: `\begin{lem}[Closureprops]` — stepping stone, inline into proof sketch; `\begin{prop}[sbhelper]` — stepping stone (subset sandwich), inline into proof sketch
  - Prose: compress to theorem statement (cross-ref sfr/siz/sb) + proof
  - Examples: cut all
  - Proofs: preserve sketch only — outline the closure-based construction in 3-5 sentences; the full detail can be left as exercise

---

### Chapter: arithmetization

### sfr/arith/int — From ℕ to ℤ
- **Action**: CUT
- **Lean Chapter**: CH-BST
- **Lean Section**: N/A
- **Rationale**: Introduces no taxonomy items. Signal is TANGENTIAL + PEDAGOGICAL. Integer construction via equivalence classes on ℕ×ℕ is outside the taxonomy (ℕ is primitive; we do not need constructed number systems). Demonstrates DEF-BST004 in practice but this application is tangential.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: ℤ-equivalence proposition — pedagogical; integer construction definition — tangential
  - Prose: cut all
  - Examples: cut all
  - Proofs: cut all

---

### sfr/arith/rat — From ℤ to ℚ
- **Action**: CUT
- **Lean Chapter**: CH-BST
- **Lean Section**: N/A
- **Rationale**: Introduces no taxonomy items. Signal is TANGENTIAL + PEDAGOGICAL. Rational construction is outside the taxonomy. Parallel to sfr/arith/int.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: rational construction definition — tangential
  - Prose: cut all
  - Examples: cut all
  - Proofs: cut all

---

### sfr/arith/real — The Real Line
- **Action**: CUT
- **Lean Chapter**: CH-BST
- **Lean Section**: N/A
- **Rationale**: Introduces no taxonomy items. Signal is PEDAGOGICAL + STEPPING-STONE. Motivates real numbers and proves √2 irrational. The Completeness Property is a GAP-CANDIDATE but belongs to analysis, not BST.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: `\begin{thm}[root2irrational]` — pedagogical
  - Prose: cut all
  - Examples: cut all
  - Proofs: cut all

---

### sfr/arith/cuts — From ℚ to ℝ
- **Action**: CUT
- **Lean Chapter**: CH-BST
- **Lean Section**: N/A
- **Rationale**: Introduces no taxonomy items in BST taxonomy. Signal is TANGENTIAL + CORE-THM (for Completeness). Dedekind cut construction is elegant but tangential to our taxonomy which does not include ℝ or the Completeness Property.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: `\begin{defn}[Cut]` — tangential; `\begin{thm}[realcompleteness]` — tangential to BST
  - Prose: cut all
  - Examples: cut all
  - Proofs: cut all

---

### sfr/arith/ref — Some Philosophical Reflections
- **Action**: CUT
- **Lean Chapter**: CH-BST
- **Lean Section**: N/A
- **Rationale**: Introduces no taxonomy items. Signal is PEDAGOGICAL + TANGENTIAL. Pure meta-commentary on the arithmetization project. No formal content.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: N/A (no formal items)
  - Prose: cut all
  - Examples: cut all
  - Proofs: N/A

---

### sfr/arith/check — Ordered Rings and Fields
- **Action**: CUT
- **Lean Chapter**: CH-BST
- **Lean Section**: N/A
- **Rationale**: Introduces no taxonomy items. Signal is TANGENTIAL + STEPPING-STONE. Algebraic structure definitions (ring, field) are GAP-CANDIDATES for an algebra domain but outside BST taxonomy scope. Technical verification of arithmetization details.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: commutative ring, ordered ring, ordered field definitions — all tangential to BST
  - Prose: cut all
  - Examples: cut all
  - Proofs: cut all

---

### sfr/arith/cauchy — Appendix: the Reals as Cauchy Sequences
- **Action**: CUT
- **Lean Chapter**: CH-BST
- **Lean Section**: N/A
- **Rationale**: Introduces no taxonomy items. Signal is TANGENTIAL + PEDAGOGICAL. Alternative construction of ℝ via Cauchy sequences. Demonstrates PRIM-BST011 in action but the construction itself is outside taxonomy scope.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: `\begin{defn}[def:CauchySequence]` — tangential; `\begin{thm}[thm:cauchyorderedfield]` — tangential; Completeness theorem — tangential
  - Prose: cut all
  - Examples: cut all
  - Proofs: cut all

---

## Summary

### Action Counts

| Action | Count |
|--------|-------|
| KEEP | 12 |
| CONDENSE | 13 |
| MERGE-INTO | 4 |
| ABSORB | 3 |
| CUT | 16 |
| **Total** | **48** |

### Detail by Action

**KEEP (12):** sfr/set/bas, sfr/set/sub, sfr/set/uni, sfr/rel/set, sfr/rel/prp, sfr/rel/eqv, sfr/fun/bas, sfr/fun/kin, sfr/fun/inv, sfr/fun/cmp, sfr/siz/zigzag, sfr/siz/car

**ABSORB (3):** sfr/set/pai (absorbs PRIM-BST010 from sfr/set/imp), sfr/siz/enm (absorbs sfr/siz/enm-alt), sfr/siz/nen (absorbs sfr/siz/nen-alt)

**CONDENSE (13):** sfr/set/imp, sfr/rel/ord, sfr/rel/tre, sfr/rel/ops, sfr/fun/rel, sfr/ind/int, sfr/siz/pai, sfr/siz/red, sfr/siz/equ, sfr/siz/sb, sfr/infinite/hilbert, sfr/infinite/dedekind, sfr/infinite/card-sb

**MERGE-INTO (4):** sfr/siz/enm-alt → sfr/siz/enm, sfr/siz/nen-alt → sfr/siz/nen, sfr/siz/red-alt → sfr/siz/red, sfr/infinite/induction → sfr/ind/int

**CUT (16):** sfr/set/rus, sfr/set/prf, sfr/rel/ref, sfr/rel/grp, sfr/fun/iso, sfr/fun/par, sfr/siz/int, sfr/siz/pai-alt, sfr/infinite/dedekindsproof, sfr/arith/int, sfr/arith/rat, sfr/arith/real, sfr/arith/cuts, sfr/arith/ref, sfr/arith/check, sfr/arith/cauchy

### BST Taxonomy Coverage (24 items)

| Taxonomy ID | Authoritative Section | Lean Section |
|-------------|----------------------|--------------|
| PRIM-BST001 (Set / Extensionality) | sfr/set/bas | BST.1 |
| PRIM-BST002 (Membership ∈) | sfr/set/bas | BST.1 |
| PRIM-BST003 (Subset ⊆) | sfr/set/sub | BST.1 |
| PRIM-BST004 (Empty Set ∅) | sfr/set/bas | BST.1 |
| PRIM-BST005 (Union/Intersection) | sfr/set/uni | BST.1 |
| PRIM-BST006 (Ordered Pair) | sfr/set/pai | BST.1 |
| PRIM-BST007 (Cartesian Product) | sfr/set/pai | BST.1 |
| PRIM-BST008 (Binary Relation) | sfr/rel/set | BST.2 |
| PRIM-BST009 (Function) | sfr/fun/bas | BST.3 |
| PRIM-BST010 (Finite Sequence A*) | sfr/set/pai (primary) | BST.4 |
| PRIM-BST011 (Infinite Sequence A^ω) | sfr/set/imp | BST.4 |
| PRIM-BST012 (Natural Number ℕ) | sfr/set/imp | BST.4 |
| PRIM-BST013 (Mathematical Induction) | sfr/ind/int (primary) | BST.5 |
| PRIM-BST014 (Structural Induction) | sfr/ind/int | BST.5 |
| PRIM-BST015 (Power Set 𝒫) | sfr/set/sub | BST.1 |
| PRIM-BST016 (Enumerability) | sfr/siz/enm (primary) | BST.6 |
| DEF-BST001 (Injection) | sfr/fun/kin | BST.3 |
| DEF-BST002 (Surjection) | sfr/fun/kin | BST.3 |
| DEF-BST003 (Bijection) | sfr/fun/kin | BST.3 |
| DEF-BST004 (Equivalence Relation) | sfr/rel/eqv | BST.2 |
| DEF-BST005 (Partial Order) | sfr/rel/ord | BST.2 |
| THM-BST001 (Cantor's Theorem) | sfr/siz/car (primary) | BST.6 |
| THM-BST002 (ℕ countably infinite) | sfr/siz/enm | BST.6 |
| THM-BST003 (ℕ×ℕ enumerable) | sfr/siz/zigzag | BST.6 |

**All 24 BST taxonomy items (PRIM-BST001–016, DEF-BST001–005, THM-BST001–003) have exactly one authoritative section.**

### COMPRESSION-TARGETs Resolved

1. **PRIM-BST010 (Sequence)**: Primary = sfr/set/pai; sfr/set/imp retains PRIM-BST011/012 but its A* content absorbed into sfr/set/pai.
2. **PRIM-BST013 (Induction)**: Primary = sfr/ind/int; sfr/infinite/induction merges into sfr/ind/int.
3. **PRIM-BST016 (Cardinality)**: Primary = sfr/siz/enm; sfr/siz/enm-alt merges into sfr/siz/enm.
4. **THM-BST001 (Cantor naive)**: Primary = sfr/siz/car; sfr/siz/nen provides stepping stones (absorbed); sfr/siz/nen-alt merges into sfr/siz/nen.

---

## CH-SYN: Syntax + CH-SEM: Semantics

### Architectural Decision: FOL-First, PL as Fragment (A2)

The lean text develops FOL directly. PL sections are merged into their FOL counterparts; PL-specific content survives only as remarks or specialization notes. The 9 `fol/int/` introductory sections are all CUT (purely pedagogical overviews with no formal items).

---

### PL syntax-and-semantics

---

### pl/syn/pre — Preliminaries
- **Action**: CONDENSE
- **Lean Chapter**: CH-SYN
- **Lean Section**: SYN.6: Theorems
- **Rationale**: Signal is CORE-THM. Introduces THM-SYN001 (unique readability, PL version) and DEF-SYN005 (structural induction on PL formulas), plus DEF-SYN001 (uniform substitution). However, under A2 FOL-first policy, the FOL versions in fol/syn/unq (THM-SYN001) and fol/syn/frm (DEF-SYN005) are authoritative. PL induction principle and unique readability survive only as remarks noting PL as a special case. DEF-SYN001 (uniform substitution) is PL-specific and survives as a remark in fol/syn/sub.
- **Content Directives**:
  - Formal items to preserve: `thm:induction` (PRIM-SYN005 / DEF-SYN005 PL version) — as remark in fol/syn/frm noting PL restriction; Unique Readability prop (THM-SYN001 PL version) — as remark in fol/syn/unq; `defn:Uniform Substitution` (DEF-SYN001) — as remark in fol/syn/sub
  - Formal items to drop: `prop:balanced` — OL-ONLY technical lemma; `prop:noinit` — OL-ONLY technical lemma (both are infrastructure for PL unique readability proof, subsumed by FOL version)
  - Prose: replace with cross-ref to fol/syn/frm (induction), fol/syn/unq (unique readability), fol/syn/sub (substitution)
  - Examples: cut all
  - Proofs: cut — FOL versions in fol/syn/unq are authoritative

---

### pl/syn/int — Introduction
- **Action**: CUT
- **Lean Chapter**: CH-SYN
- **Lean Section**: N/A
- **Rationale**: Signal is PEDAGOGICAL. No formal items. Expository overview of truth-functional PL. Under A2 FOL-first policy, the lean text opens with FOL directly; PL motivation is unnecessary.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: N/A (no formal items)
  - Prose: cut all
  - Examples: cut all
  - Proofs: N/A

---

### pl/syn/fml — Propositional Formulas
- **Action**: MERGE-INTO:fol/syn/frm
- **Lean Chapter**: CH-SYN
- **Lean Section**: SYN.2: Terms and Formulas
- **Rationale**: Signal is CORE-DEF. Introduces PRIM-SYN002 (propositional variable), PRIM-SYN003 (logical connective), PRIM-SYN012 (formula, PL version), AX-SYN003 (formation rules for PL). Under A2 PL->FOL merge map, PL formula BNF survives as a remark on the FOL fragment (propositional fragment = no quantifiers, no predicate/function symbols, atomic formulas are propositional variables).
- **Content Directives**:
  - Formal items to preserve: `defn:formulas` (AX-SYN003) — as remark in fol/syn/frm noting PL as the quantifier-free, variable-only fragment of FOL
  - Formal items to drop: `defn:Syntactic identity` — OL-ONLY, already defined in fol/syn/frm; defined operators section — OL-ONLY abbreviations, already covered in fol/syn/frm
  - Prose: replace with cross-ref to fol/syn/frm + one-line remark: "PL formulas are the fragment of FOL with no quantifiers, function symbols, or predicate symbols; atomic formulas are propositional variables."
  - Examples: cut all
  - Proofs: N/A

---

### pl/syn/fseq — Formation Sequences (PL)
- **Action**: MERGE-INTO:fol/syn/fseq
- **Lean Chapter**: CH-SYN
- **Lean Section**: SYN.2: Terms and Formulas
- **Rationale**: Signal is STEPPING-STONE. Introduces DEF-SYN006 (structural recursion via formation sequences, PL version). Under A2 PL->FOL merge map, the PL formation sequence content adds nothing beyond the FOL version in fol/syn/fseq. The structural recursion concept is already covered there.
- **Content Directives**:
  - Formal items to preserve: none standalone — DEF-SYN006 is authoritatively defined in fol/syn/fseq
  - Formal items to drop: `defn:fseq-frm` — redundant with FOL version; `prop:formed` — redundant; `lem:fseq-init` — redundant; `thm:fseq-frm-equiv` — redundant
  - Prose: replace with cross-ref to fol/syn/fseq
  - Examples: cut all
  - Proofs: cut all

---

### pl/syn/val — Valuations and Satisfaction
- **Action**: MERGE-INTO:fol/syn/sat
- **Lean Chapter**: CH-SEM
- **Lean Section**: SEM.2: Satisfaction and Truth
- **Rationale**: Signal is CORE-DEF. Introduces PRIM-SEM015 (truth-value assignment/valuation), PRIM-SEM007 (satisfaction, PL version), DEF-SEM001 (Tarski satisfaction, PL version). Under A2 PL->FOL merge map, truth-value assignment definition survives as a SEM specialization remark in fol/syn/sat: "For PL, a valuation v: PVar -> {T,F} replaces the structure+variable-assignment pair."
- **Content Directives**:
  - Formal items to preserve: `defn:valuations` (PRIM-SEM015) — as remark in fol/syn/sat noting PL specialization; `defn:satisfaction` (PRIM-SEM007/DEF-SEM001 PL version) — as remark noting PL satisfaction is the quantifier-free fragment of FOL satisfaction
  - Formal items to drop: `defn:evaluation function` — the evaluation function is OL-ONLY pedagogical scaffolding (satisfaction subsumes it); `thm:LocalDetermination` (THM-SEM002 PL version) — subsumed by fol/syn/ext extensionality; `prop:sat-value` — OL-ONLY equivalence
  - Prose: replace with cross-ref to fol/syn/sat + one remark paragraph on PL specialization
  - Examples: cut all (truth tables are pedagogical)
  - Proofs: cut all

---

### pl/syn/sem — Semantic Notions (PL)
- **Action**: MERGE-INTO:fol/syn/sem
- **Lean Chapter**: CH-SEM
- **Lean Section**: SEM.3: Validity and Consequence
- **Rationale**: Signal is CORE-DEF. Introduces DEF-SEM002 (satisfiable, PL version), DEF-SEM009 (tautology/PL validity), DEF-SEM010 (PL consequence). Under A2 PL->FOL merge map, DEF-SEM009 (tautology) and DEF-SEM010 (PL consequence) survive as specialization remarks in fol/syn/sem.
- **Content Directives**:
  - Formal items to preserve: DEF-SEM009 (tautology) — as remark in fol/syn/sem: "A tautology is a formula valid under all valuations (PL specialization of FOL validity)"; DEF-SEM010 (PL consequence) — as remark: "PL entailment is FOL entailment restricted to propositional structures"
  - Formal items to drop: DEF-SEM002 (satisfiable) — already defined in fol/syn/sem; OL-ONLY: unsatisfiable, contingent — pedagogical; `prop:semanticalfacts` — OL-ONLY properties; `prop:entails-unsat` — OL-ONLY; `thm:sem-deduction` — OL-ONLY (FOL version in fol/syn/sem is authoritative)
  - Prose: replace with cross-ref to fol/syn/sem + remark on PL-as-fragment specialization
  - Examples: cut all
  - Proofs: cut all

---

### pl/prp/snd — Soundness of Propositional Logic
- **Action**: CUT
- **Lean Chapter**: N/A (DEDUCTION domain)
- **Lean Section**: N/A
- **Rationale**: Signal is TANGENTIAL. Domain is DEDUCTION (metatheory boundary), outside SYN+SEM scope. Requires proof system ($\Proves$) which is not defined in syntax-and-semantics chapters. Will be handled in DED domain compression (Step 3).
- **Content Directives**:
  - Formal items to preserve: none (deferred to DED)
  - Formal items to drop: `thm:soundness` — requires proof system; unnamed corollary — requires proof system
  - Prose: cut all
  - Examples: cut all
  - Proofs: cut all

---

### pl/prp/com — Completeness of Propositional Logic
- **Action**: CUT
- **Lean Chapter**: N/A (DEDUCTION domain)
- **Lean Section**: N/A
- **Rationale**: Signal is TANGENTIAL. Domain is DEDUCTION (metatheory boundary), outside SYN+SEM scope. Requires proof system ($\Proves$) which is not defined in syntax-and-semantics chapters. Will be handled in DED domain compression (Step 3).
- **Content Directives**:
  - Formal items to preserve: none (deferred to DED)
  - Formal items to drop: `def:MaxCon` — requires proof system; `lem:truth` — requires proof system; `thm:completeness` — requires proof system; unnamed corollary — requires proof system; `prop:compactness` — requires proof system
  - Prose: cut all
  - Examples: cut all
  - Proofs: cut all

---

### FOL syntax-and-semantics

---

### fol/syn/int — Introduction
- **Action**: CUT
- **Lean Chapter**: CH-SYN
- **Lean Section**: N/A
- **Rationale**: Signal is PEDAGOGICAL. No formal items. Expository overview of FOL syntax and semantics concepts. The lean text begins directly with definitions.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: N/A (no formal items)
  - Prose: cut all
  - Examples: cut all
  - Proofs: N/A

---

### fol/syn/itx — Introduction (alternate)
- **Action**: CUT
- **Lean Chapter**: CH-SYN
- **Lean Section**: N/A
- **Rationale**: Signal is PEDAGOGICAL. No formal items. Alternate syntax-only intro for syntax-only builds. Redundant with fol/syn/int and equally pedagogical.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: N/A (no formal items)
  - Prose: cut all
  - Examples: cut all
  - Proofs: N/A

---

### fol/syn/fol — First-Order Languages
- **Action**: KEEP
- **Lean Chapter**: CH-SYN
- **Lean Section**: SYN.1: Languages and Symbols
- **Rationale**: Signal is CORE-DEF. Sole defining occurrence of PRIM-SYN001 (symbol), PRIM-SYN002 (variable), PRIM-SYN003 (logical connective), PRIM-SYN004 (quantifier), PRIM-SYN005 (constant), PRIM-SYN006 (function symbol), PRIM-SYN007 (predicate symbol), PRIM-SYN008 (arity), PRIM-SYN009 (language/signature), PRIM-SYN018 (equality symbol). This is the foundational vocabulary section for the entire SYN domain.
- **Content Directives**:
  - Formal items to preserve: Full enumerated list of symbols (logical: connectives, quantifiers, identity, variables; non-logical: predicates, constants, functions; punctuation) — all 10 PRIM-SYN items
  - Formal items to drop: defined symbols section — OL-ONLY abbreviations (retain one-line remark noting convention); alternate symbols `\begin{intro}` block — pedagogical notation guide; truth-functional completeness `\begin{explain}` — pedagogical
  - Prose: compress to intro + definitions only; retain the one-sentence framing that a language $\Lang{L}$ is determined by its non-logical symbols
  - Examples: keep best 1 of 3 — retain language of arithmetic $\Lang{L}_A$ (canonical, directly instantiates PRIM-SYN005/006/007/008, references standard model); cut language of set theory and language of orders (redundant)
  - Proofs: N/A

---

### fol/syn/frm — Terms and Formulas
- **Action**: ABSORB:pl/syn/fml
- **Lean Chapter**: CH-SYN
- **Lean Section**: SYN.2: Terms and Formulas
- **Rationale**: Signal is CORE-DEF. Sole defining occurrence of PRIM-SYN010 (term), PRIM-SYN011 (atomic formula), PRIM-SYN012 (formula), AX-SYN001 (formation rules for terms), AX-SYN002 (formation rules for formulas), DEF-SYN005 (structural induction). Absorbs pl/syn/fml per A2: PL formula BNF appears as a remark on the propositional fragment.
- **Content Directives**:
  - Formal items to preserve: `defn:terms` (PRIM-SYN010, AX-SYN001); `defn:formulas` (PRIM-SYN011, PRIM-SYN012, AX-SYN002); `lem:trmind` (DEF-SYN005 for terms); `thm:frmind` (DEF-SYN005 for formulas); absorbed from pl/syn/fml: one-line remark noting PL formulas as quantifier-free fragment (AX-SYN003)
  - Formal items to drop: `defn:Syntactic identity` — OL-ONLY technical definition (retain one-line note on $\ident$ notation); defined operators section — OL-ONLY abbreviations (retain one-line remark)
  - Prose: compress to intro + definitions only; cut extended `\begin{explain}` block on inductive definition stages (pedagogical)
  - Examples: cut all (no examples in source; absorbed PL examples also cut)
  - Proofs: N/A (induction principles stated as lemmas without proof)

---

### fol/syn/fseq — Formation Sequences (FOL)
- **Action**: CONDENSE + ABSORB:{pl/syn/fseq}
- **Lean Chapter**: CH-SYN
- **Lean Section**: SYN.2: Terms and Formulas
- **Rationale**: Signal is STEPPING-STONE. Introduces DEF-SYN006 (structural recursion via formation sequences, FOL version). Alternative bottom-up construction. The equivalence theorem (thm:fseq-frm-equiv) justifies induction on formation sequence length. Useful but not essential for the core development.
- **Content Directives**:
  - Formal items to preserve: `defn:fseq-trm` (DEF-SYN006 for terms); `defn:fseq-frm` (DEF-SYN006 for formulas); `thm:fseq-frm-equiv` — statement only (equivalence of inductive and formation-sequence definitions)
  - Formal items to drop: `defn:string` — OL-ONLY technical definition; `prop:formed` — infrastructure (every formula has formation sequence); `lem:fseq-init` — OL-ONLY technical lemma; `prop:fseq-trm-equiv` — OL-ONLY (parallel to thm:fseq-frm-equiv); `defn:minimal-fseq` — OL-ONLY; `prop:subformula-equivs` — OL-ONLY
  - Prose: compress to intro + definitions + theorem statement; cut historical note (Smullyan reference)
  - Examples: cut all
  - Proofs: cut — the full proof of thm:fseq-frm-equiv is infrastructure; state as remark "proof by strong induction on formation sequence length"

---

### fol/syn/unq — Unique Readability
- **Action**: KEEP
- **Lean Chapter**: CH-SYN
- **Lean Section**: SYN.6: Theorems
- **Rationale**: Signal is CORE-THM. Sole defining occurrence of THM-SYN001 (unique readability for formulas). Essential metatheoretic property justifying all recursive definitions on formulas. THM-SYN002 (unique readability for terms) is implicit.
- **Content Directives**:
  - Formal items to preserve: `prop:Unique Readability` (THM-SYN001) — full statement; `prop:unique-atomic` — supporting proposition (unique parsing of atomic formulas)
  - Formal items to drop: balanced parentheses lemma — OL-ONLY infrastructure; `defn:Proper prefix` — OL-ONLY technical definition; `lem:no-prefix` — OL-ONLY technical lemma (all three are proof infrastructure for the main theorem; retain as sketch steps)
  - Prose: preserve the introductory explain block (it motivates why unique readability matters — the ambiguity example is essential for understanding); compress technical detail
  - Examples: cut the ambiguity example in explain block — actually preserve as it IS the motivation
  - Proofs: preserve sketch only — outline the structure: (1) balanced parentheses, (2) no proper prefix is a formula, (3) unique atomic parsing, (4) main result by prefix-freeness argument

---

### fol/syn/mai — Main Operator of a Formula
- **Action**: CONDENSE
- **Lean Chapter**: CH-SYN
- **Lean Section**: SYN.2: Terms and Formulas
- **Rationale**: Signal is STEPPING-STONE. Introduces OL-ONLY concept (main operator). No taxonomy items, but the concept is used in subsequent definitions and proofs (e.g., satisfaction definition refers to "main connective"). Depends on THM-SYN001 (unique readability).
- **Content Directives**:
  - Formal items to preserve: `def:main-op` — definition of main operator (useful vocabulary for formula structure discussion)
  - Formal items to drop: `tab:main-op` — OL-ONLY classification table (pedagogical; the definition itself suffices)
  - Prose: compress to intro + definition only; cut the extended explain block about recursive definitions being well-defined (pedagogical — THM-SYN001 already justifies this)
  - Examples: cut all
  - Proofs: N/A

---

### fol/syn/sbf — Subformulas
- **Action**: KEEP
- **Lean Chapter**: CH-SYN
- **Lean Section**: SYN.2: Terms and Formulas
- **Rationale**: Signal is CORE-DEF. Sole defining occurrence of PRIM-SYN017 (subformula). Also implicitly introduces DEF-SYN008 (subterm). The subformula relation is essential for structural reasoning (induction, satisfaction, proof theory).
- **Content Directives**:
  - Formal items to preserve: `defn:Immediate subformula` (PRIM-SYN017 direct); `defn:Proper subformula` (PRIM-SYN017 recursive); `defn:subformula` (PRIM-SYN017)
  - Formal items to drop: `prop:subfrm-trans` — OL-ONLY (transitivity of subformula relation; state as one-line remark); `prop:count-subfrms` — OL-ONLY (counting bound; pedagogical)
  - Prose: preserve intro + all three definitions; compress the explain block on recursive vs explicit definitions (pedagogical)
  - Examples: cut all
  - Proofs: N/A

---

### fol/syn/fvs — Free Variables and Sentences
- **Action**: KEEP
- **Lean Chapter**: CH-SYN
- **Lean Section**: SYN.3: Variables and Scope
- **Rationale**: Signal is CORE-DEF. Sole defining occurrence of PRIM-SYN014 (free occurrence), PRIM-SYN015 (bound occurrence), PRIM-SYN016 (scope), PRIM-SYN013 (sentence), and DEF-SYN003 (free variables FV(phi)). All five are essential for semantics (satisfaction depends on free variables).
- **Content Directives**:
  - Formal items to preserve: `defn:free-occ` (PRIM-SYN014); `defn:Bound Variables` (PRIM-SYN015); `defn:Scope` (PRIM-SYN016); `defn:Sentence` (PRIM-SYN013)
  - Formal items to drop: none — all formal items map to taxonomy primitives
  - Prose: preserve — definitions require their surrounding context for clarity
  - Examples: keep the worked example (scope diagram with nested quantifiers) — canonical, directly instantiates PRIM-SYN014/015/016, shows binding ambiguity
  - Proofs: N/A

---

### fol/syn/sub — Substitution
- **Action**: KEEP
- **Lean Chapter**: CH-SYN
- **Lean Section**: SYN.4: Substitution
- **Rationale**: Signal is CORE-DEF. Sole defining occurrence of DEF-SYN001 (substitution, FOL version). Also introduces "free for" condition (capture-avoidance). Essential for quantifier rules in proof theory and the substitution lemma (THM-SYN003).
- **Content Directives**:
  - Formal items to preserve: `defn:Substitution in a term` (DEF-SYN001 for terms); `defn:free for` — capture-avoidance condition (essential for correct substitution); `defn:Substitution in a formula` (DEF-SYN001 for formulas)
  - Formal items to drop: none — all formal items are essential
  - Prose: preserve — the explain block on variable capture is essential for understanding the "free for" condition; compress the $!A(x)$/$!A(t)$ notation convention to one sentence
  - Examples: keep the 2-item "free for" example (shows both positive and negative cases; canonical)
  - Proofs: N/A

---

### fol/syn/its — Introduction (semantics)
- **Action**: CUT
- **Lean Chapter**: CH-SEM
- **Lean Section**: N/A
- **Rationale**: Signal is PEDAGOGICAL. No formal items. Expository overview of FOL semantics concepts (structures, variable assignments, satisfaction, validity). The lean text proceeds directly to definitions.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: N/A (no formal items)
  - Prose: cut all
  - Examples: cut all
  - Proofs: N/A

---

### fol/syn/str — Structures for First-order Languages
- **Action**: KEEP
- **Lean Chapter**: CH-SEM
- **Lean Section**: SEM.1: Structures
- **Rationale**: Signal is CORE-DEF. Sole defining occurrence of PRIM-SEM001 (structure), PRIM-SEM002 (domain), PRIM-SEM003 (interpretation function). Foundation of all semantic notions.
- **Content Directives**:
  - Formal items to preserve: `defn:structures` (PRIM-SEM001, PRIM-SEM002, PRIM-SEM003) — full 4-part definition (domain, interpretation of constants, predicates, functions)
  - Formal items to drop: none
  - Prose: preserve the introductory explain block (clarifies structure/interpretation/model terminology); compress the digress block on empty domains and free logic to one-line footnote
  - Examples: keep best 1 of 2 — retain standard model of arithmetic $\Struct{N}$ (canonical, directly instantiates all three PRIM-SEM items, connects to $\Lang{L}_A$ from fol/syn/fol); cut hereditarily finite sets example (tangential)
  - Proofs: N/A

---

### fol/syn/cov — Covered Structures
- **Action**: CONDENSE
- **Lean Chapter**: CH-SEM
- **Lean Section**: SEM.1: Structures
- **Rationale**: Signal is STEPPING-STONE. Introduces PRIM-SEM006 (term valuation for closed terms) and OL-ONLY concept of covered structure. The closed-term valuation is a special case of the general term valuation in fol/syn/sat, but is defined here as a stepping stone. Covered structures are used in completeness proofs.
- **Content Directives**:
  - Formal items to preserve: `defn:value of closed terms` (PRIM-SEM006) — stepping stone to general term valuation; state as preliminary definition
  - Formal items to drop: `defn:Covered structure` — OL-ONLY concept (compress to one-line remark: "A structure is covered if every domain element is the value of some closed term")
  - Prose: compress to intro + definition only
  - Examples: cut all (extended computation example is pedagogical)
  - Proofs: N/A

---

### fol/syn/sat — Satisfaction of a Formula in a Structure
- **Action**: ABSORB:pl/syn/val
- **Lean Chapter**: CH-SEM
- **Lean Section**: SEM.2: Satisfaction and Truth
- **Rationale**: Signal is CORE-DEF. Sole defining occurrence of PRIM-SEM004 (variable assignment), PRIM-SEM005 (x-variant), PRIM-SEM006 (term valuation, general), PRIM-SEM007 (satisfaction), DEF-SEM001 (Tarski satisfaction definition). Central definition of the entire semantic theory. Absorbs pl/syn/val per A2: PL valuation and satisfaction appear as specialization remarks.
- **Content Directives**:
  - Formal items to preserve: `defn:Variable Assignment` (PRIM-SEM004); `defn:value of Terms` (PRIM-SEM006 general); `defn:x-Variant` (PRIM-SEM005); unnamed defn for $\Subst{s}{m}{x}$ (PRIM-SEM005 specific); `defn:satisfaction` (PRIM-SEM007, DEF-SEM001) — full inductive definition; absorbed from pl/syn/val: one-paragraph remark noting PL specialization (PRIM-SEM015: valuation v: PVar -> {T,F} replaces structure+assignment)
  - Formal items to drop: `prop:sat-ex` — OL-ONLY (existential quantifier property for defEx variant); `prop:sat-all` — OL-ONLY (universal quantifier property for defAll variant)
  - Prose: preserve the explain blocks before variable assignment and before satisfaction definition (they motivate why assignments are needed); compress the explain block after satisfaction definition; cut the explain blocks for defined quantifiers (defEx/defAll variants)
  - Examples: cut the large worked example — pedagogical (4 pages of step-by-step computation)
  - Proofs: N/A

---

### fol/syn/ext — Extensionality
- **Action**: KEEP
- **Lean Chapter**: CH-SEM
- **Lean Section**: SEM.7: Theorems
- **Rationale**: Signal is CORE-THM. Sole defining occurrence of THM-SEM002 (coincidence lemma / extensionality) and THM-SYN003 (substitution lemma). Both are key metatheoretic results: extensionality ensures satisfaction depends only on relevant symbols, and the substitution lemma connects syntactic substitution with semantic variable reassignment.
- **Content Directives**:
  - Formal items to preserve: `prop:extensionality` (THM-SEM002); `cor:extensionality-sent` (THM-SEM002 for sentences); `prop:ext-terms` (THM-SYN003 for terms); `prop:ext-formulas` (THM-SYN003 for formulas)
  - Formal items to drop: none — all four items are taxonomy theorems or their direct corollaries
  - Prose: preserve introductory explain block (clarifies what extensionality means); preserve closing explain block (clarifies the substitution-vs-assignment equivalence); compress
  - Examples: cut all
  - Proofs: preserve sketch only for `prop:extensionality` — "by induction on $!A$, using induction on terms for the base case"; preserve sketch only for `prop:ext-terms` — "by induction on $t$" (4-case structure); `prop:ext-formulas` — note "exercise, parallel to ext-terms"

---

### fol/syn/sem — Semantic Notions (FOL)
- **Action**: ABSORB:pl/syn/sem
- **Lean Chapter**: CH-SEM
- **Lean Section**: SEM.3: Validity and Consequence
- **Rationale**: Signal is CORE-DEF. Sole defining occurrence of PRIM-SEM009 (logical validity), PRIM-SEM010 (logical consequence), PRIM-SEM011 (model), DEF-SEM002 (satisfiable), DEF-SEM004 (semantic consistency). Absorbs pl/syn/sem per A2: DEF-SEM009 (tautology) and DEF-SEM010 (PL consequence) appear as PL specialization remarks.
- **Content Directives**:
  - Formal items to preserve: `defn:Validity` (PRIM-SEM009); `defn:Entailment` (PRIM-SEM010); `defn:Satisfiability` (DEF-SEM002, PRIM-SEM011); absorbed from pl/syn/sem: DEF-SEM009 (tautology) as remark — "A PL tautology is a formula valid under all valuations; this specializes FOL validity to propositional structures"; DEF-SEM010 (PL consequence) as remark — "PL entailment specializes FOL entailment to propositional structures"
  - Formal items to drop: validity characterization prop — OL-ONLY basic property; `prop:entails-unsat` — OL-ONLY (entailment via unsatisfiability; state as one-line remark); monotonicity prop — OL-ONLY; `thm:sem-deduction` — OL-ONLY (semantic deduction theorem; state as one-line remark); `prop:quant-terms` — OL-ONLY (quantifier instantiation/generalization)
  - Prose: preserve introductory explain block (clarifies validity as logical truth); compress remainder to definitions + absorbed PL remarks
  - Examples: cut all
  - Proofs: cut all — the propositions are either exercises or straightforward

---

### fol/syn/ass — Variable Assignments
- **Action**: CONDENSE
- **Lean Chapter**: CH-SEM
- **Lean Section**: SEM.2: Satisfaction and Truth
- **Rationale**: Signal is CORE-THM. Introduces PRIM-SEM008 (truth in a structure for sentences) and proves that satisfaction depends only on free variables. The independence results (prop:valindep, prop:satindep) justify the sentence-level satisfaction definition. Key metatheoretic infrastructure.
- **Content Directives**:
  - Formal items to preserve: `prop:satindep` — satisfaction depends only on free variables (key metatheoretic result); `cor:sat-sentence` — sentences are assignment-independent; `defn:satisfaction` for sentences (PRIM-SEM008); `defn:sat` for sets (PRIM-SEM011 alternative formulation); `prop:sentence-sat-true` — equivalence of sentence satisfaction notions
  - Formal items to drop: `prop:valindep` — infrastructure (term value depends only on variables in term); compress to one-line remark; `prop:sat-quant` — OL-ONLY (quantifier satisfaction for sentences); compress to one-line remark
  - Prose: compress to intro + definitions + theorem statements; cut the extended explain block motivating why assignments are over all variables (pedagogical — already explained in fol/syn/sat)
  - Examples: cut all
  - Proofs: preserve sketch only for `prop:satindep` — "by induction on complexity of $!A$; base case uses prop:valindep; quantifier case uses x-variant construction"; cut full detailed proof (10+ cases)

---

### fol/int/ — First-Order Logic Introduction (9 sections)

All 9 `fol/int/` sections are purely pedagogical introductions with no formal items. Per the architectural decision, all are CUT.

---

### fol/int/fol — First-Order Logic
- **Action**: CUT
- **Lean Chapter**: N/A
- **Lean Section**: N/A
- **Rationale**: Signal is PEDAGOGICAL. No formal items. Chapter-opening overview of FOL: syntax, semantics, deduction.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: N/A (no formal items)
  - Prose: cut all
  - Examples: cut all
  - Proofs: N/A

---

### fol/int/syn — Syntax
- **Action**: CUT
- **Lean Chapter**: N/A
- **Lean Section**: N/A
- **Rationale**: Signal is PEDAGOGICAL. No formal items. Informal syntax overview.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: N/A (no formal items)
  - Prose: cut all
  - Examples: cut all
  - Proofs: N/A

---

### fol/int/fml — Formulas
- **Action**: CUT
- **Lean Chapter**: N/A
- **Lean Section**: N/A
- **Rationale**: Signal is PEDAGOGICAL. No formal items (simplified toy definition not in taxonomy). Simplified formula definition for toy language; full definition in fol/syn/frm.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: simplified formula definition — pedagogical toy version
  - Prose: cut all
  - Examples: cut all
  - Proofs: N/A

---

### fol/int/snt — Sentences
- **Action**: CUT
- **Lean Chapter**: N/A
- **Lean Section**: N/A
- **Rationale**: Signal is PEDAGOGICAL. No formal items. Sketches free/bound variable definitions informally; full definitions in fol/syn/fvs.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: N/A (no formal items)
  - Prose: cut all
  - Examples: cut all
  - Proofs: N/A

---

### fol/int/sub — Substitution
- **Action**: CUT
- **Lean Chapter**: N/A
- **Lean Section**: N/A
- **Rationale**: Signal is PEDAGOGICAL. No formal items. Motivates substitution informally; full definition in fol/syn/sub.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: N/A (no formal items)
  - Prose: cut all
  - Examples: cut all
  - Proofs: N/A

---

### fol/int/sat — Satisfaction
- **Action**: CUT
- **Lean Chapter**: N/A
- **Lean Section**: N/A
- **Rationale**: Signal is PEDAGOGICAL. No formal items. Sketches satisfaction for toy language; full definition in fol/syn/sat.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: N/A (no formal items)
  - Prose: cut all
  - Examples: cut all
  - Proofs: N/A

---

### fol/int/sem — Semantic Notions
- **Action**: CUT
- **Lean Chapter**: N/A
- **Lean Section**: N/A
- **Rationale**: Signal is PEDAGOGICAL. No formal items. Informal validity/entailment/satisfiability overview; full definitions in fol/syn/sem.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: N/A (no formal items)
  - Prose: cut all
  - Examples: cut all
  - Proofs: N/A

---

### fol/int/mod — Models and Theories
- **Action**: CUT
- **Lean Chapter**: N/A
- **Lean Section**: N/A
- **Rationale**: Signal is PEDAGOGICAL. No formal items. Informal model theory overview; formal model definition in fol/syn/sem.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: N/A (no formal items)
  - Prose: cut all
  - Examples: cut all
  - Proofs: N/A

---

### fol/int/scp — Soundness and Completeness
- **Action**: CUT
- **Lean Chapter**: N/A
- **Lean Section**: N/A
- **Rationale**: Signal is PEDAGOGICAL. No formal items. Informal overview of derivation systems, soundness, completeness. DED domain content; will be handled in Step 3.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: N/A (no formal items)
  - Prose: cut all
  - Examples: cut all
  - Proofs: N/A

---

## Summary: CH-SYN + CH-SEM Compression

### Action Counts

| Action | Count |
|--------|-------|
| KEEP | 7 |
| CONDENSE | 5 |
| MERGE-INTO | 4 |
| ABSORB | 3 |
| CUT | 15 |
| **Total** | **34** |

### Detail by Action

**KEEP (7):** fol/syn/fol, fol/syn/unq, fol/syn/sbf, fol/syn/fvs, fol/syn/sub, fol/syn/str, fol/syn/ext

**ABSORB (3):** fol/syn/frm (absorbs pl/syn/fml), fol/syn/sat (absorbs pl/syn/val), fol/syn/sem (absorbs pl/syn/sem)

**CONDENSE (5):** pl/syn/pre, fol/syn/fseq, fol/syn/mai, fol/syn/cov, fol/syn/ass

**MERGE-INTO (4):** pl/syn/fml -> fol/syn/frm, pl/syn/fseq -> fol/syn/fseq, pl/syn/val -> fol/syn/sat, pl/syn/sem -> fol/syn/sem

**CUT (15):** pl/syn/int, pl/prp/snd, pl/prp/com, fol/syn/int, fol/syn/itx, fol/syn/its, fol/int/fol, fol/int/syn, fol/int/fml, fol/int/snt, fol/int/sub, fol/int/sat, fol/int/sem, fol/int/mod, fol/int/scp

### SYN Taxonomy Coverage (from these sections)

| Taxonomy ID | Authoritative Section | Lean Section |
|-------------|----------------------|--------------|
| PRIM-SYN001 (Symbol) | fol/syn/fol | SYN.1 |
| PRIM-SYN002 (Variable) | fol/syn/fol | SYN.1 |
| PRIM-SYN003 (Logical Connective) | fol/syn/fol | SYN.1 |
| PRIM-SYN004 (Quantifier) | fol/syn/fol | SYN.1 |
| PRIM-SYN005 (Constant) | fol/syn/fol | SYN.1 |
| PRIM-SYN006 (Function Symbol) | fol/syn/fol | SYN.1 |
| PRIM-SYN007 (Predicate Symbol) | fol/syn/fol | SYN.1 |
| PRIM-SYN008 (Arity) | fol/syn/fol | SYN.1 |
| PRIM-SYN009 (Language/Signature) | fol/syn/fol | SYN.1 |
| PRIM-SYN010 (Term) | fol/syn/frm | SYN.2 |
| PRIM-SYN011 (Atomic Formula) | fol/syn/frm | SYN.2 |
| PRIM-SYN012 (Formula) | fol/syn/frm | SYN.2 |
| PRIM-SYN013 (Sentence) | fol/syn/fvs | SYN.3 |
| PRIM-SYN014 (Free Occurrence) | fol/syn/fvs | SYN.3 |
| PRIM-SYN015 (Bound Occurrence) | fol/syn/fvs | SYN.3 |
| PRIM-SYN016 (Scope) | fol/syn/fvs | SYN.3 |
| PRIM-SYN017 (Subformula) | fol/syn/sbf | SYN.2 |
| PRIM-SYN018 (Equality Symbol) | fol/syn/fol | SYN.1 |
| AX-SYN001 (Term Formation) | fol/syn/frm | SYN.2 |
| AX-SYN002 (Formula Formation) | fol/syn/frm | SYN.2 |
| AX-SYN003 (PL Formation) | fol/syn/frm (remark) | SYN.2 |
| DEF-SYN001 (Substitution) | fol/syn/sub | SYN.4 |
| DEF-SYN003 (Free Variables FV) | fol/syn/fvs | SYN.3 |
| DEF-SYN005 (Structural Induction) | fol/syn/frm | SYN.2 |
| DEF-SYN006 (Formation Sequences) | fol/syn/fseq | SYN.2 |
| DEF-SYN008 (Subterm) | fol/syn/sbf | SYN.2 |
| THM-SYN001 (Unique Readability) | fol/syn/unq | SYN.6 |
| THM-SYN003 (Substitution Lemma) | fol/syn/ext | SEM.7 |

### SEM Taxonomy Coverage (from these sections)

| Taxonomy ID | Authoritative Section | Lean Section |
|-------------|----------------------|--------------|
| PRIM-SEM001 (Structure) | fol/syn/str | SEM.1 |
| PRIM-SEM002 (Domain) | fol/syn/str | SEM.1 |
| PRIM-SEM003 (Interpretation) | fol/syn/str | SEM.1 |
| PRIM-SEM004 (Variable Assignment) | fol/syn/sat | SEM.2 |
| PRIM-SEM005 (x-Variant) | fol/syn/sat | SEM.2 |
| PRIM-SEM006 (Term Valuation) | fol/syn/sat (general); fol/syn/cov (closed terms) | SEM.2 / SEM.1 |
| PRIM-SEM007 (Satisfaction) | fol/syn/sat | SEM.2 |
| PRIM-SEM008 (Truth in Structure) | fol/syn/ass | SEM.2 |
| PRIM-SEM009 (Logical Validity) | fol/syn/sem | SEM.3 |
| PRIM-SEM010 (Logical Consequence) | fol/syn/sem | SEM.3 |
| PRIM-SEM011 (Model) | fol/syn/sem | SEM.3 |
| PRIM-SEM015 (Valuation, PL) | fol/syn/sat (remark) | SEM.2 |
| DEF-SEM001 (Tarski Satisfaction) | fol/syn/sat | SEM.2 |
| DEF-SEM002 (Satisfiable) | fol/syn/sem | SEM.3 |
| DEF-SEM004 (Semantic Consistency) | fol/syn/sem | SEM.3 |
| DEF-SEM009 (Tautology, PL) | fol/syn/sem (remark) | SEM.3 |
| DEF-SEM010 (PL Consequence) | fol/syn/sem (remark) | SEM.3 |
| THM-SEM002 (Coincidence Lemma) | fol/syn/ext | SEM.7 |

### PL->FOL Merges Resolved

1. **pl/syn/fml -> fol/syn/frm**: PL formula BNF survives as remark (AX-SYN003 as FOL fragment).
2. **pl/syn/val -> fol/syn/sat**: Truth-value assignment def (PRIM-SEM015) survives as SEM specialization remark.
3. **pl/syn/sem -> fol/syn/sem**: DEF-SEM009 (tautology) and DEF-SEM010 (PL consequence) survive as specialization remarks.
4. **pl/syn/fseq -> fol/syn/fseq**: Nothing survives; structural recursion already in FOL version.
5. **pl/syn/pre**: PL induction/unique-readability subsumed by FOL versions in fol/syn/frm and fol/syn/unq.

### Note on CUT Count

The CUT count of 15 includes 9 fol/int/ sections (all purely pedagogical) + 3 PL sections (pl/syn/int, pl/prp/snd, pl/prp/com) + 3 FOL intro sections (fol/syn/int, fol/syn/itx, fol/syn/its). The high CUT ratio (44%) reflects the large proportion of pedagogical introductions and proof-system-dependent sections in the OL source material.

---

## CH-CMP: Computation

---

### Chapter: recursive-functions (cmp/rec)

### cmp/rec/int — Introduction
- **Action**: CUT
- **Lean Chapter**: CH-CMP
- **Lean Section**: N/A
- **Rationale**: Introduces no taxonomy items. Signal is PEDAGOGICAL only. Purely motivational narrative explaining why number-theoretic functions are central to computability theory. No formal definitions or theorems.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: N/A (no formal items)
  - Prose: cut all
  - Examples: cut all
  - Proofs: N/A

---

### cmp/rec/pre — Primitive Recursion
- **Action**: MERGE-INTO:cmp/rec/prf
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.1: Recursive Functions
- **Rationale**: Signal is CORE-DEF but the formal definition of PRIM-CMP002 lives in cmp/rec/prf. This section only introduces the recursion pattern informally through examples (exponentiation, addition, multiplication). The pattern $h(x,0)=f(x)$, $h(x,y+1)=g(x,y,h(x,y))$ is stated formally in cmp/rec/prf's defn:primitive-recursion.
- **Content Directives**:
  - Formal items to preserve: none standalone -- the recursion pattern is formalized in cmp/rec/prf
  - Formal items to drop: informal examples of recursion pattern -- subsumed by cmp/rec/prf
  - Prose: replace with cross-ref to cmp/rec/prf
  - Examples: cut all -- pedagogical motivating examples
  - Proofs: N/A

---

### cmp/rec/com — Composition
- **Action**: MERGE-INTO:cmp/rec/prf
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.1: Recursive Functions
- **Rationale**: Signal is CORE-DEF but the formal definition of composition is given in cmp/rec/prf (defn:composition). This section introduces it informally along with projection functions. Both are formally defined in prf.
- **Content Directives**:
  - Formal items to preserve: none standalone -- composition and projection defined formally in cmp/rec/prf
  - Formal items to drop: informal definitions -- subsumed by cmp/rec/prf
  - Prose: replace with cross-ref to cmp/rec/prf
  - Examples: cut all
  - Proofs: N/A

---

### cmp/rec/prf — Primitive Recursive Functions
- **Action**: ABSORB:cmp/rec/pre,cmp/rec/com
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.1: Recursive Functions
- **Rationale**: Sole formal defining occurrence of PRIM-CMP002 (Primitive Recursive Function). Contains defn:primitive-recursion (recursion schema), defn:composition (composition schema), and the inductive definition of the set of PR functions. Signal is CORE-DEF only. Absorbs the informal introductions from cmp/rec/pre and cmp/rec/com.
- **Content Directives**:
  - Formal items to preserve: `\begin{defn}[primitive-recursion]` (PRIM-CMP002 recursion schema); `\begin{defn}[composition]` (composition schema); `\begin{defn}` (inductive definition of PR functions: Zero, Succ, projections, closed under composition and primitive recursion)
  - Formal items to drop: `\begin{prop}` (addition is PR) -- pedagogical example; `\begin{prop}[mult-pr]` (multiplication is PR) -- pedagogical example; `\begin{ex}` ($h(0)=1, h(y+1)=2h(y)$) -- pedagogical worked example
  - Prose: compress to intro + definitions only; one sentence motivating the recursion pattern (absorbing cmp/rec/pre's intuition); one sentence on projections (absorbing cmp/rec/com)
  - Examples: cut all -- Add and Mult examples are pedagogical
  - Proofs: cut all -- pedagogical verifications

---

### cmp/rec/not — Primitive Recursion Notations
- **Action**: CUT
- **Lean Chapter**: CH-CMP
- **Lean Section**: N/A
- **Rationale**: Introduces no taxonomy items. Signal is PEDAGOGICAL only. Notational system ($\fn{Comp}_{k,n}$, $\fn{Rec}_k$) is useful for enumeration but the lean text can handle enumeration directly via coding in cmp/rec/nft.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: notational system -- pedagogical
  - Prose: cut all
  - Examples: cut all
  - Proofs: N/A

---

### cmp/rec/cmp — Primitive Recursive Functions are Computable
- **Action**: CONDENSE
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.1: Recursive Functions
- **Rationale**: Signal is CORE-THM only. The claim that every PR function is computable is a key structural fact connecting PRIM-CMP002 to PRIM-CMP001. However, the argument is informal (no formal theorem environment). Condense to a one-paragraph statement of the result.
- **Content Directives**:
  - Formal items to preserve: the claim that every primitive recursive function is computable (state as a proposition)
  - Formal items to drop: N/A (no formal items in OL)
  - Prose: compress to one paragraph stating the result with brief justification (composition and primitive recursion preserve computability)
  - Examples: cut all
  - Proofs: preserve sketch only -- 2-3 sentences on why base cases are computable and closure operations preserve computability

---

### cmp/rec/exa — Examples of Primitive Recursive Functions
- **Action**: CUT
- **Lean Chapter**: CH-CMP
- **Lean Section**: N/A
- **Rationale**: Introduces no taxonomy items. Signal is PEDAGOGICAL only. All 8 propositions are OL-ONLY examples (exp, pred, factorial, truncated subtraction, distance, max, min, closure under sums/products). These are useful for intuition but none carry taxonomy IDs.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: all 8 propositions -- pedagogical examples
  - Prose: cut all
  - Examples: cut all
  - Proofs: cut all

---

### cmp/rec/prr — Primitive Recursive Relations
- **Action**: KEEP
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.1: Recursive Functions
- **Rationale**: Sole defining occurrence of DEF-CMP003 (Characteristic Function). Signal is CORE-DEF only. Defines PR relations via characteristic functions, proves closure under Boolean operations and bounded quantification, and introduces definition by cases. These are essential machinery for all subsequent CMP results.
- **Content Directives**:
  - Formal items to preserve: `\begin{defn}` (PR relation via $\Char{R}$) -- DEF-CMP003; `\begin{prop}` (closure under Boolean ops); `\begin{prop}` (closure under bounded quantification); `\begin{prop}` (definition by cases via $\fn{cond}$)
  - Formal items to drop: none -- all are essential building blocks
  - Prose: compress to intro + definitions; retain one-line examples of equality and less-than as PR relations (canonical, uses truncated subtraction)
  - Examples: keep the equality and less-than relations as inline definitions (directly instantiate the concept)
  - Proofs: preserve full for Boolean closure (short, constructive: $\Char{\lnot P} = 1 \tsub \Char{P}$, etc.); preserve full for bounded quantification (short, uses primitive recursion on min/max); preserve sketch for definition by cases

---

### cmp/rec/bmi — Bounded Minimization
- **Action**: CONDENSE
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.1: Recursive Functions
- **Rationale**: Signal is STEPPING-STONE only. Bounded minimization ($\bmin{z<y}{R(\vec{x},z)}$) preserves primitive recursiveness and is essential infrastructure for later coding results. The contrast with unbounded minimization motivates PRIM-CMP003.
- **Content Directives**:
  - Formal items to preserve: `\begin{prop}` (bounded minimization is PR) -- essential closure property
  - Formal items to drop: none
  - Prose: compress to intro + proposition statement; one sentence contrasting with unbounded search (foreshadows PRIM-CMP003)
  - Examples: cut all
  - Proofs: preserve sketch only -- bounded minimization is definable by primitive recursion on a conditional

---

### cmp/rec/pri — Primes
- **Action**: CUT
- **Lean Chapter**: CH-CMP
- **Lean Section**: N/A
- **Rationale**: Introduces no taxonomy items. Signal is PEDAGOGICAL only. Shows divisibility, primality, and $p_x$ (the $x$-th prime) are PR. These facts are used in cmp/rec/seq for sequence coding, but can be stated as one-line remarks there rather than given a full section.
- **Content Directives**:
  - Formal items to preserve: none standalone -- note in cmp/rec/seq that primality and $p_x$ are PR
  - Formal items to drop: all applications -- pedagogical
  - Prose: cut all
  - Examples: cut all
  - Proofs: cut all

---

### cmp/rec/seq — Sequences
- **Action**: KEEP
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.5: Coding and Universality
- **Rationale**: Introduces PRIM-CMP011 (Godel Numbering) for sequences. Signal is CORE-DEF. The prime factorization coding $\tuple{a_0,\ldots,a_k} = p_0^{a_0+1} \cdots p_k^{a_k+1}$ is the foundational encoding technique used throughout CMP and INC domains. Per COMPRESSION-TARGET for PRIM-CMP011: this section provides the base coding; cmp/rec/nft is primary for the index/numbering-of-functions aspect. This section is primary for the sequence coding aspect.
- **Content Directives**:
  - Formal items to preserve: coding scheme definition ($\tuple{a_0,\ldots,a_k} = p_0^{a_0+1} \cdots p_k^{a_k+1}$); `\begin{prop}` ($\len{s}$ is PR); `\begin{prop}` ($\fn{append}$ is PR); `\begin{prop}` ($\fn{element}$ is PR); `\begin{prop}` ($\fn{concat}$ is PR); `\begin{prop}[subseq]` ($\fn{subseq}$ is PR); $\fn{sequenceBound}$ definition
  - Formal items to drop: alternative bounded-search definition of $\fn{concat}$ -- redundant with the direct primitive recursive definition; both `\begin{prob}` items -- exercises
  - Prose: preserve -- the coding scheme explanation and the Fundamental Theorem of Arithmetic justification are essential context; add one-line note that divisibility, primality, and $p_x$ are PR (absorbing essential fact from cmp/rec/pri)
  - Examples: N/A (the coding itself serves as the canonical example of PRIM-CMP011)
  - Proofs: preserve full for $\len{s}$ (shows bounded minimization technique); preserve sketch for $\fn{append}$, $\fn{element}$, $\fn{concat}$ (brief constructions)

---

### cmp/rec/tre — Trees
- **Action**: CUT
- **Lean Chapter**: CH-CMP
- **Lean Section**: N/A
- **Rationale**: Introduces no taxonomy items. Signal is PEDAGOGICAL only. Tree coding as sequences is an application of cmp/rec/seq's coding. The SubtreeSeq proposition is OL-ONLY.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: `\begin{prop}[subtreeseq]` -- OL-ONLY application
  - Prose: cut all
  - Examples: cut all
  - Proofs: cut all

---

### cmp/rec/ore — Other Recursions
- **Action**: CUT
- **Lean Chapter**: CH-CMP
- **Lean Section**: N/A
- **Rationale**: Introduces no taxonomy items. Signal is PEDAGOGICAL only. Discusses simultaneous recursion, course-of-values recursion -- all reducible to ordinary PR via sequence coding. A one-line remark can be added to cmp/rec/prf or cmp/rec/seq if needed.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: N/A (no formal items)
  - Prose: cut all
  - Examples: cut all
  - Proofs: N/A

---

### cmp/rec/npr — Non-Primitive Recursive Functions
- **Action**: CONDENSE
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.4: Diagonalization and Halting
- **Rationale**: Introduces PRIM-CMP010 (Diagonalization) applied to show PR is a strict subset of computable functions. Signal is CORE-THM only. The diagonalization argument (enumerating PR functions via codes and constructing a function that differs from each) is structurally important and motivates the need for mu-recursion.
- **Content Directives**:
  - Formal items to preserve: the result that there exist computable but non-PR functions (state as theorem)
  - Formal items to drop: Ackermann function discussion -- pedagogical elaboration
  - Prose: compress to theorem statement + proof sketch; one sentence noting this uses PRIM-CMP010 (diagonalization) on the enumeration of PR functions
  - Examples: cut all
  - Proofs: preserve sketch only -- enumerate PR functions via codes (using PRIM-CMP011), diagonalize to get a total computable function not in the list

---

### cmp/rec/par — Partial Recursive Functions
- **Action**: KEEP
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.1: Recursive Functions
- **Rationale**: Sole formal defining occurrence of PRIM-CMP003 (mu-Recursion), PRIM-CMP001 (Computable Function -- partial and total recursive), and DEF-CMP002 (Total Function -- recursive = total partial recursive). Signal is CORE-DEF only. Per COMPRESSION-TARGET for PRIM-CMP001: this section gives the mathematical (recursive function) definition; tur/mac/una gives the TM-based definition. This is primary because partial recursive functions are the most general formulation.
- **Content Directives**:
  - Formal items to preserve: definition of unbounded search $\mu x \; f(x,\vec{z})$ (PRIM-CMP003); `\begin{defn}` (partial recursive functions) -- PRIM-CMP001; `\begin{defn}[recursive-fn]` (recursive = total partial recursive) -- DEF-CMP002; notation $f(x) \fdefined$, $f(x) \fundefined$, $f(x) \simeq g(x)$
  - Formal items to drop: none
  - Prose: preserve -- the motivation for allowing partial functions and the operational intuition for unbounded search are essential context; compress the explain block about composition/PR modifications to 2-3 sentences
  - Examples: N/A
  - Proofs: N/A

---

### cmp/rec/nft — The Normal Form Theorem
- **Action**: KEEP + ABSORB:{cmp/thy/nfm}
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.5: Coding and Universality
- **Rationale**: Introduces THM-CMP004 (Kleene Normal Form), DEF-CMP005 (Index/Program), and is primary for PRIM-CMP011 (Godel Numbering -- numbering of functions via indices). Signal is CORE-THM only. Per COMPRESSION-TARGET for PRIM-CMP011: this section is primary for the function-indexing aspect (cmp/rec/seq handles sequence coding). Per COMPRESSION-TARGET for THM-CMP004: cmp/thy/nfm duplicates this; cmp/thy/smn is primary for the s-m-n part. Verified from .tex: contains `\begin{thm}[kleene-nf]` with full statement; explain block introduces index $e$ and notation $\cfind{e}$.
- **Content Directives**:
  - Formal items to preserve: `\begin{thm}[kleene-nf]` (THM-CMP004: $f(x) \simeq U(\mu s \; T(e,x,s))$ with $T$ and $U$ primitive recursive); the concept of index $e$ (DEF-CMP005); notation $\cfind{e}$
  - Formal items to drop: none
  - Prose: preserve the explain block -- it introduces the crucial concept of index and the notation $\cfind{e}$; compress to key insights: (1) every PR function has an index, (2) $T$ checks computation records, (3) $U$ extracts output, (4) only one unbounded search needed, (5) infinitely many indices per function
  - Examples: N/A
  - Proofs: N/A (theorem stated without full proof, as in OL)

---

### cmp/rec/hlt — The Halting Problem
- **Action**: MERGE-INTO:tur/und/hal
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.4: Diagonalization and Halting
- **Rationale**: Introduces PRIM-CMP008 (Halting Problem) and THM-CMP002 (halting function not recursive). Signal is CORE-THM. Per COMPRESSION-TARGET for PRIM-CMP008 and THM-CMP002: tur/und/hal is primary because it provides both the formal definition (halting function, halting problem) and the complete diagonalization proof via TM construction, plus lemma on function $s$. cmp/rec/hlt provides the recursive-functions version of the same proof. Both are complete, but tur/und/hal is more self-contained and connects to the TM model directly. The recursive-functions proof can be noted as an alternative.
- **Content Directives**:
  - Formal items to preserve: none standalone -- content subsumed by tur/und/hal
  - Formal items to drop: `\begin{thm}[halting-problem]` -- duplicate of tur/und/hal; proof via diagonalization on $\cfind{e}$ -- subsumed
  - Prose: replace with cross-ref to tur/und/hal; note in tur/und/hal that the same result holds for partial recursive functions via the same diagonalization pattern
  - Examples: cut all
  - Proofs: cut all -- proved in tur/und/hal

---

### cmp/rec/gen — General Recursive Functions
- **Action**: CUT
- **Lean Chapter**: CH-CMP
- **Lean Section**: N/A
- **Rationale**: Introduces no new taxonomy items. Signal is TANGENTIAL. Alternative characterization (general recursive = total recursive) adds no new formal content beyond PRIM-CMP001 and DEF-CMP002 already defined in cmp/rec/par.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: `\begin{defn}[general-recursive]` -- OL-ONLY alternative definition; tangential
  - Prose: cut all -- one-line remark about the equivalence can be noted in cmp/rec/par if needed
  - Examples: cut all
  - Proofs: cut all

---

### Chapter: computability-theory (cmp/thy)

### cmp/thy/int — Introduction
- **Action**: CUT
- **Lean Chapter**: CH-CMP
- **Lean Section**: N/A
- **Rationale**: Introduces PRIM-CMP012 (Universal TM) as $\fn{Un}$ and DEF-CMP004 (Enumeration) conceptually, but both are formally defined elsewhere (cmp/thy/uni and cmp/thy/eqc respectively). Signal is PEDAGOGICAL only. Narrative introduction to the chapter.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: N/A (no formal items)
  - Prose: cut all -- the notation $\cfind{k}$ and $\fn{Un}(k,x)$ are introduced formally in cmp/rec/nft and cmp/thy/uni
  - Examples: cut all
  - Proofs: N/A

---

### cmp/thy/cod — Coding Computations
- **Action**: CUT
- **Lean Chapter**: CH-CMP
- **Lean Section**: N/A
- **Rationale**: Introduces no taxonomy items. Signal is PEDAGOGICAL only. Conceptual overview of coding definitions and computations as numbers -- this is handled formally in cmp/rec/nft (Normal Form Theorem) and cmp/rec/seq (sequence coding).
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: N/A (no formal items)
  - Prose: cut all
  - Examples: cut all
  - Proofs: N/A

---

### cmp/thy/nfm — The Normal Form Theorem
- **Action**: MERGE-INTO:cmp/rec/nft
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.5: Coding and Universality
- **Rationale**: Duplicate coverage of THM-CMP004 (Kleene Normal Form). Signal is CORE-THM but REDUNDANT with cmp/rec/nft. Verified from .tex: contains `\begin{thm}[normal-form]` (same statement) plus a proof sketch and the observation about infinitely many indices. Per COMPRESSION-TARGET for THM-CMP004: cmp/rec/nft is the first occurrence and states the theorem identically. cmp/thy/nfm adds a proof sketch and uses $\cfind{e}$ as a definition -- absorb the proof sketch into cmp/rec/nft.
- **Content Directives**:
  - Formal items to preserve: none standalone -- proof sketch absorbed into cmp/rec/nft
  - Formal items to drop: `\begin{thm}[normal-form]` -- duplicate; `\begin{thm}` (infinitely many indices) -- OL-ONLY observation, note as remark in cmp/rec/nft
  - Prose: replace with cross-ref to cmp/rec/nft; absorb the definitional use of $\cfind{e}(x) \simeq U(\mu s \; T(e,x,s))$ into cmp/rec/nft
  - Examples: cut all
  - Proofs: cut -- proof sketch absorbed into cmp/rec/nft

---

### cmp/thy/smn — The s-m-n Theorem
- **Action**: KEEP
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.5: Coding and Universality
- **Rationale**: Primary defining occurrence of THM-CMP004 (s-m-n Theorem). Signal is CORE-THM only. Per COMPRESSION-TARGET for THM-CMP004: this is the dedicated section for the s-m-n component. Verified from .tex: `\begin{thm}[s-m-n]` gives the full statement with primitive recursive $s^m_n$. The s-m-n theorem is used pervasively in subsequent proofs (Rice's theorem, fixed-point theorem, totality undecidable).
- **Content Directives**:
  - Formal items to preserve: `\begin{thm}[s-m-n]` (THM-CMP004: primitive recursive $s^m_n$ such that $\cfind{s^m_n(e,a_0,\ldots,a_{m-1})}(y_0,\ldots,y_{n-1}) \simeq \cfind{e}(a_0,\ldots,a_{m-1},y_0,\ldots,y_{n-1})$)
  - Formal items to drop: none
  - Prose: preserve the explain block about $s^m_n$ acting on programs (essential operational intuition); compress to 2-3 sentences
  - Examples: N/A
  - Proofs: N/A (stated without proof, as in OL)

---

### cmp/thy/uni — The Universal Partial Computable Function
- **Action**: CONDENSE
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.5: Coding and Universality
- **Rationale**: Introduces PRIM-CMP012 (Universal TM) formally as $\fn{Un}(e,x)$ in the recursive-functions setting. Signal is CORE-DEF only. Per COMPRESSION-TARGET for PRIM-CMP012: tur/und/uni is primary (full UTM construction from TM perspective). This section provides the recursive-functions perspective via Normal Form. Keep the theorem statement but condense.
- **Content Directives**:
  - Formal items to preserve: `\begin{thm}[univ-comp]` (universal partial computable function $\fn{Un}(e,x)$) -- PRIM-CMP012 in recursive-functions formulation
  - Formal items to drop: none
  - Prose: compress to theorem statement + one-line proof reference (follows from Normal Form); cut explain block about enumeration details (absorbed into cmp/rec/nft context)
  - Examples: N/A
  - Proofs: preserve full -- it is one line: $\fn{Un}(e,x) \simeq U(\mu s \; T(e,x,s))$

---

### cmp/thy/nou — No Universal Computable Function
- **Action**: KEEP
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.4: Diagonalization and Halting
- **Rationale**: Proves by diagonalization that there is no total computable universal function. Signal is CORE-THM only. This is a key structural result: PRIM-CMP010 (Diagonalization) applied to show the unavoidability of partiality in PRIM-CMP012. The contrast between partial and total universal functions is fundamental.
- **Content Directives**:
  - Formal items to preserve: `\begin{thm}[no-univ]` (no universal total computable function)
  - Formal items to drop: none
  - Prose: compress to theorem statement + explain block (essential -- clarifies why partial functions are unavoidable)
  - Examples: N/A
  - Proofs: preserve full -- the diagonalization is short (3 lines) and canonical: $d(x) = \fn{Un}'(x,x)+1$

---

### cmp/thy/hlt — The Halting Problem
- **Action**: MERGE-INTO:tur/und/hal
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.4: Diagonalization and Halting
- **Rationale**: Duplicate of PRIM-CMP008 / THM-CMP002. Signal is CORE-THM but REDUNDANT. Per COMPRESSION-TARGET: tur/und/hal is primary. Verified from .tex: contains `\begin{thm}[halting-problem]` with two proofs (one via cmp/thy/nou, one direct diagonalization) plus a TM tagblock explanation. The first proof (via no-universal-function) is elegant but dependent on cmp/thy/nou; the second is the same diagonalization as cmp/rec/hlt and tur/und/hal. The TM tagblock is absorbed into tur/und/hal's treatment.
- **Content Directives**:
  - Formal items to preserve: none standalone
  - Formal items to drop: `\begin{thm}[halting-problem]` -- duplicate; both proofs -- duplicates
  - Prose: replace with cross-ref to tur/und/hal; note in tur/und/hal or cmp/thy/nou that undecidability also follows from no-universal-function result
  - Examples: cut all
  - Proofs: cut all -- proved in tur/und/hal

---

### cmp/thy/rus — Comparison with Russell's Paradox
- **Action**: CUT
- **Lean Chapter**: CH-CMP
- **Lean Section**: N/A
- **Rationale**: Introduces no taxonomy items. Signal is PEDAGOGICAL only. Purely philosophical discussion comparing diagonalization in computability with Russell's paradox. No formal content.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: N/A (no formal items)
  - Prose: cut all
  - Examples: cut all
  - Proofs: N/A

---

### cmp/thy/cps — Computable Sets
- **Action**: KEEP
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.3: Decidability
- **Rationale**: Sole formal defining occurrence of PRIM-CMP006 (Decidable Set). Signal is CORE-DEF only. Per COMPRESSION-TARGET for PRIM-CMP006: this is primary (abstract characterization via computable characteristic function). tur/und/int and tur/und/dec reference the concept but do not formally define it. Verified from .tex: `\begin{defn}` gives the clean definition: $S$ is computable iff $\Char{S}$ is computable. Also defines computable relations.
- **Content Directives**:
  - Formal items to preserve: `\begin{defn}` (computable/decidable set via $\Char{S}$) -- PRIM-CMP006; also the definition of computable relations
  - Formal items to drop: none
  - Prose: preserve -- the definition is short and needs its context (distinction from computable functions); compress the explain block to 1-2 sentences
  - Examples: N/A
  - Proofs: N/A

---

### cmp/thy/ces — Computably Enumerable Sets
- **Action**: KEEP
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.3: Decidability
- **Rationale**: Sole formal defining occurrence of PRIM-CMP007 (Semi-Decidable / c.e. Set). Signal is CORE-DEF only. Verified from .tex: `\begin{defn}` gives the clean definition (empty or range of computable function). Also shows computable implies c.e. as immediate consequence.
- **Content Directives**:
  - Formal items to preserve: `\begin{defn}` (computably enumerable set) -- PRIM-CMP007; the argument that computable implies c.e.
  - Formal items to drop: none
  - Prose: compress to intro + definition + one paragraph showing computable implies c.e.; cut explain block about enumeration intuition (retain one sentence)
  - Examples: N/A
  - Proofs: N/A (the computable-implies-c.e. argument is a short construction, preserve it)

---

### cmp/thy/eqc — Equivalent Definitions of C.E. Sets
- **Action**: KEEP
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.3: Decidability
- **Rationale**: Introduces DEF-CMP010 (Recursive Enumerability -- Equivalent Characterizations). Signal is CORE-THM only. Verified from .tex: `\begin{thm}[ce-equiv]` proves four equivalent characterizations (range of computable, range of partial computable, range of PR, domain of partial computable); `\begin{thm}[exists-char]` gives the $\exists$-characterization. Introduces $W_e$ notation. These are fundamental structural results.
- **Content Directives**:
  - Formal items to preserve: `\begin{thm}[ce-equiv]` (four equivalent characterizations of c.e.) -- DEF-CMP010; `\begin{thm}[exists-char]` ($S$ c.e. iff $S = \{x : \exists y \, R(x,y)\}$) -- DEF-CMP010; $W_e$ notation definition
  - Formal items to drop: none
  - Prose: compress explain block to 2-3 sentences; retain the semi-decidability remark (key intuition)
  - Examples: N/A
  - Proofs: preserve full for `thm:ce-equiv` -- the proof is the core content (uses Normal Form to convert range-of-partial to range-of-PR); preserve full for `thm:exists-char` -- short and essential

---

### cmp/thy/ncp — There Are Non-Computable Sets
- **Action**: KEEP
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.3: Decidability
- **Rationale**: Proves $K_0$ and $K$ are c.e. but not computable. Signal is CORE-THM only. These are the canonical examples of non-computable sets and are referenced throughout the rest of the chapter (reducibility, completeness, Rice's theorem). $K$ is the self-halting set, central to computability theory.
- **Content Directives**:
  - Formal items to preserve: `\begin{thm}[K-0]` ($K_0$ is c.e. but not computable); `\begin{thm}[K]` ($K$ is c.e. but not computable)
  - Formal items to drop: none
  - Prose: compress to definitions of $K_0 = \{\tuple{e,x} : \cfind{e}(x) \fdefined\}$ and $K = \{e : \cfind{e}(e) \fdefined\}$ plus theorem statements
  - Examples: N/A
  - Proofs: preserve full for both -- proofs are short (K-0: domain argument + halting problem; K: direct diagonalization)

---

### cmp/thy/clo — Union and Intersection of C.E. Sets
- **Action**: CONDENSE
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.3: Decidability
- **Rationale**: Signal is STEPPING-STONE only. Closure of c.e. sets under union and intersection is a useful structural property but not a taxonomy item. It feeds into the complement non-closure result.
- **Content Directives**:
  - Formal items to preserve: `\begin{thm}` (c.e. closed under $\cup$ and $\cap$)
  - Formal items to drop: none
  - Prose: compress to theorem statement + one-line remark
  - Examples: cut all
  - Proofs: preserve sketch only -- one sentence per case (union: interleave enumerations; intersection: check membership in both)

---

### cmp/thy/cmp — C.E. Sets not Closed under Complement
- **Action**: KEEP
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.3: Decidability
- **Rationale**: Proves the fundamental characterization: $A$ computable iff both $A$ and $\bar{A}$ are c.e. Signal is CORE-THM only. This result is structural and heavily cited. Corollary: $\bar{K_0}$ is not c.e.
- **Content Directives**:
  - Formal items to preserve: `\begin{thm}[ce-comp]` ($A$ computable iff $A$ and $\bar{A}$ both c.e.); `\begin{cor}[comp-k]` ($\bar{K_0}$ not c.e.)
  - Formal items to drop: none
  - Prose: compress explain block to one sentence (operational: dovetail semi-decision procedures for $A$ and $\bar{A}$)
  - Examples: N/A
  - Proofs: preserve full -- the proof is short and constructive (dovetailing via unbounded search on disjunction of $T$-predicates)

---

### cmp/thy/red — Reducibility
- **Action**: KEEP
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.6: Computability Theory
- **Rationale**: Sole formal defining occurrence of PRIM-CMP009 (Many-One Reducibility). Signal is CORE-DEF only. Verified from .tex: `\begin{defn}` defines many-one reduction $A \leq_m B$ via computable $f$ with $x \in A \iff f(x) \in B$. Also mentions one-one reducibility.
- **Content Directives**:
  - Formal items to preserve: `\begin{defn}` (many-one reduction, $A \leq_m B$, many-one equivalence $A \equiv_m B$) -- PRIM-CMP009
  - Formal items to drop: none
  - Prose: compress the explain block to 2-3 sentences; retain the motivating example ($K$ reduced to $K_0$ via $f(x) = \tuple{x,x}$); cut NP-completeness digression and one-one reducibility discussion (note in one sentence)
  - Examples: keep the $K$-to-$K_0$ reduction example (canonical, directly instantiates PRIM-CMP009)
  - Proofs: N/A

---

### cmp/thy/ppr — Properties of Reducibility
- **Action**: KEEP
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.6: Computability Theory
- **Rationale**: Signal is CORE-THM only. Transitivity of $\leq_m$ and preservation of c.e./decidable under reduction are essential structural properties of PRIM-CMP009. Used in all subsequent undecidability proofs via reduction.
- **Content Directives**:
  - Formal items to preserve: `\begin{prop}[trans-red]` ($\leq_m$ is transitive); `\begin{prop}[reduce]` ($A \leq_m B$ and $B$ c.e./decidable implies $A$ c.e./decidable)
  - Formal items to drop: Turing reducibility digression -- tangential
  - Prose: compress to proposition statements
  - Examples: cut all
  - Proofs: preserve full for both -- both are short (transitivity: compose reductions; preservation: compose with characteristic function)

---

### cmp/thy/cce — Complete Computably Enumerable Sets
- **Action**: KEEP
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.6: Computability Theory
- **Rationale**: Introduces DEF-CMP008 (Creative Set, related: completeness). Signal is CORE-THM only. Defines complete c.e. sets and proves $K$, $K_0$, $K_1$ are complete -- establishing the structure of the c.e. degree hierarchy.
- **Content Directives**:
  - Formal items to preserve: `\begin{defn}` (complete c.e. set) -- DEF-CMP008; `\begin{thm}` ($K$, $K_0$, $K_1$ are complete c.e.)
  - Formal items to drop: Friedberg-Muchnik digression -- tangential
  - Prose: compress to definition + theorem statement
  - Examples: N/A
  - Proofs: preserve full -- proof is short (for $K_0$: $f(x)=\tuple{e,x}$; for $K_1$: reference to cmp/thy/k1 + transitivity)

---

### cmp/thy/k1 — An Example of Reducibility
- **Action**: CUT
- **Lean Chapter**: CH-CMP
- **Lean Section**: N/A
- **Rationale**: Introduces no taxonomy items. Signal is PEDAGOGICAL only. $K_1 = \{e : \cfind{e}(0)\fdefined\}$ is an example application of s-m-n and reducibility. The completeness of $K_1$ is already cited in cmp/thy/cce.
- **Content Directives**:
  - Formal items to preserve: none standalone -- the $K_1$ result is cited in cmp/thy/cce
  - Formal items to drop: `\begin{prop}[k1]` -- OL-ONLY application
  - Prose: cut all -- can be noted as one-line example in cmp/thy/cce
  - Examples: cut all
  - Proofs: cut all

---

### cmp/thy/tot — Totality is Undecidable
- **Action**: CONDENSE
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.6: Computability Theory
- **Rationale**: Signal is STEPPING-STONE only. Proves $\fn{Tot}$ is not computable (not even c.e.) via reduction from $K$ using s-m-n. Important stepping stone to Rice's theorem.
- **Content Directives**:
  - Formal items to preserve: `\begin{prop}[total]` ($\fn{Tot}$ not computable)
  - Formal items to drop: none
  - Prose: compress to definition of $\fn{Tot} = \{x : \cfind{x} \text{ is total}\}$ + proposition statement
  - Examples: cut all
  - Proofs: preserve sketch only -- the s-m-n reduction technique (define $h(x,y)$ that is total iff $x \in K$, apply s-m-n) in 3-4 sentences; this serves as the template for Rice's theorem proof

---

### cmp/thy/rce — Rice's Theorem
- **Action**: KEEP
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.7: Theorems
- **Rationale**: Sole defining occurrence of THM-CMP003 (Rice's Theorem). Signal is CORE-THM only. Verified from .tex: `\begin{thm}` (Rice's Theorem: no nontrivial index set is decidable) with full proof via s-m-n + halting problem. Corollaries demonstrate power. This is a major theorem of computability theory.
- **Content Directives**:
  - Formal items to preserve: `\begin{thm}` (Rice's Theorem) -- THM-CMP003; `\begin{cor}` (sample applications: range contains 17, constant, total, monotone -- all undecidable)
  - Formal items to drop: none
  - Prose: retain the explain block distinguishing programs (syntactic) from behavior (semantic) -- this is the key insight of Rice's theorem; compress to 2-3 sentences
  - Examples: keep the corollary applications (canonical, demonstrate theorem's power)
  - Proofs: preserve full -- the proof is the core content and uses s-m-n + halting problem reduction; essential for understanding the technique

---

### cmp/thy/fix — The Fixed-Point Theorem
- **Action**: KEEP
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.7: Theorems
- **Rationale**: Sole defining occurrence of THM-CMP005 (Recursion Theorem / Kleene's Fixed-Point Theorem). Signal is CORE-THM only. Verified from .tex: `\begin{lem}[fixed-equiv]` (two equivalent formulations) and `\begin{thm}` (existence of fixed point) with full proof via $\fn{diag}$ construction. Fundamental theorem enabling self-reference.
- **Content Directives**:
  - Formal items to preserve: `\begin{lem}[fixed-equiv]` (two equivalent forms: (1) $\cfind{e}(y) \simeq g(e,y)$, (2) $\cfind{e}(y) \simeq \cfind{f(e)}(y)$); `\begin{thm}` (statement (1) is true)
  - Formal items to drop: lambda calculus digression (tagblock:lambda) -- tangential
  - Prose: retain the halting problem motivation (shows self-reference is the mechanism); compress the quine/print explanation to 2-3 sentences (helpful intuition)
  - Examples: N/A
  - Proofs: preserve full for lemma (short: both directions using Un and s-m-n); preserve full for theorem (the $\fn{diag}$ construction is the core content: define $s(x,y)$, get $\fn{diag}$ via s-m-n, define $l$, let $e = \fn{diag}(\gn{l})$)

---

### cmp/thy/apf — Applying the Fixed-Point Theorem
- **Action**: CUT
- **Lean Chapter**: CH-CMP
- **Lean Section**: N/A
- **Rationale**: Introduces no taxonomy items. Signal is PEDAGOGICAL only. Application of THM-CMP005 (no effective procedure for characteristic functions of decidable c.e. sets). Quines mentioned.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: `\begin{thm}` -- OL-ONLY application
  - Prose: cut all
  - Examples: cut all
  - Proofs: cut all

---

### cmp/thy/slf — Defining Functions using Self-Reference
- **Action**: CUT
- **Lean Chapter**: CH-CMP
- **Lean Section**: N/A
- **Rationale**: Introduces no taxonomy items. Signal is PEDAGOGICAL only. Application of fixed-point theorem to justify self-referential definitions (e.g., gcd). Pedagogical elaboration.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: N/A (no formal items)
  - Prose: cut all
  - Examples: cut all
  - Proofs: N/A

---

### Chapter: machines-computations (tur/mac)

### tur/mac/int — Introduction
- **Action**: CUT
- **Lean Chapter**: CH-CMP
- **Lean Section**: N/A
- **Rationale**: Introduces no taxonomy items formally. Signal is PEDAGOGICAL only. Purely expository section with pedagogical explanation of TM mechanism, philosophical discussion, and historical context. PRIM-CMP004 and PRIM-CMP001 are only conceptually introduced; formal definitions are in tur/mac/tur and tur/mac/una.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: N/A (no formal items)
  - Prose: cut all
  - Examples: cut all
  - Proofs: N/A

---

### tur/mac/tur — Turing Machines
- **Action**: KEEP
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.2: Turing Machines
- **Rationale**: Sole formal defining occurrence of PRIM-CMP004 (Turing Machine). Signal is CORE-DEF only. Per COMPRESSION-TARGET for PRIM-CMP004: this is primary (formal 4-tuple definition). Verified from .tex: `\begin{defn}[Turing machine]` gives $M = \langle Q, \Sigma, q_0, \delta \rangle$ with all components.
- **Content Directives**:
  - Formal items to preserve: `\begin{defn}[Turing machine]` ($M = \langle Q, \Sigma, q_0, \delta \rangle$) -- PRIM-CMP004
  - Formal items to drop: `\begin{ex}` (Even machine) -- pedagogical example
  - Prose: compress to intro + definition; retain one sentence about $\TMendtape$ as left end marker (important convention)
  - Examples: cut the Even machine example -- pedagogical
  - Proofs: N/A

---

### tur/mac/hal — Halting States
- **Action**: CUT
- **Lean Chapter**: CH-CMP
- **Lean Section**: N/A
- **Rationale**: Introduces no taxonomy items. Signal is PEDAGOGICAL only. Discusses alternative TM formulation with dedicated halting states -- a variant not used in the main development.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: halting state examples -- pedagogical
  - Prose: cut all
  - Examples: cut all
  - Proofs: N/A

---

### cmp/tur/con — Configurations and Computations
- **Action**: KEEP
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.2: Turing Machines
- **Rationale**: Defines the execution semantics of TMs (configuration, initial configuration, yields-in-one-step, run, halting, output). Signal is CORE-DEF only. These concepts are essential for connecting TMs to the functions they compute. Without this, PRIM-CMP004 has no operational meaning.
- **Content Directives**:
  - Formal items to preserve: `\begin{defn}[Configuration]` (triple $\langle C, m, q \rangle$); `\begin{defn}[Initial configuration]`; `\begin{defn}` (yields in one step); `\begin{defn}[Run, halting, output]`
  - Formal items to drop: none -- all are essential
  - Prose: compress explain blocks to one sentence each; the formal definitions carry the content
  - Examples: N/A
  - Proofs: N/A

---

### tur/mac/una — Unary Representation of Numbers
- **Action**: CONDENSE
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.2: Turing Machines
- **Rationale**: Defines what it means for a TM to compute a function (PRIM-CMP001 in TM setting). Signal is CORE-DEF only. Per COMPRESSION-TARGET for PRIM-CMP001: cmp/rec/par is primary (partial recursive functions). This section provides the TM formulation which must be stated but need not be the primary. Verified from .tex: `\begin{defn}[Computation]` (TM computes $f$ via unary representation) and `\begin{defn}` (TM computes partial function).
- **Content Directives**:
  - Formal items to preserve: `\begin{defn}[Computation]` ($M$ computes $f: \Nat^k \to \Nat$ via unary); `\begin{defn}` (TM computes partial function)
  - Formal items to drop: `\begin{ex}[adder]` -- pedagogical; `\begin{ex}` (doubler) -- pedagogical; `\begin{ex}` (mover) -- pedagogical; all `\begin{prob}` items -- exercises
  - Prose: compress to intro + definitions; one sentence on unary representation ($\TMstroke^n$ represents $n$)
  - Examples: cut all -- pedagogical machine examples
  - Proofs: N/A

---

### tur/mac/var — Variants of Turing Machines
- **Action**: CUT
- **Lean Chapter**: CH-CMP
- **Lean Section**: N/A
- **Rationale**: Signal is PEDAGOGICAL only. Discusses TM variants (multi-tape, two-way infinite tape, etc.) and informally argues equivalence. THM-CMP001 (Equivalence of Computation Models) is only informally discussed; the lean text can note this as a remark.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: N/A (no formal items)
  - Prose: cut all -- note equivalence of TM variants as a one-line remark in tur/mac/tur if needed
  - Examples: cut all
  - Proofs: N/A

---

### tur/mac/ctt — The Church-Turing Thesis
- **Action**: KEEP
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.2: Turing Machines
- **Rationale**: Sole formal defining occurrence of PRIM-CMP005 (Church-Turing Thesis). Signal is CORE-DEF only. Verified from .tex: `\begin{defn}[Church-Turing thesis]` states that effective computability = Turing computability. This is a central methodological principle used throughout computability theory.
- **Content Directives**:
  - Formal items to preserve: `\begin{defn}[Church-Turing thesis]` -- PRIM-CMP005
  - Formal items to drop: none
  - Prose: compress to definition + two key uses: (1) justify informal computability arguments, (2) derive absolute non-computability from TM non-computability; compress from 3 paragraphs to 1
  - Examples: N/A
  - Proofs: N/A

---

### tur/mac/rep — Representing Turing Machines
- **Action**: CUT
- **Lean Chapter**: CH-CMP
- **Lean Section**: N/A
- **Rationale**: Introduces no taxonomy items. Signal is PEDAGOGICAL only. Presents state diagrams and machine tables as representation methods for TMs. Entirely pedagogical visualization tools.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: all examples and exercises -- pedagogical
  - Prose: cut all
  - Examples: cut all
  - Proofs: N/A

---

### tur/mac/dis — Disciplined Machines
- **Action**: CONDENSE
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.2: Turing Machines
- **Rationale**: Signal is STEPPING-STONE only. Disciplined TMs (halt while scanning first square) are a technical convenience that simplifies machine composition proofs. Used in tur/und/hal proof. OL-ONLY concept but needed as infrastructure.
- **Content Directives**:
  - Formal items to preserve: `\begin{defn}` (disciplined TM); `\begin{prop}` (disciplined TMs compute same functions as arbitrary TMs)
  - Formal items to drop: `\begin{ex}` (disciplined adder) -- pedagogical; problems -- exercises
  - Prose: compress to definition + proposition statement; one sentence explaining purpose (simplifies composition)
  - Examples: cut all
  - Proofs: preserve sketch only for proposition -- one sentence (modify any TM to return to first square before halting)

---

### tur/mac/cmb — Combining Turing Machines
- **Action**: CONDENSE
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.2: Turing Machines
- **Rationale**: Signal is STEPPING-STONE only. Machine composition ($M \frown M'$) is essential infrastructure for building complex machines and is directly used in tur/und/hal (the halting problem proof). OL-ONLY concept but required for tur/und/hal.
- **Content Directives**:
  - Formal items to preserve: formal construction of $M \frown M'$ (sequential composition); `\begin{prop}` (composition preserves computability)
  - Formal items to drop: `\begin{ex}` (combined adder+doubler) -- pedagogical; `\begin{prob}` -- exercise
  - Prose: compress to construction description + proposition statement; one sentence on purpose (build complex machines from simple ones)
  - Examples: cut all
  - Proofs: preserve sketch only for proposition -- one sentence (run first machine, then second)

---

### Chapter: undecidability (tur/und)

### tur/und/enu — Enumerating Turing Machines
- **Action**: KEEP
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.5: Coding and Universality
- **Rationale**: Introduces PRIM-CMP011 (Godel Numbering for TMs) and DEF-CMP005 (Index). Signal is CORE-DEF only. Per COMPRESSION-TARGET for PRIM-CMP011: cmp/rec/nft is primary for function indices, cmp/rec/seq for sequence coding; this section handles TM description coding. All three aspects of PRIM-CMP011 are essential. Per COMPRESSION-TARGET for DEF-CMP005: cmp/rec/nft is primary (introduces $\cfind{e}$); this section provides the TM-side index concept. Verified from .tex: describes encoding TMs as sequences of positive integers, proves uncomputable functions exist via cardinality.
- **Content Directives**:
  - Formal items to preserve: the encoding scheme (TMs as sequences of positive integers); `\begin{thm}` (uncomputable functions exist); the concept that TMs can be enumerated as $M_1, M_2, \ldots$
  - Formal items to drop: `\begin{prob}` -- exercise; state diagram figures -- pedagogical
  - Prose: compress to the encoding scheme + theorem; cut the extended explanation of standard machines (retain one sentence: rename states/symbols to positive integers)
  - Examples: keep the standard Even machine encoding as the canonical example of the coding scheme
  - Proofs: preserve full for the theorem -- short argument (TMs enumerable, functions not, hence non-computable functions exist)

---

### tur/und/int — Introduction
- **Action**: CUT
- **Lean Chapter**: CH-CMP
- **Lean Section**: N/A
- **Rationale**: Introduces no taxonomy items formally. Signal is PEDAGOGICAL only. Motivates undecidability, discusses cardinality argument, previews halting problem and decision problem. All formal content appears in subsequent sections.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: N/A (no formal items)
  - Prose: cut all
  - Examples: cut all
  - Proofs: N/A

---

### tur/und/hal — The Halting Problem
- **Action**: ABSORB:cmp/rec/hlt,cmp/thy/hlt
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.4: Diagonalization and Halting
- **Rationale**: Primary for PRIM-CMP008 (Halting Problem) and THM-CMP002 (Unsolvability of Halting Problem). Signal is CORE-THM only. Per COMPRESSION-TARGET: this section provides (1) formal definitions of halting function and halting problem, (2) the auxiliary function $s$ and its non-computability lemma, and (3) the full unsolvability theorem with proof. Verified from .tex: `\begin{defn}[Halting function]`, `\begin{defn}[Halting problem]`, `\begin{defn}` (function $s$), `\begin{lem}` ($s$ not computable -- via TM construction with $S \frown J$), `\begin{thm}[Unsolvability of the Halting Problem]` (reduction from $s$ to $h$). Absorbs cmp/rec/hlt (recursive-functions version) and cmp/thy/hlt (computability-theory duplicate).
- **Content Directives**:
  - Formal items to preserve: `\begin{defn}[Halting function]` ($h(e,n)$) -- PRIM-CMP008; `\begin{defn}[Halting problem]` -- PRIM-CMP008; `\begin{lem}` ($s$ not Turing computable) -- key lemma; `\begin{thm}[Unsolvability of the Halting Problem]` -- THM-CMP002
  - Formal items to drop: `\begin{defn}` (function $s$) -- inline into lemma statement; all `\begin{prob}` items -- exercises
  - Prose: retain explain blocks about enumeration context and proof strategy (essential for understanding the diagonalization); add one-sentence remark that the same result holds for partial recursive functions (absorbing cmp/rec/hlt perspective); add one-sentence remark noting the alternative proof via no-universal-function (absorbing cmp/thy/hlt's first proof)
  - Examples: N/A
  - Proofs: preserve full for lemma ($s$ not computable: $S \frown J$ construction with diagonalization at $M_e$ on input $e$); preserve full for theorem (reduction: copier + $H$ would compute $s$)

---

### tur/und/rep — Representing Turing Machines
- **Action**: CONDENSE
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.5: Coding and Universality
- **Rationale**: Introduces DEF-CMP009 (Representability of TM behavior in FOL). Signal is STEPPING-STONE only. This is the technical machinery encoding TM execution in first-order sentences $!T(M,w)$ and $!E(M,w)$, needed for the undecidability of the decision problem (tur/und/uns). Note: DEF-CMP009 also appears in inc/* sections (handled in Step 6); here it is the TM-specific encoding in FOL.
- **Content Directives**:
  - Formal items to preserve: `\begin{defn}` (language $\Lang{L}_M$: predicates $Q_q$, $S_\sigma$, constant $0$, function $\prime$, predicate $<$) -- DEF-CMP009; the construction of sentences $!T(M,w)$ and $!E(M,w)$ (description of input configuration and transition axioms)
  - Formal items to drop: `\begin{prop}` ($!T(M,w) \Entails \num{m} < \num{k}$) -- OL-ONLY lemma used in verification; `\begin{prob}` -- exercise
  - Prose: compress to definition of $\Lang{L}_M$ + summary of what $!T(M,w)$ and $!E(M,w)$ encode (2-3 sentences); cut detailed listing of all axiom types
  - Examples: N/A
  - Proofs: N/A

---

### tur/und/dec — The Decision Problem
- **Action**: CONDENSE
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.7: Theorems
- **Rationale**: Signal is STEPPING-STONE only. Sets up the strategy for proving the decision problem unsolvable by reduction from halting problem. PRIM-CMP006 (Decidable Set) is applied to FOL validity here but defined in cmp/thy/cps.
- **Content Directives**:
  - Formal items to preserve: the reduction strategy statement (if FOL validity were decidable, the halting problem would be solvable)
  - Formal items to drop: N/A (no formal environments)
  - Prose: compress to one paragraph stating the proof strategy
  - Examples: N/A
  - Proofs: N/A

---

### tur/und/ver — Verifying the Representation
- **Action**: CONDENSE
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.5: Coding and Universality
- **Rationale**: Signal is STEPPING-STONE only. Technical proof that the FOL representation correctly captures TM behavior. Contains 4 lemmas establishing the correctness of $!T(M,w)$ and $!E(M,w)$. Essential for the decision problem result but highly technical.
- **Content Directives**:
  - Formal items to preserve: `\begin{lem}` (halt implies $!E(M,w)$ -- valid if halt); `\begin{lem}` ($!T(M,w) \Entails !C(M,w,n)$ -- representation correct); `\begin{lem}` (valid if halt); `\begin{lem}` (halt if valid) -- the key bidirectional correctness result
  - Formal items to drop: `\begin{defn}` ($!C(M,w,n)$ configuration sentence) -- inline into lemma context; `\begin{prob}` items -- exercises
  - Prose: compress to statements of the four lemmas with one-sentence proof ideas
  - Examples: N/A
  - Proofs: preserve sketch only for all four lemmas -- one paragraph each summarizing the inductive argument; cut detailed case analysis

---

### tur/und/uni — Universal Turing Machines
- **Action**: KEEP
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.5: Coding and Universality
- **Rationale**: Primary for PRIM-CMP012 (Universal Turing Machine). Signal is CORE-THM only. Per COMPRESSION-TARGET for PRIM-CMP012: this is primary (full UTM construction). Verified from .tex: `\begin{defn}` (index of TM) -- DEF-CMP005 in TM context; `\begin{thm}[universal-tm]` (existence of universal TM $U$ that simulates any $M_e$ on input $n$) with detailed proof outline.
- **Content Directives**:
  - Formal items to preserve: `\begin{defn}` (index of TM, $M_e$ notation) -- DEF-CMP005 TM formulation; `\begin{thm}[universal-tm]` (universal TM exists: halts iff $M_e$ halts, produces same output) -- PRIM-CMP012
  - Formal items to drop: none
  - Prose: retain the introductory paragraph establishing the natural question of which functions of TM indices are computable; compress the example of counting states (one sentence)
  - Examples: N/A
  - Proofs: preserve full -- the proof outlines UTM operation (decode, simulate, output) and is the core content; compress the step-by-step simulation description while retaining the key ideas (decode index, maintain current state/position/tape, simulate transitions, copy output)

---

### tur/und/uns — The Decision Problem is Unsolvable
- **Action**: KEEP
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.7: Theorems
- **Rationale**: Main result connecting logic and computability: FOL validity is undecidable, satisfiability is undecidable, validity is semi-decidable. Signal is CORE-THM only. Extends THM-CMP002 (Halting unsolvable) to FOL via the representation machinery. Verified from .tex: `\begin{thm}[decision-prob]` (decision problem unsolvable), `\begin{cor}[undecidable-sat]` (satisfiability undecidable), `\begin{thm}[valid-ce]` (validity semi-decidable).
- **Content Directives**:
  - Formal items to preserve: `\begin{thm}[decision-prob]` (decision problem unsolvable) -- THM-CMP002 extension; `\begin{cor}[undecidable-sat]` (satisfiability undecidable); `\begin{thm}[valid-ce]` (validity semi-decidable) -- PRIM-CMP007 application
  - Formal items to drop: none
  - Prose: retain the explain block about semi-decidability (one sentence)
  - Examples: N/A
  - Proofs: preserve full for all three -- decision problem proof uses the representation lemmas (tur/und/ver); satisfiability corollary is short (negate + decide); semi-decidability proof appeals to soundness/completeness + enumeration of derivations

---

### tur/und/tra — Trakhtenbrot's Theorem
- **Action**: CUT
- **Lean Chapter**: CH-CMP
- **Lean Section**: N/A
- **Rationale**: Introduces no taxonomy items. Signal is TANGENTIAL only. Advanced result (finite satisfiability undecidable) extending beyond core CMP material. All items are OL-ONLY.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: all lemmas, theorem, corollary, modified $!T'(M,w)$ -- tangential
  - Prose: cut all
  - Examples: cut all
  - Proofs: cut all

---

## Summary

### Action Counts

| Action | Count |
|--------|-------|
| KEEP | 22 |
| CONDENSE | 13 |
| MERGE-INTO | 6 |
| ABSORB | 2 |
| CUT | 17 |
| **Total** | **60** |

### Detail by Action

**KEEP (22):** cmp/rec/prr, cmp/rec/seq, cmp/rec/par, cmp/rec/nft, cmp/thy/cps, cmp/thy/ces, cmp/thy/eqc, cmp/thy/ncp, cmp/thy/cmp, cmp/thy/red, cmp/thy/ppr, cmp/thy/cce, cmp/thy/rce, cmp/thy/fix, cmp/thy/smn, cmp/thy/nou, tur/mac/tur, cmp/tur/con, tur/mac/ctt, tur/und/enu, tur/und/uni, tur/und/uns

**ABSORB (2):** cmp/rec/prf (absorbs cmp/rec/pre and cmp/rec/com), tur/und/hal (absorbs cmp/rec/hlt and cmp/thy/hlt)

**CONDENSE (13):** cmp/rec/cmp, cmp/rec/bmi, cmp/rec/npr, cmp/thy/uni, cmp/thy/clo, cmp/thy/tot, tur/mac/una, tur/mac/dis, tur/mac/cmb, tur/und/rep, tur/und/dec, tur/und/ver, tur/und/hal (note: tur/und/hal is listed under ABSORB as its primary action)

*Correction: tur/und/hal is ABSORB, not CONDENSE. The 13 CONDENSE sections are:* cmp/rec/cmp, cmp/rec/bmi, cmp/rec/npr, cmp/thy/uni, cmp/thy/clo, cmp/thy/tot, tur/mac/una, tur/mac/dis, tur/mac/cmb, tur/und/rep, tur/und/dec, tur/und/ver, (12 sections -- recount shows 12 CONDENSE not 13)

*Revised counts:*

| Action | Count |
|--------|-------|
| KEEP | 22 |
| CONDENSE | 12 |
| MERGE-INTO | 6 |
| ABSORB | 2 |
| CUT | 18 |
| **Total** | **60** |

**MERGE-INTO (6):** cmp/rec/pre -> cmp/rec/prf, cmp/rec/com -> cmp/rec/prf, cmp/rec/hlt -> tur/und/hal, cmp/thy/nfm -> cmp/rec/nft, cmp/thy/hlt -> tur/und/hal, tur/und/int -> (CUT, not MERGE)

*Correction: tur/und/int is CUT, not MERGE-INTO. Recount:*

**MERGE-INTO (5):** cmp/rec/pre -> cmp/rec/prf, cmp/rec/com -> cmp/rec/prf, cmp/rec/hlt -> tur/und/hal, cmp/thy/nfm -> cmp/rec/nft, cmp/thy/hlt -> tur/und/hal

**CUT (19):** cmp/rec/int, cmp/rec/not, cmp/rec/exa, cmp/rec/pri, cmp/rec/tre, cmp/rec/ore, cmp/rec/gen, cmp/thy/int, cmp/thy/cod, cmp/thy/rus, cmp/thy/k1, cmp/thy/apf, cmp/thy/slf, tur/mac/int, tur/mac/hal, tur/mac/var, tur/mac/rep, tur/und/int, tur/und/tra

*Final corrected counts:*

| Action | Count |
|--------|-------|
| KEEP | 22 |
| CONDENSE | 12 |
| MERGE-INTO | 5 |
| ABSORB | 2 |
| CUT | 19 |
| **Total** | **60** |

### CMP Taxonomy Coverage (28 items across all CMP sections)

| Taxonomy ID | Authoritative Section | Lean Section |
|-------------|----------------------|--------------|
| PRIM-CMP001 (Computable Function) | cmp/rec/par (primary: partial recursive) | CMP.1 |
| PRIM-CMP002 (Primitive Recursive Function) | cmp/rec/prf | CMP.1 |
| PRIM-CMP003 (mu-Recursion) | cmp/rec/par | CMP.1 |
| PRIM-CMP004 (Turing Machine) | tur/mac/tur | CMP.2 |
| PRIM-CMP005 (Church-Turing Thesis) | tur/mac/ctt | CMP.2 |
| PRIM-CMP006 (Decidable Set) | cmp/thy/cps (primary) | CMP.3 |
| PRIM-CMP007 (Semi-Decidable / c.e. Set) | cmp/thy/ces | CMP.3 |
| PRIM-CMP008 (Halting Problem) | tur/und/hal (primary) | CMP.4 |
| PRIM-CMP009 (Many-One Reducibility) | cmp/thy/red | CMP.6 |
| PRIM-CMP010 (Diagonalization) | cmp/rec/npr (first use); cmp/thy/nou (key application) | CMP.4 |
| PRIM-CMP011 (Godel Numbering) | cmp/rec/seq (sequences), cmp/rec/nft (function indices), tur/und/enu (TM codes) | CMP.5 |
| PRIM-CMP012 (Universal TM) | tur/und/uni (primary: full UTM construction) | CMP.5 |
| DEF-CMP001 (Partial Function) | cmp/rec/par (implicit) | CMP.1 |
| DEF-CMP002 (Total Function) | cmp/rec/par | CMP.1 |
| DEF-CMP003 (Characteristic Function) | cmp/rec/prr | CMP.1 |
| DEF-CMP004 (Enumeration) | cmp/thy/eqc (via $W_e$) | CMP.3 |
| DEF-CMP005 (Index / Program) | cmp/rec/nft (primary: $\cfind{e}$ notation) | CMP.5 |
| DEF-CMP008 (Creative Set / Completeness) | cmp/thy/cce | CMP.6 |
| DEF-CMP009 (Representability) | tur/und/rep | CMP.5 |
| DEF-CMP010 (R.E. Equiv. Characterizations) | cmp/thy/eqc | CMP.3 |
| THM-CMP001 (Equivalence of Models) | tur/mac/var (informal only -- CUT) | N/A |
| THM-CMP002 (Halting Unsolvable) | tur/und/hal (primary) | CMP.4 |
| THM-CMP003 (Rice's Theorem) | cmp/thy/rce | CMP.7 |
| THM-CMP004 (s-m-n / Normal Form) | cmp/thy/smn (s-m-n primary), cmp/rec/nft (Normal Form primary) | CMP.5 |
| THM-CMP005 (Recursion Theorem) | cmp/thy/fix | CMP.7 |

**Notes:**
- THM-CMP001 (Equivalence of Computation Models) is only informally discussed in tur/mac/var which is CUT. If needed, add a one-sentence remark in tur/mac/ctt.
- DEF-CMP006 (Lambda-Definable), DEF-CMP007 (Productive Set) are not present in any CMP batch section.
- DEF-CMP009 (Representability) also appears in inc/* sections (Step 6). The tur/und/rep treatment is the TM-in-FOL encoding; the inc/* treatment will be the arithmetic representability concept.

### COMPRESSION-TARGETs Resolved (9 items)

1. **PRIM-CMP001 (Computable Function)**: Primary = cmp/rec/par (mathematical definition via partial recursive functions). tur/mac/una CONDENSES the TM formulation. tur/mac/int CUT.

2. **PRIM-CMP004 (Turing Machine)**: Primary = tur/mac/tur (formal 4-tuple definition). tur/mac/int CUT.

3. **PRIM-CMP006 (Decidable Set)**: Primary = cmp/thy/cps (abstract characterization via computable characteristic function). tur/und/int CUT. tur/und/dec CONDENSES the application to FOL.

4. **PRIM-CMP008 (Halting Problem)**: Primary = tur/und/hal (formal definitions + complete diagonalization proof via TM construction). cmp/rec/hlt MERGES-INTO tur/und/hal. cmp/thy/hlt MERGES-INTO tur/und/hal. tur/und/int CUT.

5. **PRIM-CMP011 (Godel Numbering)**: Three complementary aspects, all preserved:
   - Sequence coding: cmp/rec/seq KEEP (primary for coding technique)
   - Function indexing: cmp/rec/nft KEEP (primary for index $e$ and $\cfind{e}$)
   - TM description coding: tur/und/enu KEEP (TM enumeration)

6. **PRIM-CMP012 (Universal TM)**: Primary = tur/und/uni (full UTM construction with simulation outline). cmp/thy/uni CONDENSES the recursive-functions formulation. cmp/thy/int CUT.

7. **THM-CMP002 (Halting Unsolvable)**: Primary = tur/und/hal (combined with PRIM-CMP008). tur/und/uns KEEP (extends to decision problem unsolvability).

8. **THM-CMP004 (s-m-n / Normal Form)**: Two components:
   - Normal Form: Primary = cmp/rec/nft KEEP. cmp/thy/nfm MERGES-INTO cmp/rec/nft.
   - s-m-n: Primary = cmp/thy/smn KEEP (dedicated section).

9. **DEF-CMP005 (Index)**: Primary = cmp/rec/nft (introduces $\cfind{e}$ notation and index concept). tur/und/enu KEEP (provides TM-side index concept).

---

## CH-DED: Deduction

---

### Chapter: proof-systems

### fol/prf/int — Introduction
- **Action**: CUT
- **Lean Chapter**: CH-DED
- **Lean Section**: N/A
- **Rationale**: Signal is PEDAGOGICAL. No formal definitions or theorems introduced. Purely motivational narrative explaining the goals of derivation systems and the soundness/completeness connection. The lean text's DED.1 generic section will provide a one-paragraph framing replacing this.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: N/A (no formal items)
  - Prose: cut all -- replaced by DED.1 intro paragraph
  - Examples: cut all
  - Proofs: N/A

---

### fol/prf/axd — Axiomatic Derivation (proof-systems overview)
- **Action**: CONDENSE
- **Lean Chapter**: CH-DED
- **Lean Section**: DED.2: Axiomatic (Hilbert) Systems
- **Rationale**: Signal is CORE-DEF for Hilbert systems, but content is a discursive survey rather than formal specification. The formal definitions of DEF-DED005, AX-DED001, AX-DED003 live in fol/axd/prp and fol/axd/rul. This section contributes a useful high-level framing paragraph and one worked derivation example for DED.2.
- **Content Directives**:
  - Formal items to preserve: one-paragraph characterization of Hilbert systems (linear sequence, axiom schemas + few rules)
  - Formal items to drop: worked derivation example (redundant with fol/axd/pro examples, but keep one sentence summarizing it)
  - Prose: compress to 2-3 sentence overview for DED.2 preamble; cut historical notes (Frege, Russell, Hilbert)
  - Examples: cut all -- pedagogical illustration
  - Proofs: N/A

---

### fol/prf/ntd — Natural Deduction (proof-systems overview)
- **Action**: CONDENSE
- **Lean Chapter**: CH-DED
- **Lean Section**: DED.3: Natural Deduction
- **Rationale**: Signal is CORE-DEF for ND systems, but content is a discursive survey. Formal definitions of DEF-DED006, PRIM-DED009 live in fol/ntd/rul, fol/ntd/prl. This section contributes a useful high-level framing paragraph for DED.3.
- **Content Directives**:
  - Formal items to preserve: one-paragraph characterization of ND (tree-structured, intro/elim rules, assumption discharge)
  - Formal items to drop: worked derivation example (redundant)
  - Prose: compress to 2-3 sentence overview for DED.3 preamble; cut historical notes (Gentzen, Jaskowski, Prawitz, Fitch)
  - Examples: cut all
  - Proofs: N/A

---

### fol/prf/seq — The Sequent Calculus (proof-systems overview)
- **Action**: CUT
- **Lean Chapter**: CH-DED
- **Lean Section**: N/A
- **Rationale**: Signal is PEDAGOGICAL (REDUNDANT-WITH: fol/seq chapter). Everything here is covered more formally in fol/seq/rul, fol/seq/prl, fol/seq/srl. The DED.4 preamble will be sourced from the condensed fol/prf/ntd-style overview, but actually fol/seq/rul already has a clean sequent definition. No unique content.
- **Content Directives**:
  - Formal items to preserve: none -- all covered in fol/seq/*
  - Formal items to drop: all explain blocks -- redundant
  - Prose: cut all
  - Examples: cut all -- worked derivation example redundant with fol/seq/pro
  - Proofs: N/A

---

### fol/prf/tab — Tableaux (proof-systems overview)
- **Action**: CUT
- **Lean Chapter**: CH-DED
- **Lean Section**: N/A
- **Rationale**: Signal is PEDAGOGICAL (REDUNDANT-WITH: fol/tab chapter). Everything here is covered more formally in fol/tab/rul, fol/tab/prl. No unique formal content.
- **Content Directives**:
  - Formal items to preserve: none -- all covered in fol/tab/*
  - Formal items to drop: all explain blocks -- redundant
  - Prose: cut all
  - Examples: cut all
  - Proofs: N/A

---

### Chapter: axiomatic-deduction

### fol/axd/rul — Rules and Derivation
- **Action**: KEEP
- **Lean Chapter**: CH-DED
- **Lean Section**: DED.1: Generic Proof-Theoretic Concepts (authoritative for PRIM-DED001, PRIM-DED002)
- **Rationale**: Signal is CORE-DEF. Authoritative defining occurrence of PRIM-DED001 (Rule of Inference) and PRIM-DED005 (Derivation) at the generic level. Contains two defn blocks (derivation, rule of inference) plus the derived definitions of derivability and theorem. By A1 decision, the generic definitions from this section become DED.1 content; the axiomatic-specific instantiation (sequence-based derivation) goes to DED.2.
- **Content Directives**:
  - Formal items to preserve: `defn[Derivability]` (generic derivation definition -- PRIM-DED005); `defn[Rule of inference]` (PRIM-DED001); second `defn[Derivability]` (provability relation Gamma |- A); `defn[Theorems]` (PRIM-DED010)
  - Formal items to drop: modus ponens informal example in explain block -- moves to DED.2 as instantiation
  - Prose: split into two: (a) DED.1 gets the abstract framing (derivation as structured object, rule of inference as pattern); (b) DED.2 gets the Hilbert instantiation (derivation as finite sequence)
  - Examples: cut all -- the modus ponens example is pedagogical
  - Proofs: N/A

---

### fol/axd/prp — Axioms and Rules for Propositional Connectives
- **Action**: KEEP
- **Lean Chapter**: CH-DED
- **Lean Section**: DED.2: Axiomatic (Hilbert) Systems
- **Rationale**: Signal is CORE-DEF. Sole defining occurrence of AX-DED003 (Logical Axiom Schemas, propositional part), AX-DED001 (Modus Ponens), and DEF-DED005 (Hilbert-Style Proof System). Specifies the 14 propositional axiom schemas and the MP rule. Essential system specification for DED.2.
- **Content Directives**:
  - Formal items to preserve: all 14 axiom schema definitions (AX-DED003 propositional fragment); `defn[Modus ponens]` (AX-DED001)
  - Formal items to drop: none -- all are essential system specification
  - Prose: compress to intro + definitions only
  - Examples: cut all
  - Proofs: N/A

---

### fol/axd/qua — Axioms and Rules for Quantifiers
- **Action**: KEEP
- **Lean Chapter**: CH-DED
- **Lean Section**: DED.2: Axiomatic (Hilbert) Systems
- **Rationale**: Signal is CORE-DEF. Sole defining occurrence of AX-DED003 (quantifier axiom schemas) and AX-DED002 (Universal Generalization / QR rule). Completes the specification of the Hilbert system for FOL.
- **Content Directives**:
  - Formal items to preserve: quantifier axiom schemas (Q1, Q2); `defn[Rules for quantifiers]` (QR / AX-DED002)
  - Formal items to drop: none
  - Prose: compress to intro + definitions only
  - Examples: cut all
  - Proofs: N/A

---

### fol/axd/ptn — Proof-Theoretic Notions (Axiomatic)
- **Action**: ABSORB:fol/ntd/ptn,fol/seq/ptn,fol/tab/ptn
- **Lean Chapter**: CH-DED
- **Lean Section**: DED.1: Generic Proof-Theoretic Concepts (authoritative for PRIM-DED003, PRIM-DED004, DEF-DED001)
- **Rationale**: Signal is CORE-DEF. By A1 decision, this section becomes the authoritative home for the generic proof-theoretic notions: Provability (PRIM-DED003/006), Theorem (PRIM-DED010), Consistency (DEF-DED001), and the 5 structural properties (reflexivity, monotonicity, transitivity, inconsistency characterization, compactness). The 3 parallel ptn sections (NTD, SC, Tab) all define identical concepts with system-specific proof details. This section absorbs them: the generic definitions go to DED.1; system-specific proof sketches are noted as remarks in DED.2-5.
- **Content Directives**:
  - Formal items to preserve: `defn[Derivability]` (PRIM-DED006); `defn[Theorems]` (PRIM-DED010); `defn[Consistency]` (DEF-DED001); `prop[Reflexivity]` with proof; `prop[Monotonicity]` with proof; `prop[Transitivity]` with proof; `prop[incons]` (statement); `prop[Compactness]` with proof
  - Formal items to drop: exercises (prob blocks) -- pedagogical
  - Prose: generalize away from axiomatic-specific language; replace "derivation" with proof-system-neutral language where needed; add remark noting that each proof system instantiates these properties (the proof of transitivity differs: AXD uses sequence concatenation, NTD uses implication-intro + elim, SC uses cut, Tab uses cut rule)
  - Examples: cut all
  - Proofs: preserve full for reflexivity, monotonicity (trivial); preserve full for transitivity (using the AXD proof as template, noting variants); preserve full for compactness; cut inconsistency characterization proof (exercise)

---

### fol/axd/ded — Deduction Theorem
- **Action**: KEEP + ABSORB:{fol/axd/ddq}
- **Lean Chapter**: CH-DED
- **Lean Section**: DED.2: Axiomatic (Hilbert) Systems
- **Rationale**: Signal is CORE-THM. Sole defining occurrence of THM-DED001 (Deduction Theorem) and CP-009 (Deduction Theorem as composition pattern). Central metatheorem for the Hilbert system. This is specific to DED.2 (ND and SC do not need a separate deduction theorem -- it is built into the system design).
- **Content Directives**:
  - Formal items to preserve: `prop[mp]` (meta-MP -- AX-DED001 at meta-level); `thm[deduction-thm]` (THM-DED001 / CP-009) with full proof
  - Formal items to drop: `prop[derivfacts]` -- OL-ONLY derived facts (contraposition, explosion, DNE); these are exercises and not taxonomy items
  - Prose: compress intro; preserve the remark about why axioms lif1 and lif2 were chosen to make the Deduction Theorem work
  - Examples: cut all
  - Proofs: preserve full -- the induction on derivation length is the canonical proof of THM-DED001

---

### fol/axd/ddq — Deduction Theorem with Quantifiers
- **Action**: MERGE-INTO:fol/axd/ded
- **Lean Chapter**: CH-DED
- **Lean Section**: DED.2: Axiomatic (Hilbert) Systems
- **Rationale**: Signal is STEPPING-STONE. Extends THM-DED001 to handle the QR rule. The lean text should present the full FOL version of the Deduction Theorem in one place. The additional QR case is a straightforward extension of the inductive proof.
- **Content Directives**:
  - Formal items to preserve: `thm[deduction-thm-q]` -- statement of the FOL extension (merge as additional case in fol/axd/ded's proof)
  - Formal items to drop: none
  - Prose: replace with cross-ref to extended proof in fol/axd/ded
  - Examples: cut all
  - Proofs: merge the QR case into fol/axd/ded's proof as an additional inductive case

---

### fol/axd/prv — Derivability and Consistency (Axiomatic)
- **Action**: KEEP + ABSORB:{fol/ntd/prv, fol/seq/prv, fol/tab/prv}
- **Lean Chapter**: CH-DED
- **Lean Section**: DED.1: Generic Proof-Theoretic Concepts (authoritative for consistency properties)
- **Rationale**: Signal is STEPPING-STONE. Contains 4 propositions about the derivability/consistency relationship needed for completeness. By A1, these are generic results (they hold for all 4 proof systems). This section is authoritative; the 3 parallel prv sections (NTD, SC, Tab) merge into it.
- **Content Directives**:
  - Formal items to preserve: `prop[provability-contr]` with proof; `prop[prov-incons]` with proof; `prop[explicit-inc]` with proof; `prop[provability-exhaustive]` (statement)
  - Formal items to drop: exercises (prob blocks)
  - Prose: generalize language to be proof-system-neutral; note that proofs use the Deduction Theorem (which in ND is built-in, in SC uses cut)
  - Examples: cut all
  - Proofs: preserve full for provability-contr, prov-incons, explicit-inc; cut exhaustive (exercise)

---

### fol/axd/ppr — Derivability and Propositional Connectives (Axiomatic)
- **Action**: CONDENSE + ABSORB:{fol/ntd/ppr, fol/seq/ppr, fol/tab/ppr}
- **Lean Chapter**: CH-DED
- **Lean Section**: DED.2: Axiomatic (Hilbert) Systems
- **Rationale**: Signal is STEPPING-STONE. Establishes derivability facts for connectives needed for completeness. These are system-specific technical results (they use the specific Hilbert axioms). The generic results (that each system can derive these) follow from equivalence of proof systems. Keep statements, condense proofs to sketches.
- **Content Directives**:
  - Formal items to preserve: `prop[provability-land]` (statement); `prop[provability-lor]` (statement); `prop[provability-lif]` (statement)
  - Formal items to drop: none
  - Prose: compress to statements + one-line proof sketch each
  - Examples: cut all
  - Proofs: preserve sketch only -- each uses axiom schemas + Deduction Theorem + meta-MP

---

### fol/axd/qpr — Derivability and Quantifiers (Axiomatic)
- **Action**: CONDENSE + ABSORB:{fol/ntd/qpr, fol/seq/qpr, fol/tab/qpr}
- **Lean Chapter**: CH-DED
- **Lean Section**: DED.2: Axiomatic (Hilbert) Systems
- **Rationale**: Signal is STEPPING-STONE. Establishes quantifier derivability facts needed for completeness. FOL-only. System-specific proofs using QR and quantifier axioms.
- **Content Directives**:
  - Formal items to preserve: `thm[strong-generalization]` (statement); `prop[provability-quantifiers]` (statement)
  - Formal items to drop: none
  - Prose: compress to statements + one-line proof sketch each
  - Examples: cut all
  - Proofs: preserve sketch only

---

### fol/axd/sou — Soundness (Axiomatic)
- **Action**: KEEP
- **Lean Chapter**: CH-DED
- **Lean Section**: DED.2: Axiomatic (Hilbert) Systems
- **Rationale**: Signal is CORE-THM. Introduces CP-001 (Soundness Theorem) for the Hilbert system. Per architectural decision, each proof system's soundness proof stays in its own DED.2-5 section. The Hilbert soundness proof is the simplest (induction on derivation length with only MP and QR cases).
- **Content Directives**:
  - Formal items to preserve: `prop` (axioms are valid -- stepping stone); `thm[soundness]` (CP-001: Gamma |- A implies Gamma |= A) with full proof; `cor[weak-soundness]`; `cor[consistency-soundness]` with proof
  - Formal items to drop: exercises (prob block for QR case)
  - Prose: preserve explain block (it motivates what soundness means); compress slightly
  - Examples: cut all
  - Proofs: preserve full -- canonical induction argument; include QR case (merge from exercise)

---

### fol/axd/ide — Derivation with Identity (Axiomatic)
- **Action**: CUT
- **Lean Chapter**: CH-DED
- **Lean Section**: N/A
- **Rationale**: Signal is PEDAGOGICAL. Adds identity axioms as a simple extension. The identity axioms are already specified as part of AX-DED003 (A6, A7) in the taxonomy's axiom schema list. No unique taxonomy items introduced. The soundness of identity axioms follows from the main soundness theorem.
- **Content Directives**:
  - Formal items to preserve: none -- identity axioms already in AX-DED003
  - Formal items to drop: all -- pedagogical extension
  - Prose: cut all
  - Examples: cut all
  - Proofs: cut all

---

### fol/axd/pro — Examples of Derivation (Axiomatic)
- **Action**: CUT
- **Lean Chapter**: CH-DED
- **Lean Section**: N/A
- **Rationale**: Signal is PEDAGOGICAL. Purely pedagogical worked examples showing how to construct Hilbert derivations. No taxonomy items introduced. The identity derivation (D -> D) is referenced by fol/axd/ded, but that proof can be stated inline.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: all examples -- pedagogical
  - Prose: cut all
  - Examples: cut all
  - Proofs: cut all

---

### fol/axd/prq — Derivation with Quantifiers (Axiomatic)
- **Action**: CUT
- **Lean Chapter**: CH-DED
- **Lean Section**: N/A
- **Rationale**: Signal is PEDAGOGICAL. Worked examples of quantifier derivations in the Hilbert system. No taxonomy items.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: all examples -- pedagogical
  - Prose: cut all
  - Examples: cut all
  - Proofs: cut all

---

### Chapter: natural-deduction

### fol/ntd/rul — Rules and Derivation (ND)
- **Action**: KEEP
- **Lean Chapter**: CH-DED
- **Lean Section**: DED.3: Natural Deduction (also contributes PRIM-DED009 to DED.1)
- **Rationale**: Signal is CORE-DEF. Introduces PRIM-DED009 (Assumption Discharge) and DEF-DED006 (Natural Deduction System). The assumption discharge concept is unique to ND and goes to DED.1 as a generic concept. The system-specific framing (tree-structured derivations, intro/elim pattern) goes to DED.3.
- **Content Directives**:
  - Formal items to preserve: `defn[Assumption]` (top-level sentence notion); explain block on discharge mechanism (PRIM-DED009); the intro/elim rule pattern description
  - Formal items to drop: none
  - Prose: preserve -- foundational framing for ND system
  - Examples: cut all
  - Proofs: N/A

---

### fol/ntd/prl — Propositional Rules (ND)
- **Action**: KEEP
- **Lean Chapter**: CH-DED
- **Lean Section**: DED.3: Natural Deduction
- **Rationale**: Signal is CORE-DEF. Sole defining occurrence of DEF-DED006 (Natural Deduction System, propositional part). Specifies all propositional intro/elim rule pairs. Essential system specification for DED.3.
- **Content Directives**:
  - Formal items to preserve: all rule displays (conjunction-I/E, disjunction-I/E, implication-I/E, negation-I/E, FalseInt, FalseCl)
  - Formal items to drop: none -- all are system specification
  - Prose: compress to intro + rule displays
  - Examples: cut all
  - Proofs: N/A

---

### fol/ntd/qrl — Quantifier Rules (ND)
- **Action**: KEEP
- **Lean Chapter**: CH-DED
- **Lean Section**: DED.3: Natural Deduction
- **Rationale**: Signal is CORE-DEF. Extends DEF-DED006 with quantifier rules. Introduces eigenvariable condition (PRIM-DED007 instance). FOL-only.
- **Content Directives**:
  - Formal items to preserve: all rule displays (forall-I/E, exists-I/E); eigenvariable condition statement
  - Formal items to drop: none
  - Prose: compress to intro + rule displays; preserve eigenvariable explanation
  - Examples: cut all
  - Proofs: N/A

---

### fol/ntd/der — Derivations (ND)
- **Action**: CONDENSE
- **Lean Chapter**: CH-DED
- **Lean Section**: DED.3: Natural Deduction
- **Rationale**: Signal is CORE-DEF. Formal definition of PRIM-DED005 (Derivation, ND version) as tree structure. Contains a key `defn[Derivation]` block plus extensive examples. The definition is essential; the examples are pedagogical. Condense to definition only.
- **Content Directives**:
  - Formal items to preserve: `defn[Derivation]` (tree-structured derivation from assumptions -- PRIM-DED005 ND instantiation); the sentence defining $\Gamma \Proves !A$ notation
  - Formal items to drop: all examples (ex block) -- pedagogical
  - Prose: compress to intro + definition only
  - Examples: cut all -- pedagogical (conjunction-intro, implication-intro worked examples)
  - Proofs: N/A

---

### fol/ntd/ptn — Proof-Theoretic Notions (ND)
- **Action**: MERGE-INTO:fol/axd/ptn
- **Lean Chapter**: CH-DED
- **Lean Section**: DED.1: Generic Proof-Theoretic Concepts (absorbed by fol/axd/ptn)
- **Rationale**: Signal is CORE-DEF but REDUNDANT-WITH fol/axd/ptn. Defines identical concepts (Theorem, Derivability, Consistency) plus identical structural properties (reflexivity, monotonicity, transitivity, inconsistency characterization, compactness) for ND. By A1 decision, the generic definitions are authoritative in fol/axd/ptn. The ND-specific proof of transitivity (using implication-intro/elim instead of sequence concatenation) is noted as a remark in DED.3.
- **Content Directives**:
  - Formal items to preserve: none standalone -- all definitions absorbed by fol/axd/ptn
  - Formal items to drop: all definitions and propositions -- redundant with authoritative section
  - Prose: replace with cross-ref to DED.1; add one-line remark in DED.3 noting that transitivity in ND uses implication-intro + elim (the proof tree construction)
  - Examples: cut all
  - Proofs: cut (absorbed; ND transitivity proof noted as remark)

---

### fol/ntd/sou — Soundness (ND)
- **Action**: KEEP + ABSORB:{fol/ntd/sid}
- **Lean Chapter**: CH-DED
- **Lean Section**: DED.3: Natural Deduction
- **Rationale**: Signal is CORE-THM. Introduces CP-001 (Soundness) for ND. Per architectural decision, each system's soundness proof stays in its own section. The ND soundness proof is by induction on derivation tree structure with one case per rule (larger than AXD but structurally important).
- **Content Directives**:
  - Formal items to preserve: `thm[soundness]` (CP-001 ND variant) with proof; `cor[weak-soundness]`; `cor[consistency-soundness]`
  - Formal items to drop: exercises
  - Prose: compress explain block
  - Examples: cut all
  - Proofs: preserve full -- each rule case is a separate verification

---

### fol/ntd/prv — Derivability and Consistency (ND)
- **Action**: MERGE-INTO:fol/axd/prv
- **Lean Chapter**: CH-DED
- **Lean Section**: DED.1: Generic Proof-Theoretic Concepts (absorbed by fol/axd/prv)
- **Rationale**: Signal is STEPPING-STONE but REDUNDANT-WITH fol/axd/prv. Same 4 propositions proved for ND. By A1, the generic statements are authoritative in fol/axd/prv. ND-specific proof techniques noted as remarks.
- **Content Directives**:
  - Formal items to preserve: none standalone
  - Formal items to drop: all 4 propositions -- redundant
  - Prose: replace with cross-ref to DED.1
  - Examples: cut all
  - Proofs: cut (absorbed)

---

### fol/ntd/ppr — Derivability and Propositional Connectives (ND)
- **Action**: MERGE-INTO:fol/axd/ppr
- **Lean Chapter**: CH-DED
- **Lean Section**: DED.1: Generic Proof-Theoretic Concepts (absorbed by fol/axd/ppr as generic statement)
- **Rationale**: Signal is STEPPING-STONE but REDUNDANT-WITH fol/axd/ppr. Same connective derivability facts proved using ND rules instead of Hilbert axioms. By A1, the statements are generic (they hold for any adequate proof system). The ND-specific proofs are not needed since equivalence of systems guarantees the results.
- **Content Directives**:
  - Formal items to preserve: none standalone
  - Formal items to drop: all propositions -- redundant
  - Prose: replace with cross-ref
  - Examples: cut all
  - Proofs: cut

---

### fol/ntd/qpr — Derivability and Quantifiers (ND)
- **Action**: MERGE-INTO:fol/axd/qpr
- **Lean Chapter**: CH-DED
- **Lean Section**: DED.1: Generic Proof-Theoretic Concepts (absorbed by fol/axd/qpr as generic statement)
- **Rationale**: Signal is STEPPING-STONE but REDUNDANT-WITH fol/axd/qpr. Same quantifier derivability facts for ND. FOL-only.
- **Content Directives**:
  - Formal items to preserve: none standalone
  - Formal items to drop: all -- redundant
  - Prose: replace with cross-ref
  - Examples: cut all
  - Proofs: cut

---

### fol/ntd/ide — Derivation with Identity (ND)
- **Action**: CUT
- **Lean Chapter**: CH-DED
- **Lean Section**: N/A
- **Rationale**: Signal is PEDAGOGICAL. Adds identity intro/elim rules to ND. Simple extension pattern with no unique taxonomy items. Identity rules are specified generically in the taxonomy.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: all -- pedagogical extension
  - Prose: cut all
  - Examples: cut all
  - Proofs: cut all

---

### fol/ntd/sid — Soundness with Identity (ND)
- **Action**: MERGE-INTO:fol/ntd/sou
- **Lean Chapter**: CH-DED
- **Lean Section**: DED.3: Natural Deduction
- **Rationale**: Signal is STEPPING-STONE. Extends ND soundness proof to handle identity rules. Should be merged as additional cases in the main ND soundness proof (fol/ntd/sou).
- **Content Directives**:
  - Formal items to preserve: identity rule soundness cases -- merge as additional cases in fol/ntd/sou proof
  - Formal items to drop: none
  - Prose: replace with cross-ref
  - Examples: cut all
  - Proofs: merge into fol/ntd/sou proof

---

### fol/ntd/pro — Examples of Derivation (ND)
- **Action**: CUT
- **Lean Chapter**: CH-DED
- **Lean Section**: N/A
- **Rationale**: Signal is PEDAGOGICAL. Purely pedagogical worked examples of ND proofs. No taxonomy items.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: all examples -- pedagogical
  - Prose: cut all
  - Examples: cut all
  - Proofs: cut all

---

### fol/ntd/prq — Derivation with Quantifiers (ND)
- **Action**: CUT
- **Lean Chapter**: CH-DED
- **Lean Section**: N/A
- **Rationale**: Signal is PEDAGOGICAL. Worked examples of quantifier reasoning in ND. No taxonomy items.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: all examples -- pedagogical
  - Prose: cut all
  - Examples: cut all
  - Proofs: cut all

---

### Chapter: sequent-calculus

### fol/seq/rul — Rules and Derivations (SC)
- **Action**: KEEP
- **Lean Chapter**: CH-DED
- **Lean Section**: DED.4: Sequent Calculus (also contributes PRIM-DED008 to DED.1)
- **Rationale**: Signal is CORE-DEF. Sole formal defining occurrence of PRIM-DED008 (Sequent) and DEF-DED007 (Sequent Calculus). Contains `defn[Sequent]` and `defn[Initial Sequent]`. The sequent concept is unique to SC and goes to DED.1 as a generic concept. The system-specific framing goes to DED.4.
- **Content Directives**:
  - Formal items to preserve: `defn[Sequent]` (PRIM-DED008: antecedent/succedent notation); `defn[Initial Sequent]` (axiom for PRIM-DED004); explain block on sequent intuition (conjunction-of-antecedents implies disjunction-of-succedents)
  - Formal items to drop: none
  - Prose: preserve -- foundational for SC system
  - Examples: cut all
  - Proofs: N/A

---

### fol/seq/prl — Propositional Rules (SC)
- **Action**: KEEP
- **Lean Chapter**: CH-DED
- **Lean Section**: DED.4: Sequent Calculus
- **Rationale**: Signal is CORE-DEF. Specifies all propositional left/right rules for LK. Essential system specification for DED.4.
- **Content Directives**:
  - Formal items to preserve: all rule displays (negation-L/R, conjunction-L/R, disjunction-L/R, implication-L/R)
  - Formal items to drop: none -- all are system specification
  - Prose: compress to intro + rule displays
  - Examples: cut all
  - Proofs: N/A

---

### fol/seq/srl — Structural Rules (SC)
- **Action**: KEEP
- **Lean Chapter**: CH-DED
- **Lean Section**: DED.4: Sequent Calculus (also contributes PRIM-DED007 to DED.1)
- **Rationale**: Signal is CORE-DEF. Sole formal defining occurrence of PRIM-DED007 (Structural Rules: Weakening, Contraction, Exchange) and the Cut rule (CP-010 stated informally as admissible). The structural rule concepts go to DED.1 as generic concepts. The specific SC formulations go to DED.4. Note: CP-010 (Cut Elimination / Hauptsatz) is only mentioned informally here; the full proof is absent from OL.
- **Content Directives**:
  - Formal items to preserve: all defish blocks (Weakening-L/R, Contraction-L/R, Exchange-L/R, Cut); remark that Cut is admissible (informal statement of THM-DED003)
  - Formal items to drop: none
  - Prose: preserve -- concise rule specifications
  - Examples: cut all
  - Proofs: N/A (no proofs in this section; Cut admissibility is stated without proof)

---

### fol/seq/qrl — Quantifier Rules (SC)
- **Action**: KEEP
- **Lean Chapter**: CH-DED
- **Lean Section**: DED.4: Sequent Calculus
- **Rationale**: Signal is CORE-DEF. Extends LK with quantifier left/right rules and eigenvariable conditions. FOL-only.
- **Content Directives**:
  - Formal items to preserve: all rule displays (forall-L/R, exists-L/R); eigenvariable condition statement
  - Formal items to drop: none
  - Prose: compress to intro + rule displays; preserve eigenvariable explanation
  - Examples: cut all
  - Proofs: N/A

---

### fol/seq/der — Derivations (SC)
- **Action**: CONDENSE
- **Lean Chapter**: CH-DED
- **Lean Section**: DED.4: Sequent Calculus
- **Rationale**: Signal is CORE-DEF. Formal definition of PRIM-DED005 (Derivation, SC version) as tree of sequents. Contains definition plus worked examples. Condense to definition only.
- **Content Directives**:
  - Formal items to preserve: `defn[LK-derivation]` (PRIM-DED005 SC instantiation)
  - Formal items to drop: worked examples (ex block) -- pedagogical
  - Prose: compress to intro + definition only
  - Examples: cut all
  - Proofs: N/A

---

### fol/seq/ptn — Proof-Theoretic Notions (SC)
- **Action**: MERGE-INTO:fol/axd/ptn
- **Lean Chapter**: CH-DED
- **Lean Section**: DED.1: Generic Proof-Theoretic Concepts (absorbed by fol/axd/ptn)
- **Rationale**: Signal is CORE-DEF but REDUNDANT-WITH fol/axd/ptn. Defines identical concepts (Theorem, Derivability, Consistency) plus identical structural properties for SC. By A1 decision, absorbed by fol/axd/ptn. The SC-specific definition of derivability (via finite subsets and sequents rather than derivation sequences) is noted as a remark in DED.4. Also introduces DEF-DED003 (Deductive Closure) -- this is absorbed into the generic section.
- **Content Directives**:
  - Formal items to preserve: none standalone -- all absorbed by fol/axd/ptn; the SC-specific derivability definition (using sequent notation) is noted as a remark in DED.4
  - Formal items to drop: all -- redundant
  - Prose: replace with cross-ref to DED.1; add remark in DED.4 noting SC-specific derivability definition (via Gamma_0 Sequent A)
  - Examples: cut all
  - Proofs: cut (SC transitivity via Cut is noted as remark in DED.4)

---

### fol/seq/prv — Derivability and Consistency (SC)
- **Action**: MERGE-INTO:fol/axd/prv
- **Lean Chapter**: CH-DED
- **Lean Section**: DED.1: Generic Proof-Theoretic Concepts (absorbed by fol/axd/prv)
- **Rationale**: Signal is STEPPING-STONE but REDUNDANT-WITH fol/axd/prv. Same 4 consistency/derivability propositions for SC.
- **Content Directives**:
  - Formal items to preserve: none standalone
  - Formal items to drop: all -- redundant
  - Prose: replace with cross-ref
  - Examples: cut all
  - Proofs: cut

---

### fol/seq/ppr — Derivability and Propositional Connectives (SC)
- **Action**: MERGE-INTO:fol/axd/ppr
- **Lean Chapter**: CH-DED
- **Lean Section**: DED.1: Generic Proof-Theoretic Concepts (absorbed)
- **Rationale**: Signal is STEPPING-STONE but REDUNDANT-WITH fol/axd/ppr. Same connective derivability facts for SC.
- **Content Directives**:
  - Formal items to preserve: none standalone
  - Formal items to drop: all -- redundant
  - Prose: replace with cross-ref
  - Examples: cut all
  - Proofs: cut

---

### fol/seq/qpr — Derivability and Quantifiers (SC)
- **Action**: MERGE-INTO:fol/axd/qpr
- **Lean Chapter**: CH-DED
- **Lean Section**: DED.1: Generic Proof-Theoretic Concepts (absorbed)
- **Rationale**: Signal is STEPPING-STONE but REDUNDANT-WITH fol/axd/qpr. Same quantifier derivability facts for SC. FOL-only.
- **Content Directives**:
  - Formal items to preserve: none standalone
  - Formal items to drop: all -- redundant
  - Prose: replace with cross-ref
  - Examples: cut all
  - Proofs: cut

---

### fol/seq/sou — Soundness (SC)
- **Action**: KEEP + ABSORB:{fol/seq/sid}
- **Lean Chapter**: CH-DED
- **Lean Section**: DED.4: Sequent Calculus
- **Rationale**: Signal is CORE-THM. Introduces CP-001 (Soundness) for SC. Per architectural decision, each system's soundness proof stays in its own section. Includes the definition of valid sequent (semantic notion specific to SC).
- **Content Directives**:
  - Formal items to preserve: `defn[valid sequent]` (semantic notion for sequents); `thm[sequent-soundness]` (CP-001 SC variant) with proof; `cor[weak-soundness]`; `cor[entailment-soundness]`; `cor[consistency-soundness]`
  - Formal items to drop: none
  - Prose: compress explain block
  - Examples: cut all
  - Proofs: preserve full -- induction on derivation structure

---

### fol/seq/ide — Derivations with Identity (SC)
- **Action**: CONDENSE
- **Lean Chapter**: CH-DED
- **Lean Section**: DED.4: Sequent Calculus
- **Rationale**: Signal is CORE-DEF. Extends LK with identity initial sequents and rules. Unlike the AXD and NTD identity sections (which are PEDAGOGICAL), this section formally specifies the identity extension rules for SC, which have a distinctive form (initial sequents for =).
- **Content Directives**:
  - Formal items to preserve: `defn[Initial sequents for =]` (identity axiom for SC); identity rule defish blocks
  - Formal items to drop: worked examples (Leibniz's Law, symmetry, transitivity) -- pedagogical
  - Prose: compress to rule specification only
  - Examples: cut all
  - Proofs: cut all (identity properties)

---

### fol/seq/sid — Soundness with Identity (SC)
- **Action**: MERGE-INTO:fol/seq/sou
- **Lean Chapter**: CH-DED
- **Lean Section**: DED.4: Sequent Calculus
- **Rationale**: Signal is STEPPING-STONE. Extends SC soundness to identity rules. Should be merged as additional cases in fol/seq/sou.
- **Content Directives**:
  - Formal items to preserve: identity rule soundness cases -- merge into fol/seq/sou proof
  - Formal items to drop: none
  - Prose: replace with cross-ref
  - Examples: cut all
  - Proofs: merge into fol/seq/sou

---

### fol/seq/pro — Examples of Derivations (SC)
- **Action**: CUT
- **Lean Chapter**: CH-DED
- **Lean Section**: N/A
- **Rationale**: Signal is PEDAGOGICAL. Worked examples of SC derivations. No taxonomy items.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: all examples and exercises -- pedagogical
  - Prose: cut all
  - Examples: cut all
  - Proofs: cut all

---

### fol/seq/prq — Derivations with Quantifiers (SC)
- **Action**: CUT
- **Lean Chapter**: CH-DED
- **Lean Section**: N/A
- **Rationale**: Signal is PEDAGOGICAL. Worked examples of quantifier SC derivations. FOL-only. No taxonomy items.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: all examples and exercises -- pedagogical
  - Prose: cut all
  - Examples: cut all
  - Proofs: cut all

---

### Chapter: tableaux

### fol/tab/rul — Rules and Tableaux
- **Action**: KEEP
- **Lean Chapter**: CH-DED
- **Lean Section**: DED.5: Tableaux
- **Rationale**: Signal is CORE-DEF. Introduces DEF-DED008 (Tableau System) and PRIM-DED005 (Tableau derivation). Defines signed formulas, closed branches, and closed tableaux. Essential system specification for DED.5.
- **Content Directives**:
  - Formal items to preserve: `defn` (signed formula: T:A and F:A); explain on closed branches and closed tableaux; explain on closed tableau for A (root F:A)
  - Formal items to drop: none
  - Prose: preserve -- foundational for tableau system
  - Examples: cut all
  - Proofs: N/A

---

### fol/tab/prl — Propositional Rules (Tableaux)
- **Action**: KEEP
- **Lean Chapter**: CH-DED
- **Lean Section**: DED.5: Tableaux
- **Rationale**: Signal is CORE-DEF. Specifies all propositional tableau rules. Essential system specification for DED.5.
- **Content Directives**:
  - Formal items to preserve: all defish blocks (T-negation, F-negation, T-conjunction, F-conjunction, T-disjunction, F-disjunction, T-implication, F-implication, Cut)
  - Formal items to drop: none -- all are system specification
  - Prose: compress to intro + rule displays; note Cut as admissible but included for convenience
  - Examples: cut all
  - Proofs: N/A

---

### fol/tab/qrl — Quantifier Rules (Tableaux)
- **Action**: KEEP
- **Lean Chapter**: CH-DED
- **Lean Section**: DED.5: Tableaux
- **Rationale**: Signal is CORE-DEF. Extends tableau with quantifier rules. FOL-only. Includes eigenvariable conditions.
- **Content Directives**:
  - Formal items to preserve: all defish blocks (T-forall, F-forall, T-exists, F-exists); eigenvariable condition statement
  - Formal items to drop: none
  - Prose: compress to intro + rule displays; preserve eigenvariable explanation
  - Examples: cut all
  - Proofs: N/A

---

### fol/tab/der — Tableaux (derivations)
- **Action**: CONDENSE
- **Lean Chapter**: CH-DED
- **Lean Section**: DED.5: Tableaux
- **Rationale**: Signal is CORE-DEF. Formal definition of PRIM-DED005 (Derivation, tableau version) as tree of signed formulas with closure criterion. Contains definition plus worked examples. Condense to definition only.
- **Content Directives**:
  - Formal items to preserve: `defn[tableau]` (PRIM-DED005 tableau instantiation)
  - Formal items to drop: worked examples (ex block) -- pedagogical
  - Prose: compress to intro + definition only
  - Examples: cut all
  - Proofs: N/A

---

### fol/tab/ptn — Proof-Theoretic Notions (Tableaux)
- **Action**: MERGE-INTO:fol/axd/ptn
- **Lean Chapter**: CH-DED
- **Lean Section**: DED.1: Generic Proof-Theoretic Concepts (absorbed by fol/axd/ptn)
- **Rationale**: Signal is CORE-DEF (REDUNDANT-WITH fol/axd/ptn). Defines identical concepts (Theorem, Derivability, Consistency) plus identical structural properties for tableaux. By A1 decision, absorbed by fol/axd/ptn. The tableau-specific definitions (derivability via closed tableaux, consistency via absence of closed tableaux) are noted as remarks in DED.5. Particularly notable: tableau consistency is defined differently (no closed tableau for T-signed assumptions rather than non-derivability of falsum).
- **Content Directives**:
  - Formal items to preserve: none standalone -- absorbed by fol/axd/ptn; the tableau-specific derivability and consistency definitions are noted as remarks in DED.5
  - Formal items to drop: all -- redundant
  - Prose: replace with cross-ref to DED.1; add remark in DED.5 for the tableau-specific definition of consistency (closed tableau formulation)
  - Examples: cut all
  - Proofs: cut (tableau transitivity via Cut rule noted as remark in DED.5)

---

### fol/tab/prv — Derivability and Consistency (Tableaux)
- **Action**: MERGE-INTO:fol/axd/prv
- **Lean Chapter**: CH-DED
- **Lean Section**: DED.1: Generic Proof-Theoretic Concepts (absorbed by fol/axd/prv)
- **Rationale**: Signal is STEPPING-STONE (REDUNDANT-WITH fol/axd/prv). Same 4 consistency/derivability propositions for tableaux.
- **Content Directives**:
  - Formal items to preserve: none standalone
  - Formal items to drop: all -- redundant
  - Prose: replace with cross-ref
  - Examples: cut all
  - Proofs: cut

---

### fol/tab/ppr — Derivability and Propositional Connectives (Tableaux)
- **Action**: MERGE-INTO:fol/axd/ppr
- **Lean Chapter**: CH-DED
- **Lean Section**: DED.1: Generic Proof-Theoretic Concepts (absorbed)
- **Rationale**: Signal is STEPPING-STONE (REDUNDANT-WITH fol/axd/ppr). Same connective derivability facts for tableaux.
- **Content Directives**:
  - Formal items to preserve: none standalone
  - Formal items to drop: all -- redundant
  - Prose: replace with cross-ref
  - Examples: cut all
  - Proofs: cut

---

### fol/tab/qpr — Derivability and Quantifiers (Tableaux)
- **Action**: MERGE-INTO:fol/axd/qpr
- **Lean Chapter**: CH-DED
- **Lean Section**: DED.1: Generic Proof-Theoretic Concepts (absorbed)
- **Rationale**: Signal is STEPPING-STONE (REDUNDANT-WITH fol/axd/qpr). Same quantifier derivability facts for tableaux. FOL-only.
- **Content Directives**:
  - Formal items to preserve: none standalone
  - Formal items to drop: all -- redundant
  - Prose: replace with cross-ref
  - Examples: cut all
  - Proofs: cut

---

### fol/tab/sou — Soundness (Tableaux)
- **Action**: KEEP + ABSORB:{fol/tab/sid}
- **Lean Chapter**: CH-DED
- **Lean Section**: DED.5: Tableaux
- **Rationale**: Signal is CORE-THM (REDUNDANT-WITH fol/seq/sou for the result, but proof strategy differs). Introduces CP-001 (Soundness) for tableaux. Per architectural decision, each system's soundness proof stays in its own section. The tableau soundness proof uses branch satisfaction (different from induction-on-derivation in other systems).
- **Content Directives**:
  - Formal items to preserve: `defn[satisfies signed formula]` (semantic notion specific to tableaux); `thm[tableau-soundness]` (CP-001 tableau variant) with proof; corollaries (weak-soundness, entailment-soundness, consistency-soundness)
  - Formal items to drop: none
  - Prose: compress explain block
  - Examples: cut all
  - Proofs: preserve full -- branch satisfaction argument is distinctive

---

### fol/tab/ide — Tableaux with Identity
- **Action**: CONDENSE
- **Lean Chapter**: CH-DED
- **Lean Section**: DED.5: Tableaux
- **Rationale**: Signal is CORE-DEF (REDUNDANT-WITH fol/seq/ide for concepts, but tableau-specific formulation). Extends tableau with identity rules. The tableau identity rules (T=, F=) have a distinctive form that differs from SC identity rules.
- **Content Directives**:
  - Formal items to preserve: identity rule defish blocks (= rule, T=, F=)
  - Formal items to drop: worked examples (Leibniz's Law, symmetry, transitivity) -- pedagogical
  - Prose: compress to rule specification only
  - Examples: cut all
  - Proofs: cut all

---

### fol/tab/sid — Soundness with Identity (Tableaux)
- **Action**: MERGE-INTO:fol/tab/sou
- **Lean Chapter**: CH-DED
- **Lean Section**: DED.5: Tableaux
- **Rationale**: Signal is STEPPING-STONE (REDUNDANT-WITH fol/seq/sid). Extends tableau soundness to identity rules. Merge as additional cases in fol/tab/sou.
- **Content Directives**:
  - Formal items to preserve: identity rule soundness cases -- merge into fol/tab/sou proof
  - Formal items to drop: none
  - Prose: replace with cross-ref
  - Examples: cut all
  - Proofs: merge into fol/tab/sou

---

### fol/tab/pro — Examples of Tableaux
- **Action**: CUT
- **Lean Chapter**: CH-DED
- **Lean Section**: N/A
- **Rationale**: Signal is PEDAGOGICAL. Worked examples of propositional tableaux. No taxonomy items.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: all examples and exercises -- pedagogical
  - Prose: cut all
  - Examples: cut all
  - Proofs: cut all

---

### fol/tab/prq — Tableaux with Quantifiers (examples)
- **Action**: CUT
- **Lean Chapter**: CH-DED
- **Lean Section**: N/A
- **Rationale**: Signal is PEDAGOGICAL. Worked examples of quantifier tableaux. FOL-only. No taxonomy items.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: all examples and exercises -- pedagogical
  - Prose: cut all
  - Examples: cut all
  - Proofs: cut all

---

## Summary

### Action Counts

| Action | Count | Sections |
|--------|-------|----------|
| **KEEP** | 19 | fol/axd/rul, fol/axd/prp, fol/axd/qua, fol/axd/ded, fol/axd/prv, fol/axd/sou, fol/ntd/rul, fol/ntd/prl, fol/ntd/qrl, fol/ntd/sou, fol/seq/rul, fol/seq/prl, fol/seq/srl, fol/seq/qrl, fol/seq/sou, fol/tab/rul, fol/tab/prl, fol/tab/qrl, fol/tab/sou |
| **ABSORB** | 1 | fol/axd/ptn (absorbs fol/ntd/ptn, fol/seq/ptn, fol/tab/ptn) |
| **CONDENSE** | 9 | fol/prf/axd, fol/prf/ntd, fol/axd/ppr, fol/axd/qpr, fol/ntd/der, fol/seq/der, fol/seq/ide, fol/tab/der, fol/tab/ide |
| **MERGE-INTO** | 16 | fol/axd/ddq->ded, fol/ntd/ptn->axd/ptn, fol/ntd/prv->axd/prv, fol/ntd/ppr->axd/ppr, fol/ntd/qpr->axd/qpr, fol/ntd/sid->ntd/sou, fol/seq/ptn->axd/ptn, fol/seq/prv->axd/prv, fol/seq/ppr->axd/ppr, fol/seq/qpr->axd/qpr, fol/seq/sid->seq/sou, fol/tab/ptn->axd/ptn, fol/tab/prv->axd/prv, fol/tab/ppr->axd/ppr, fol/tab/qpr->axd/qpr, fol/tab/sid->tab/sou |
| **CUT** | 13 | fol/prf/int, fol/prf/seq, fol/prf/tab, fol/axd/ide, fol/axd/pro, fol/axd/prq, fol/ntd/ide, fol/ntd/pro, fol/ntd/prq, fol/seq/pro, fol/seq/prq, fol/tab/pro, fol/tab/prq |
| **Total** | **58** | (19 KEEP + 1 ABSORB + 9 CONDENSE + 16 MERGE-INTO + 13 CUT) |

Note: The ABSORB action (fol/axd/ptn) is functionally a KEEP that also absorbs 3 MERGE-INTO sources. The 16 MERGE-INTO entries are the sections being merged. The total 19 + 1 + 9 + 16 + 13 = 58 sections.

### Lean Section Distribution

| Lean Section | Sections Feeding In | Key Content |
|-------------|-------------------|-------------|
| **DED.1** Generic | fol/axd/rul (generic defs), fol/axd/ptn (ABSORB:3 ptn), fol/axd/prv (ABSORB:3 prv), fol/axd/ppr (ABSORB:3 ppr), fol/axd/qpr (ABSORB:3 qpr), fol/ntd/rul (PRIM-DED009), fol/seq/rul (PRIM-DED008), fol/seq/srl (PRIM-DED007) | Rule of inference, derivation, provability, theorem, consistency, structural properties, sequent, structural rules, assumption discharge |
| **DED.2** Axiomatic | fol/prf/axd, fol/axd/prp, fol/axd/qua, fol/axd/ded (+ddq), fol/axd/ppr, fol/axd/qpr, fol/axd/sou | Hilbert axiom schemas, MP, QR, Deduction Theorem, connective/quantifier facts, soundness |
| **DED.3** Natural Deduction | fol/prf/ntd, fol/ntd/rul, fol/ntd/prl, fol/ntd/qrl, fol/ntd/der, fol/ntd/sou (+sid) | ND rules (intro/elim), derivation definition, soundness |
| **DED.4** Sequent Calculus | fol/seq/rul, fol/seq/prl, fol/seq/srl, fol/seq/qrl, fol/seq/der, fol/seq/sou (+sid), fol/seq/ide | LK rules (left/right), structural rules, sequent derivation, soundness, identity rules |
| **DED.5** Tableaux | fol/tab/rul, fol/tab/prl, fol/tab/qrl, fol/tab/der, fol/tab/sou (+sid), fol/tab/ide | Signed formulas, tableau rules, tableau derivation, soundness, identity rules |

### Taxonomy Coverage

**Primitives covered** (10 of 10):
- PRIM-DED001 (Axiom Schema): fol/axd/prp (DED.2)
- PRIM-DED002 (Non-Logical Axiom): not in this batch (theories chapter)
- PRIM-DED003 (Rule of Inference): fol/axd/rul (DED.1)
- PRIM-DED004 (Proof System): implicit across DED.2-5
- PRIM-DED005 (Derivation): fol/axd/rul (DED.1 generic), instantiated in DED.2-5
- PRIM-DED006 (Provability): fol/axd/ptn (DED.1)
- PRIM-DED007 (Structural Rules): fol/seq/srl (DED.1/4)
- PRIM-DED008 (Sequent): fol/seq/rul (DED.1/4)
- PRIM-DED009 (Assumption Discharge): fol/ntd/rul (DED.1/3)
- PRIM-DED010 (Theorem): fol/axd/ptn (DED.1)

**Definitions covered** (8 of 10 in-scope):
- DEF-DED001 (Syntactic Consistency): fol/axd/ptn (DED.1)
- DEF-DED003 (Deductive Closure): fol/axd/ptn (DED.1, absorbed from fol/seq/ptn)
- DEF-DED005 (Hilbert-Style System): fol/axd/prp (DED.2)
- DEF-DED006 (ND System): fol/ntd/prl (DED.3)
- DEF-DED007 (SC System): fol/seq/rul (DED.4)
- DEF-DED008 (Tableau System): fol/tab/rul (DED.5)
- DEF-DED002 (Maximal Consistent Set): not in this batch (completeness chapter)
- DEF-DED004 (Conservative Extension): NEW-CONTENT

**Axioms covered** (3 of 3):
- AX-DED001 (MP): fol/axd/prp (DED.2)
- AX-DED002 (Gen): fol/axd/qua (DED.2)
- AX-DED003 (Axiom Schemas): fol/axd/prp + fol/axd/qua (DED.2)

**Theorems covered** (1 in-scope):
- THM-DED001 (Deduction Theorem): fol/axd/ded (DED.2)
- CP-001 (Soundness): fol/axd/sou (DED.2), fol/ntd/sou (DED.3), fol/seq/sou (DED.4), fol/tab/sou (DED.5)

**Composition patterns**:
- CP-009 (Deduction Theorem): fol/axd/ded (DED.2)
- CP-010 (Cut Elimination): fol/seq/srl (DED.4, informal statement only)

### Expected Redundancy Resolutions (19 of 19)

All 19 expected cross-system redundancies are resolved by the A1 architecture:

| Redundant Concept | Authoritative Home | Systems Merged |
|-------------------|-------------------|----------------|
| Provability (PRIM-DED006) | fol/axd/ptn | NTD, SC, Tab ptn |
| Theorem (PRIM-DED010) | fol/axd/ptn | NTD, SC, Tab ptn |
| Consistency (DEF-DED001) | fol/axd/ptn | NTD, SC, Tab ptn |
| Reflexivity | fol/axd/ptn | NTD, SC, Tab ptn |
| Monotonicity | fol/axd/ptn | NTD, SC, Tab ptn |
| Transitivity | fol/axd/ptn | NTD, SC, Tab ptn |
| Inconsistency characterization | fol/axd/ptn | NTD, SC, Tab ptn |
| Compactness | fol/axd/ptn | NTD, SC, Tab ptn |
| provability-contr | fol/axd/prv | NTD, SC, Tab prv |
| prov-incons | fol/axd/prv | NTD, SC, Tab prv |
| explicit-inc | fol/axd/prv | NTD, SC, Tab prv |
| provability-exhaustive | fol/axd/prv | NTD, SC, Tab prv |
| provability-land | fol/axd/ppr | NTD, SC, Tab ppr |
| provability-lor | fol/axd/ppr | NTD, SC, Tab ppr |
| provability-lif | fol/axd/ppr | NTD, SC, Tab ppr |
| strong-generalization | fol/axd/qpr | NTD, SC, Tab qpr |
| provability-quantifiers | fol/axd/qpr | NTD, SC, Tab qpr |
| Soundness identity ext (sid) | per-system sou | NTD, SC, Tab sid |
| Deductive Closure (DEF-DED003) | fol/axd/ptn | SC ptn |

### Generic Concept Assignments (DED.1)

See DED-GENERIC-ASSIGNMENTS.md for the full table. In summary:

- **fol/axd/rul** is authoritative for: PRIM-DED001 (Rule of Inference), PRIM-DED005 (Derivation)
- **fol/axd/ptn** is authoritative for: PRIM-DED006 (Provability), PRIM-DED010 (Theorem), DEF-DED001 (Consistency), DEF-DED003 (Deductive Closure), plus 5 structural properties
- **fol/axd/prv** is authoritative for: 4 consistency/derivability propositions
- **fol/ntd/rul** is authoritative for: PRIM-DED009 (Assumption Discharge)
- **fol/seq/rul** is authoritative for: PRIM-DED008 (Sequent)
- **fol/seq/srl** is authoritative for: PRIM-DED007 (Structural Rules)

---

## CH-META: Metatheory (Composition Patterns) — Completeness, Models, Beyond

---

### Chapter: completeness (fol/com)

### fol/com/int — Introduction
- **Action**: CUT
- **Lean Chapter**: CH-META
- **Lean Section**: N/A
- **Rationale**: Signal is PEDAGOGICAL only. Purely motivational overview previewing completeness, compactness, and Lowenheim-Skolem with no formal items. Hilbert-to-Frege historical anecdote is interesting but provides no taxonomy content. The lean text's META.2 statement will subsume this introduction.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: N/A (no formal items)
  - Prose: cut all
  - Examples: cut all
  - Proofs: N/A

---

### fol/com/out — Outline of the Proof
- **Action**: CUT
- **Lean Chapter**: CH-META
- **Lean Section**: N/A
- **Rationale**: Signal is PEDAGOGICAL only. Prose road map of the Henkin construction proof strategy. References nearly every subsequent section but introduces no definitions, theorems, or lemmas. The lean text's proof chain in META.2 (fol/com/ccs through fol/com/cth) is self-documenting and renders this overview redundant.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: N/A (no formal items)
  - Prose: cut all
  - Examples: cut all
  - Proofs: N/A

---

### fol/com/ccs — Complete Consistent Sets of Sentences
- **Action**: KEEP
- **Lean Chapter**: CH-META
- **Lean Section**: META.2: Completeness (CP-002)
- **Rationale**: Signal is CORE-DEF (for DEF-SEM005) + STEPPING-STONE (for prop:ccs). Sole defining occurrence of DEF-SEM005 (Complete Set / Complete Theory). The proposition prop:ccs (closure under provability, connective conditions for complete consistent sets) is an essential stepping stone used directly by the Truth Lemma in fol/com/mod. This is the first node in the Henkin proof chain and must be preserved intact.
- **Content Directives**:
  - Formal items to preserve: `\begin{defn}[Complete set]` (DEF-SEM005); `\begin{prop}` prop:ccs with all sub-items (prop:ccs-prov-in, prop:ccs-and, prop:ccs-or, prop:ccs-if) -- required by Truth Lemma
  - Formal items to drop: none
  - Prose: compress to intro + definition only; cut the two `\begin{explain}` blocks (pedagogical motivation for why complete consistent sets matter); retain one sentence linking completeness to the construction
  - Examples: cut all (none present)
  - Proofs: preserve full -- prop:ccs proof is the structural backbone used by the Truth Lemma; it establishes the connective-by-connective correspondence

---

### fol/com/mcs — Maximally Consistent Sets of Sentences
- **Action**: CONDENSE
- **Lean Chapter**: CH-META
- **Lean Section**: META.2: Completeness (CP-002)
- **Rationale**: Signal is CORE-DEF (for DEF-DED002) + STEPPING-STONE (for prop:mcs). Introduces DEF-DED002 (Maximally Consistent Set). The prop:mcs results mirror prop:ccs exactly (the OL uses both as tagged alternatives for the completeness proof). In the lean text, we use the "complete consistent set" approach (via fol/com/ccs), so the MCS properties are a redundant parallel. However, the MCS definition itself (DEF-DED002) is an independent taxonomy item used elsewhere (e.g., Lindenbaum's Lemma extends to MCS).
- **Content Directives**:
  - Formal items to preserve: `\begin{defn}[Maximally consistent set]` (DEF-DED002); one-line remark that every MCS is complete and consistent (linking DEF-DED002 to DEF-SEM005)
  - Formal items to drop: `\begin{prop}` prop:mcs and all sub-items (prop:mcs-prov-in, prop:mcs-either-or, prop:mcs-and, prop:mcs-or, prop:mcs-if) -- these duplicate prop:ccs for the tagged-alternative approach; the lean text uses the CCS approach
  - Prose: compress to definition + one sentence stating the equivalence with complete consistent sets
  - Examples: cut all (none present)
  - Proofs: cut all -- the prop:mcs proofs are redundant once we retain prop:ccs

---

### fol/com/hen — Henkin Expansion
- **Action**: KEEP
- **Lean Chapter**: CH-META
- **Lean Section**: META.2: Completeness (CP-002)
- **Rationale**: Signal is STEPPING-STONE (all items serve CP-002). This is the core of the Henkin trick and an essential node in the completeness proof chain. Contains: (1) language expansion preserves consistency (prop:lang-exp), (2) saturated set definition, (3) Henkin expansion construction (defn:henkin-exp), (4) extension to saturated consistent set (lem:henkin), (5) quantifier instances in saturated complete consistent sets (prop:saturated-instances). All five items are required by the completeness theorem proof.
- **Content Directives**:
  - Formal items to preserve: `\begin{prop}` prop:lang-exp (language expansion preserves consistency); `\begin{defn}[Saturated set]` (saturated set definition); `\begin{defn}` defn:henkin-exp (Henkin witness sentences $D_n$); `\begin{lem}` lem:henkin (every consistent set extends to saturated consistent set); `\begin{prop}` prop:saturated-instances (quantifier instances in saturated CCS)
  - Formal items to drop: none
  - Prose: compress to intro + definitions only; cut the opening `\begin{explain}` block (motivation for the Henkin trick); cut the explain block before prop:saturated-instances; retain one sentence stating the key idea (adding witness constants)
  - Examples: cut all (none present)
  - Proofs: preserve full -- lem:henkin proof is essential (inductive consistency argument); prop:saturated-instances proof is essential (used directly by the Truth Lemma's quantifier cases)

---

### fol/com/lin — Lindenbaum's Lemma
- **Action**: KEEP
- **Lean Chapter**: CH-META
- **Lean Section**: META.2: Completeness (CP-002)
- **Rationale**: Signal is CORE-THM. Sole defining occurrence of THM-DED005 (Lindenbaum's Lemma: every consistent set extends to a complete consistent set). This is a core DED result with independent reuse beyond the completeness theorem (e.g., in compactness, in model theory). Essential node in the Henkin proof chain.
- **Content Directives**:
  - Formal items to preserve: `\begin{lem}[Lindenbaum's Lemma]` lem:lindenbaum (THM-DED005)
  - Formal items to drop: none
  - Prose: compress to intro + statement only; cut the `\begin{explain}` block (pedagogical description of the enumeration-and-extension strategy)
  - Examples: cut all (none present)
  - Proofs: preserve full -- the proof is concise and essential (enumeration construction, inductive consistency, compactness of $\Proves$ for the union step)

---

### fol/com/mod — Construction of a Model
- **Action**: KEEP
- **Lean Chapter**: CH-META
- **Lean Section**: META.2: Completeness (CP-002)
- **Rationale**: Signal is STEPPING-STONE (critical -- the heart of the Henkin construction). Contains the term model definition (defn:termmodel), the value lemma (lem:val-in-termmodel), the quantifier reduction for covered models (prop:quant-termmodel), and the Truth Lemma (lem:truth). The Truth Lemma is the central technical result that bridges the syntactic (complete consistent set) and semantic (satisfaction) worlds. All items are essential for CP-002.
- **Content Directives**:
  - Formal items to preserve: `\begin{defn}[Term model]` defn:termmodel (term model $\mathfrak{M}(\Gamma^*)$ / valuation $v(\Gamma^*)$); `\begin{lem}` lem:val-in-termmodel (value of term in term model); `\begin{prop}` prop:quant-termmodel (quantifiers in term model reduce to instances); `\begin{lem}[Truth Lemma]` lem:truth ($\mathfrak{M}(\Gamma^*) \models A$ iff $A \in \Gamma^*$)
  - Formal items to drop: none
  - Prose: compress to intro + definitions only; cut the opening `\begin{explain}` block (pedagogical description of the construction strategy); cut the explain block before prop:quant-termmodel; retain one sentence stating that the term model domain is the set of closed terms
  - Examples: cut all (none present)
  - Proofs: preserve full -- lem:truth proof by induction on formula complexity is the technical core; lem:val-in-termmodel and prop:quant-termmodel proofs are concise and necessary

---

### fol/com/ide — Identity
- **Action**: KEEP
- **Lean Chapter**: CH-META
- **Lean Section**: META.2: Completeness (CP-002)
- **Rationale**: Signal is STEPPING-STONE. Extends the term model construction to handle identity via the factoring construction (quotienting by $\approx$). Contains: $\approx$ relation definition, congruence proof (prop:approx-equiv), equivalence class definition, factored term model (defn:term-model-factor), factored value lemma (lem:val-in-termmodel-factored), and factored Truth Lemma (lem:truth). All items are required for the completeness theorem to handle languages with identity. FOL-only section.
- **Content Directives**:
  - Formal items to preserve: `\begin{defn}` ($\approx$ relation on closed terms); `\begin{prop}` prop:approx-equiv ($\approx$ is a congruence -- reflexive, symmetric, transitive, respects functions and predicates); `\begin{defn}` (equivalence class $[t]_\approx$); `\begin{defn}` defn:term-model-factor (factored term model $\mathfrak{M}/{\approx}$); `\begin{lem}` lem:val-in-termmodel-factored; `\begin{lem}` lem:truth (Truth Lemma for factored model)
  - Formal items to drop: `\begin{digress}` block (observation that $\mathfrak{M}/{\approx}$ may be finite) -- interesting but tangential to the proof
  - Prose: compress to intro + definitions only; cut the opening `\begin{explain}` block (pedagogical motivation for factoring); cut the explain block about well-definedness; retain one sentence stating the key idea (quotient by provable equality)
  - Examples: cut all (none present)
  - Proofs: preserve full -- prop:approx-equiv proof and lem:truth proof are essential for correctness of the identity case

---

### fol/com/cth — The Completeness Theorem
- **Action**: KEEP
- **Lean Chapter**: CH-META
- **Lean Section**: META.2: Completeness (CP-002)
- **Rationale**: Signal is CORE-THM. Sole defining occurrence of CP-002 (Completeness Theorem) in both formulations: (1) consistent implies satisfiable (thm:completeness), and (2) $\Gamma \models A \Rightarrow \Gamma \vdash A$ (cor:completeness). This is the culminating result of the completeness chapter, assembling all stepping stones: Henkin expansion, Lindenbaum's Lemma, and the Truth Lemma.
- **Content Directives**:
  - Formal items to preserve: `\begin{thm}[Completeness Theorem]` thm:completeness (CP-002, first formulation); `\begin{cor}[Completeness Theorem, Second Version]` cor:completeness (CP-002, second formulation)
  - Formal items to drop: `\begin{prob}` items (exercises asking students to show equivalence of formulations and trace rule usage) -- pedagogical
  - Prose: preserve the one-line explain block ("Let's combine our results"); it serves as a useful structural marker
  - Examples: cut all (none present)
  - Proofs: preserve full -- the proof is concise and essential (assembles Henkin + Lindenbaum + Truth Lemma for (1); derives (2) from (1) via contraposition and entails-unsat)

---

### fol/com/com — The Compactness Theorem
- **Action**: KEEP
- **Lean Chapter**: CH-META
- **Lean Section**: META.3: Compactness (CP-003)
- **Rationale**: Signal is CORE-THM (for CP-003 and DEF-SEM003). Sole defining occurrence of CP-003 (Compactness Theorem) in both formulations, and of DEF-SEM003 (Finitely Satisfiable). The proof route (finitely satisfiable -> finitely consistent via soundness -> consistent via compactness of $\Proves$ -> satisfiable via completeness) is elegant and concise. The three examples are pedagogically valuable but not required for the lean text.
- **Content Directives**:
  - Formal items to preserve: `\begin{defn}` (finitely satisfiable -- DEF-SEM003); `\begin{thm}[Compactness Theorem]` thm:compactness (CP-003, both formulations)
  - Formal items to drop: `\begin{ex}` (covered model) -- pedagogical application; `\begin{ex}` (infinitesimals via compactness) -- pedagogical application; `\begin{ex}` (finitude not expressible) -- pedagogical application (this result is stated without proof in fol/mat/siz, and follows from CP-003 + CP-004, but the example itself is pedagogical)
  - Prose: compress to intro + definition + statement; cut the opening paragraph motivating compactness (the lean text's META.3 heading suffices)
  - Examples: cut all 3 -- pedagogical applications
  - Proofs: preserve full -- the proof is concise (4 steps) and essential; it demonstrates the soundness-completeness bridge

---

### fol/com/cpd — A Direct Proof of the Compactness Theorem
- **Action**: CUT
- **Lean Chapter**: CH-META
- **Lean Section**: N/A
- **Rationale**: Signal is STEPPING-STONE (alternative proof). All items are OL-ONLY alternative-proof stepping stones for CP-003. The lean text already establishes CP-003 via the completeness + soundness route in fol/com/com, which is more concise and demonstrates the composition pattern (CP-003 as corollary of CP-001 + CP-002). The direct proof, while pedagogically interesting (shows the construction's flexibility), is redundant in the lean text.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: prop:fsat-ccs (properties of complete finitely satisfiable sets) -- redundant parallel of prop:ccs; lem:fsat-henkin (Henkin for finitely satisfiable) -- redundant parallel of lem:henkin; prop:fsat-instances -- redundant parallel of prop:saturated-instances; lem:fsat-lindenbaum -- redundant parallel of lem:lindenbaum; thm:compactness-direct -- alternative proof of already-established CP-003
  - Prose: cut all
  - Examples: cut all
  - Proofs: cut all

---

### fol/com/dls — The Lowenheim-Skolem Theorem
- **Action**: KEEP
- **Lean Chapter**: CH-META
- **Lean Section**: META.4: Lowenheim-Skolem (CP-004)
- **Rationale**: Signal is CORE-THM. Sole defining occurrence of CP-004 (Downward Lowenheim-Skolem Theorem). The proof is remarkably short (follows directly from the term model having a domain no larger than the set of terms). The variant without identity (noidentity-ls) gives a stronger result (denumerable, not just countable) and is worth preserving. Skolem's Paradox is pedagogical.
- **Content Directives**:
  - Formal items to preserve: `\begin{thm}` thm:downward-ls (CP-004: consistent set has enumerable model); `\begin{thm}` noidentity-ls (variant: without identity, consistent set has denumerable model)
  - Formal items to drop: `\begin{ex}[Skolem's Paradox]` -- pedagogical (interesting philosophical discussion of ZFC having countable models, but not a taxonomy item)
  - Prose: compress to intro + statements; retain the one-sentence opening paragraph (captures the key consequence: FOL cannot express non-enumerability)
  - Examples: cut Skolem's Paradox -- pedagogical
  - Proofs: preserve full -- both proofs are 2-3 lines each (direct corollaries of the term model construction); they demonstrate the compositional power of the completeness proof

---

### Chapter: models-theories (fol/mat)

### fol/mat/int — Introduction
- **Action**: DISTRIBUTE
- **Lean Chapter**: CH-META (for DEF-DED003 definition); CH-SEM (for DEF-SEM007 definition)
- **Lean Section**: META.2 preamble (for DEF-DED003: Deductive Closure / Closed Set); SEM.5 or equivalent (for DEF-SEM007: Axiomatizable Theory)
- **Rationale**: Signal is CORE-DEF (for DEF-DED003 and DEF-SEM007) + PEDAGOGICAL (for the expository list). Contains the sole formal definitions of DEF-DED003 (Deductive Closure: $\{A : \Gamma \models A\}$, and "closed" set) and DEF-SEM007 (Axiomatizable Theory: $\Gamma$ is axiomatized by $\Delta$ if $\Gamma$ is the closure of $\Delta$). These two definitions belong in different lean chapters. The 6-item expository list is pedagogical.
- **Content Directives**:
  - Formal items to preserve: `\begin{defn}` containing "closed," "closure," and "axiomatized by" -- distribute "closed" and "closure" as DEF-DED003 to CH-META (or CH-DED if deductive closure is placed there); distribute "axiomatized by" as DEF-SEM007 to CH-SEM
  - Formal items to drop: `\begin{explain}` 6-item list (importance of axiom systems, capturing structures, consistency, independence, definability) -- pedagogical
  - Prose: cut all expository prose; the definitions carry themselves
  - Examples: cut all (none present as formal examples)
  - Proofs: N/A

---

### fol/mat/exs — Expressing Properties of Structures
- **Action**: CONDENSE
- **Lean Chapter**: CH-SEM
- **Lean Section**: SEM.3 or equivalent (Satisfaction and Models)
- **Rationale**: Signal is CORE-DEF (for PRIM-SEM011). Contains the sole formal defining occurrence of PRIM-SEM011 (Model of a set of sentences: $\mathfrak{M}$ is a model of $\Gamma$ iff $\mathfrak{M} \models A$ for all $A \in \Gamma$). The partial order example is pedagogical. Note: this definition logically belongs in CH-SEM (it extends the satisfaction relation to sets), not CH-META, even though it appears in the OL's models-theories chapter.
- **Content Directives**:
  - Formal items to preserve: `\begin{defn}[Model of a set]` (PRIM-SEM011)
  - Formal items to drop: none (only one formal item)
  - Prose: compress to definition only; cut the `\begin{explain}` block (motivational discussion of which structural properties can be expressed by sentences)
  - Examples: cut `\begin{ex}` (partial order axioms) -- pedagogical illustration
  - Proofs: N/A

---

### fol/mat/the — Examples of First-Order Theories
- **Action**: CUT
- **Lean Chapter**: CH-META
- **Lean Section**: N/A
- **Rationale**: Signal is PEDAGOGICAL only. Consists entirely of examples (strict linear orders, groups, Peano arithmetic, naive comprehension / Russell's Paradox, mereology). No formal theorem/definition environments -- all items are `\begin{ex}`. While the examples implicitly demonstrate PRIM-DED002 (non-logical axioms), the lean text introduces PRIM-DED002 formally in CH-DED. The induction schema for PA is introduced here but will be treated in CH-INC (incompleteness).
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: all 5 `\begin{ex}` items -- pedagogical
  - Prose: cut all
  - Examples: cut all
  - Proofs: N/A

---

### fol/mat/exr — Expressing Relations in a Structure
- **Action**: CUT
- **Lean Chapter**: CH-META
- **Lean Section**: N/A
- **Rationale**: Signal is PEDAGOGICAL. The "expresses the relation" definition is not a core taxonomy item (the SECTION-MAP notes it is OL-ONLY and "not in taxonomy as a separate item, though it relates to DEF-SEM008 indirectly"). The definition of definability-in-a-structure is a standard concept but serves here only to set up examples in arithmetic. The examples are pedagogical.
- **Content Directives**:
  - Formal items to preserve: none -- the definability concept will be noted inline if needed when DEF-SEM008 is introduced
  - Formal items to drop: `\begin{defn}` ("expresses the relation") -- OL-ONLY, not in taxonomy; `\begin{ex}` (arithmetic relations) -- pedagogical
  - Prose: cut all
  - Examples: cut all
  - Proofs: N/A

---

### fol/mat/set — The Theory of Sets
- **Action**: CUT
- **Lean Chapter**: CH-META
- **Lean Section**: N/A
- **Rationale**: Signal is PEDAGOGICAL only. Extended exposition of how ZFC can be formulated in FOL. No formal theorem/definition environments. Demonstrates how to define $\subseteq$, $\emptyset$, $\cup$, $\mathcal{P}(X)$, ordered pairs, Cartesian products, functions, injectivity, and Cantor's theorem within the language of set theory. Entirely pedagogical from the taxonomy perspective -- all of these set-theoretic concepts are already defined as primitives in CH-BST.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: N/A (no formal environments)
  - Prose: cut all
  - Examples: cut all
  - Proofs: N/A

---

### fol/mat/siz — Expressing the Size of Structures
- **Action**: CUT
- **Lean Chapter**: CH-META
- **Lean Section**: N/A
- **Rationale**: Signal is PEDAGOGICAL only. The $A_{\ge n}$ and $A_{= n}$ sentences are OL-ONLY pedagogical constructions (not taxonomy items). The key results (finitude and non-enumerability cannot be expressed in FOL) are stated without proof and follow from CP-003 and CP-004, which are established in fol/com/com and fol/com/dls respectively. The $A_{\ge n}$ sentences also appear in the compactness examples in fol/com/com (which we already cut as examples). The propositions are unlabeled and pedagogical.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: 3 unlabeled propositions ($A_{\ge n}$, $A_{= n}$, infinitude via set of sentences) -- pedagogical
  - Prose: cut all
  - Examples: cut all
  - Proofs: N/A

---

### Chapter: beyond (fol/byd)

### fol/byd/int — Overview
- **Action**: CUT
- **Lean Chapter**: CH-META
- **Lean Section**: N/A
- **Rationale**: Signal is TANGENTIAL. Philosophical introduction discussing what makes a system "logical." Mentions Russell-Whitehead Principia, Quine's objections to higher-order logic, Frege's logicist tradition. No formal content whatsoever. The lean text's CH-EXT stubs (extension logic pointers) serve this purpose without the philosophical discussion.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: N/A (no formal items)
  - Prose: cut all
  - Examples: cut all
  - Proofs: N/A

---

### fol/byd/msl — Many-Sorted Logic
- **Action**: CUT
- **Lean Chapter**: CH-META
- **Lean Section**: N/A
- **Rationale**: Signal is TANGENTIAL. Survey of many-sorted logic: multiple disjoint domains, typed variables/quantifiers/predicates/functions, embedding into FOL via sort predicates. Notes completeness carries over. No formal items from the taxonomy. The lean text's CH-EXT stubs cover extension logics at the pointer level.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: N/A (no formal items)
  - Prose: cut all
  - Examples: cut all
  - Proofs: N/A

---

### fol/byd/sol — Second-Order Logic
- **Action**: CUT
- **Lean Chapter**: CH-META
- **Lean Section**: N/A
- **Rationale**: Signal is TANGENTIAL. Most technically dense section in the beyond chapter but still survey-level with no formal environments. Covers: SOL syntax, comprehension schema, full vs. weak semantics, categoricity of second-order PA, expressiveness, incompleteness of full SOL, completeness for weak semantics. No taxonomy items introduced. The lean text's CH-EXT stubs serve this purpose.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: N/A (no formal environments)
  - Prose: cut all
  - Examples: cut all
  - Proofs: cut all (inline proof sketches only)

---

### fol/byd/hol — Higher-Order Logic
- **Action**: CUT
- **Lean Chapter**: CH-META
- **Lean Section**: N/A
- **Rationale**: Signal is TANGENTIAL. Describes finite type theory: types, terms, formulas, full vs. weak semantics. Mentions Church's simple theory of types. No taxonomy items. The lean text's CH-EXT stubs cover this.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: N/A (no formal items)
  - Prose: cut all
  - Examples: cut all
  - Proofs: N/A

---

### fol/byd/il — Intuitionistic Logic
- **Action**: CUT
- **Lean Chapter**: CH-META
- **Lean Section**: N/A
- **Rationale**: Signal is TANGENTIAL. Covers BHK interpretation, Curry-Howard, double-negation translation (Godel-Gentzen), Kripke semantics. Contains three unlabeled theorems (equivalence of excluded middle schemata, double-negation translation, relativization to hypotheses), but all are OL-ONLY and TANGENTIAL. No core taxonomy items. The lean text's CH-EXT stubs cover intuitionistic logic at the pointer level.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: 3 unlabeled theorems -- tangential to FOL taxonomy
  - Prose: cut all
  - Examples: cut all
  - Proofs: N/A

---

### fol/byd/mod — Modal Logics
- **Action**: CUT
- **Lean Chapter**: CH-META
- **Lean Section**: N/A
- **Rationale**: Signal is TANGENTIAL. Survey of modal logic: $\Box$ and $\Diamond$ operators, Kripke semantics, applications (provability logic, epistemic logic, temporal logic), axiom systems S4 and S5. No formal environments. No taxonomy items. The lean text's CH-EXT stubs cover this.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: N/A (no formal items)
  - Prose: cut all
  - Examples: cut all
  - Proofs: N/A

---

### fol/byd/oth — Other Logics
- **Action**: CUT
- **Lean Chapter**: CH-META
- **Lean Section**: N/A
- **Rationale**: Signal is TANGENTIAL. One-page survey mentioning fuzzy logic, probabilistic logic, default/nonmonotonic logics, epistemic logics, causal logics, deontic logics. No formal content. Closes with a Leibniz reference. The lean text's CH-EXT stubs cover this.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: N/A (no formal items)
  - Prose: cut all
  - Examples: cut all
  - Proofs: N/A

---

## Summary

### Action Counts (25 sections total)

| Action | Count | Sections |
|--------|-------|----------|
| KEEP | 8 | fol/com/ccs, fol/com/hen, fol/com/lin, fol/com/mod, fol/com/ide, fol/com/cth, fol/com/com, fol/com/dls |
| CONDENSE | 2 | fol/com/mcs, fol/mat/exs |
| DISTRIBUTE | 1 | fol/mat/int (DEF-DED003 -> CH-META/CH-DED; DEF-SEM007 -> CH-SEM) |
| CUT | 14 | fol/com/int, fol/com/out, fol/com/cpd, fol/mat/the, fol/mat/exr, fol/mat/set, fol/mat/siz, fol/byd/int, fol/byd/msl, fol/byd/sol, fol/byd/hol, fol/byd/il, fol/byd/mod, fol/byd/oth |

*Totals: 8+2+1+14 = 25 sections.*

### Composition Pattern (CP) Placement

| CP | Lean Section | Key Sections |
|----|-------------|--------------|
| CP-002 (Completeness) | META.2 | fol/com/ccs -> fol/com/mcs -> fol/com/hen -> fol/com/lin -> fol/com/mod -> fol/com/ide -> fol/com/cth |
| CP-003 (Compactness) | META.3 | fol/com/com |
| CP-004 (Lowenheim-Skolem) | META.4 | fol/com/dls |

*Note: CP-001 (Soundness) is already covered in CH-DED (DED.2-5). META.1 would just state the unified theorem.*

### Henkin Proof Chain (CP-002): Preserved Intact

```
fol/com/ccs (DEF-SEM005 + prop:ccs) [KEEP]
  -> fol/com/mcs (DEF-DED002) [CONDENSE -- definition only]
  -> fol/com/hen (saturated set + Henkin expansion + lem:henkin + prop:saturated-instances) [KEEP]
  -> fol/com/lin (THM-DED005: Lindenbaum's Lemma) [KEEP]
  -> fol/com/mod (term model + Truth Lemma) [KEEP]
  -> fol/com/ide (factored term model + factored Truth Lemma) [KEEP]
  -> fol/com/cth (CP-002: thm:completeness + cor:completeness) [KEEP]
```

### Taxonomy Items Covered

| Item | Source Section | Action |
|------|--------------|--------|
| DEF-SEM005 (Complete Set) | fol/com/ccs | KEEP |
| DEF-DED002 (Maximally Consistent Set) | fol/com/mcs | CONDENSE |
| THM-DED005 (Lindenbaum's Lemma) | fol/com/lin | KEEP |
| CP-002 (Completeness Theorem) | fol/com/cth | KEEP |
| CP-003 (Compactness Theorem) | fol/com/com | KEEP |
| DEF-SEM003 (Finitely Satisfiable) | fol/com/com | KEEP |
| CP-004 (Lowenheim-Skolem) | fol/com/dls | KEEP |
| DEF-DED003 (Deductive Closure) | fol/mat/int | DISTRIBUTE to CH-META/CH-DED |
| DEF-SEM007 (Axiomatizable Theory) | fol/mat/int | DISTRIBUTE to CH-SEM |
| PRIM-SEM011 (Model of a set) | fol/mat/exs | CONDENSE to CH-SEM |

### Beyond Chapter (fol/byd): All 7 sections CUT
All fol/byd/* sections (int, msl, sol, hol, il, mod, oth) are survey/pointer sections with no formal taxonomy items. All CUT; the lean text's CH-EXT stubs serve this purpose.

# INC Batch — Compression Plan (Step 6)

## CH-INC (feeds into CH-META, CH-CMP, CH-DED, CH-SEM)

Note: INC sections do not form a standalone lean chapter. Their content distributes across CH-META (incompleteness theorems CP-005 through CP-008), CH-CMP (representability, arithmetization), CH-DED (theory definitions Q, PA, derivability conditions), and CH-SEM (standard model, true arithmetic, undefinability of truth).

---

## Chapter 1: Introduction to Incompleteness (`inc/int/`)

### inc/int/bgr -- Historical Background
- **Action**: CUT
- **Lean Chapter**: (none)
- **Lean Section**: (none)
- **Rationale**: PEDAGOGICAL only. Pure narrative covering Aristotle through Godel. No formal definitions or theorems. No taxonomy items introduced or needed.
- **Content Directives**:
  - Formal items to preserve: (none)
  - Formal items to drop: (none -- no formal items exist)
  - Prose: cut entirely
  - Examples: cut all
  - Proofs: N/A

### inc/int/def -- Definitions
- **Action**: DISTRIBUTE
- **Lean Chapter**: CH-DED, CH-SEM, CH-CMP
- **Lean Section**: DED.6, SEM.5, CMP.5, CMP.6
- **Rationale**: CORE-DEF section introducing items across 4 domains. Each formal item goes to its taxonomy-owner's lean chapter. This is the densest definition section in the INC batch.
- **Content Directives**:
  - defn (theory, as deductively closed set) [DEF-INC001] -> CUT: subsumed by DEF-DED003 (Deductive Closure) already in DED.1
  - defn[def:standard-model] (Standard Model N) [DEF-INC002 -> DEF-SEM017] -> SEM.5: preserve full definition
  - defn (True Arithmetic TA) [DEF-INC003 -> DEF-SEM018] -> SEM.5: preserve full definition
  - defn (axiomatized theory) [DEF-INC004] -> CUT: restates basic concept already covered in DED.1 under PRIM-DED002
  - defn (Q, Robinson's Q with 8 axioms) [DEF-INC005 -> DEF-DED011] -> DED.6: preserve full definition including all 8 axiom schemas
  - defn (PA, Peano Arithmetic with induction schema) [DEF-INC006 -> DEF-DED012] -> DED.6: preserve full definition
  - defn (complete theory) [DEF-INC007] -> CUT: subsumed by DEF-SEM005 (Semantic Completeness of a theory) already in SEM.3
  - defn (decidable set) -> CUT: merely references PRIM-CMP006, already in CMP.3
  - defn (axiomatizable, by decidable axiom set) [DEF-INC008 -> DEF-CMP011] -> CMP.6: preserve full definition
  - defn (c.e.) -> CUT: merely references PRIM-CMP007, already in CMP.3
  - defn (represents function) [DEF-CMP009] -> CMP.5: preserve full definition (both conditions)
  - defn (represents relation) [DEF-INC009] -> CMP.5: preserve full definition (both conditions)
  - Prose: distribute introductory sentences to each target section; cut general motivation
  - Examples: keep the PA axiomatizability example (finite axiom check + induction schema check) in CMP.6
  - Proofs: N/A (definition section)

### inc/int/ovr -- Overview of Incompleteness Results
- **Action**: CUT
- **Lean Chapter**: (none)
- **Lean Section**: (none)
- **Rationale**: PEDAGOGICAL only. Roadmap section that informally previews CP-005 and CP-006 without proving anything. No formal items survive.
- **Content Directives**:
  - Formal items to preserve: (none)
  - Formal items to drop: thm (informal statement of first incompleteness) -- pedagogical preview only
  - Prose: cut entirely
  - Examples: cut all
  - Proofs: N/A

### inc/int/dec -- Undecidability and Incompleteness
- **Action**: CONDENSE
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.7: Theorems (stepping stone for CP-005)
- **Rationale**: STEPPING-STONE. Proves a weak version of first incompleteness via diagonal argument and the key lemma "axiomatizable + complete => decidable." The weak incompleteness result and the axiomatizable+complete=>decidable lemma are useful stepping stones that belong in CMP.7 since they connect computability to incompleteness.
- **Content Directives**:
  - Formal items to preserve: thm (consistent theory representing all decidable relations is not decidable); thm (axiomatizable + complete => decidable); cor[cor:incompleteness] (weak first incompleteness)
  - Formal items to drop: prob (TA not axiomatizable) -- pedagogical exercise
  - Prose: compress to intro + theorem statements only
  - Examples: cut all (Presburger arithmetic mention is tangential)
  - Proofs: preserve sketch only for the two theorems; the corollary follows immediately

---

## Chapter 2: Arithmetization of Syntax (`inc/art/`)

### inc/art/int -- Introduction (Arithmetization)
- **Action**: CUT
- **Lean Chapter**: (none)
- **Lean Section**: (none)
- **Rationale**: PEDAGOGICAL only. Motivational section with no formal items. The arithmetization idea is introduced by the definitions in inc/art/cod.
- **Content Directives**:
  - Formal items to preserve: (none)
  - Formal items to drop: (none -- no formal items)
  - Prose: cut entirely
  - Examples: cut all
  - Proofs: N/A

### inc/art/cod -- Coding Symbols
- **Action**: CONDENSE
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.5: Coding and Universality (instantiates PRIM-CMP011)
- **Rationale**: STEPPING-STONE. Defines symbol codes and Godel numbers (DEF-INC010, DEF-INC011 instantiating PRIM-CMP011). Essential for the arithmetization chain. Preserve definitions, compress verification.
- **Content Directives**:
  - Formal items to preserve: defn (symbol code) [DEF-INC010]; defn (Godel number) [DEF-INC011]
  - Formal items to drop: prop (Fn, Pred primitive recursive) -- stepping stone, state without proof
  - Prose: compress to intro + definitions only
  - Examples: cut all (specific code assignments are implementation details)
  - Proofs: cut (primitive recursiveness of Fn, Pred stated as remark)

### inc/art/trm -- Coding Terms
- **Action**: CONDENSE
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.5: Coding and Universality
- **Rationale**: STEPPING-STONE. Shows Term(x) and ClTerm(x) are primitive recursive. Essential link in arithmetization chain but verification details can be compressed.
- **Content Directives**:
  - Formal items to preserve: prop[prop:term-primrec] (Term(x) primitive recursive); prop[prop:num-primrec] (num(n) primitive recursive) -- state results
  - Formal items to drop: (none)
  - Prose: compress to statement of results + one-sentence inductive argument sketch
  - Examples: cut all
  - Proofs: preserve sketch only (note formation sequences provide inductive structure)

### inc/art/frm -- Coding Formulas
- **Action**: CONDENSE
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.5: Coding and Universality
- **Rationale**: STEPPING-STONE. Extends primitive recursiveness to formulas and sentences. Essential for proof predicate construction.
- **Content Directives**:
  - Formal items to preserve: prop[prop:frm-primrec] (Frm(x) primitive recursive); prop (Sent(x) primitive recursive)
  - Formal items to drop: prop (Atom(x) primitive recursive) -- intermediate step; prop[prop:freeocc-primrec] (FreeOcc primitive recursive) -- intermediate step
  - Prose: compress to statement of results
  - Examples: cut all
  - Proofs: preserve sketch only (parallel structure to term case)

### inc/art/sub -- Substitution
- **Action**: CONDENSE
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.5: Coding and Universality
- **Rationale**: STEPPING-STONE. Shows Subst(x,y,z) is primitive recursive. Needed for fixed-point lemma.
- **Content Directives**:
  - Formal items to preserve: prop[prop:subst-primrec] (Subst(x,y,z) primitive recursive)
  - Formal items to drop: prop[prop:free-for] (FreeFor primitive recursive) -- intermediate step
  - Prose: compress to statement of result
  - Examples: cut all
  - Proofs: preserve sketch only

### inc/art/plk -- Derivations in LK
- **Action**: ABSORB:{inc/art/pnd, inc/art/pax}
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.5: Coding and Universality (DEF-INC012 Proof Predicate)
- **Rationale**: STEPPING-STONE. This is the primary section for DEF-INC012 (Proof Predicate Prf_Gamma(x,y)). Under A1 (generic proof theory), we present the proof predicate once generically, noting that the construction works for any proof system (LK, ND, AX) with appropriate Godel numbering of derivations. LK chosen as primary because it has the most explicit and complete treatment with fully worked FollowsBy definitions. The ND and AX variants merge into this section.
- **Content Directives**:
  - Formal items to preserve: defn (Godel number of derivation -- generalized); prop[prop:followsby] (Correct(p) primitive recursive); prop[prop:deriv] (Deriv(p) primitive recursive); prop (Prf_Gamma(x,y) primitive recursive) [DEF-INC012]
  - Formal items to drop: prob (define FollowsBy for specific rules) -- exercise; ex (specific LK derivation Godel number) -- keep as canonical example
  - From inc/art/pnd: absorb nothing (parallel content, ND-specific encoding details dropped)
  - From inc/art/pax: absorb nothing (parallel content, AX-specific encoding details dropped)
  - Prose: compress to intro + generic proof predicate construction + result statements. Note variant proof systems in a remark.
  - Examples: keep 1 (the LK derivation example showing concrete Godel number computation)
  - Proofs: preserve sketch only for Correct(p); preserve full proof for Prf_Gamma(x,y)

### inc/art/pnd -- Derivations in Natural Deduction
- **Action**: MERGE-INTO:inc/art/plk
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.5: Coding and Universality
- **Rationale**: STEPPING-STONE. ND variant of DEF-INC012 (Proof Predicate). Under A1, the generic proof predicate is defined once in inc/art/plk. The ND-specific encoding details (Assum, Discharge, OpenAssum as primitive recursive) are noted as a remark in the generic treatment.
- **Content Directives**:
  - Formal items to preserve: (none -- all absorbed into inc/art/plk's generic treatment)
  - Formal items to drop: all ND-specific propositions -- subsumed by generic proof predicate
  - Prose: replace with cross-ref to inc/art/plk
  - Examples: cut all
  - Proofs: cut all

### inc/art/pax -- Axiomatic Derivations
- **Action**: MERGE-INTO:inc/art/plk
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.5: Coding and Universality
- **Rationale**: STEPPING-STONE. AX variant of DEF-INC012 (Proof Predicate). Under A1, merges into the generic treatment in inc/art/plk. The AX encoding is simpler (derivations are sequences) but the result is the same.
- **Content Directives**:
  - Formal items to preserve: (none -- all absorbed into inc/art/plk's generic treatment)
  - Formal items to drop: all AX-specific propositions -- subsumed by generic proof predicate
  - Prose: replace with cross-ref to inc/art/plk
  - Examples: cut all
  - Proofs: cut all

---

## Chapter 3: Representability in Q (`inc/req/`)

### inc/req/int -- Introduction (Representability)
- **Action**: CONDENSE
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.5: Coding and Universality (DEF-CMP009 restated)
- **Rationale**: CORE-DEF. Restates Q axioms and representability definition, announces the main representability theorem. Since inc/int/def distributes DEF-CMP009 to CMP.5, this section provides the most complete treatment context for the representability theorem statement. Keep the theorem statement and proof strategy outline; compress the Q restatement.
- **Content Directives**:
  - Formal items to preserve: defn[defn:representable-fn] (representable in Q) -- cross-ref to CMP.5 DEF-CMP009; thm[thm:representable-iff-comp] (representable iff computable) -- core theorem statement
  - Formal items to drop: Q axiom restatement -- already in DED.6
  - Prose: compress to theorem statement + 1 paragraph proof strategy outline
  - Examples: cut all
  - Proofs: cut (proof is assembled across the chapter)

### inc/req/rpc -- Functions Representable in Q are Computable
- **Action**: CONDENSE
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.5: Coding and Universality
- **Rationale**: STEPPING-STONE. One direction of the representability theorem: representable implies computable. Key stepping stone.
- **Content Directives**:
  - Formal items to preserve: lem (every representable function is computable) -- key direction
  - Formal items to drop: lem[lem:rep-q] (Q proves A_f(n,m) iff m=f(n)) -- intermediate step, fold into main lemma proof
  - Prose: compress to statement + proof sketch
  - Examples: cut all
  - Proofs: preserve sketch only (uses proof predicate and Godel numbering to define f by minimization)

### inc/req/bet -- The Beta Function Lemma
- **Action**: CONDENSE
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.5: Coding and Universality
- **Rationale**: STEPPING-STONE. The beta function lemma (DEF-INC013) is a key technical tool for simulating primitive recursion. Needed for the representability theorem.
- **Content Directives**:
  - Formal items to preserve: lem[lem:beta] (beta function lemma) [DEF-INC013]
  - Formal items to drop: thm (Chinese Remainder Theorem) -- standard number theory result, state without proof
  - Prose: compress to definition of beta function + lemma statement
  - Examples: cut all
  - Proofs: preserve sketch only (cite CRT, state key idea)

### inc/req/pri -- Simulating Primitive Recursion
- **Action**: CONDENSE
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.5: Coding and Universality
- **Rationale**: STEPPING-STONE. Shows primitive recursion reducible to composition + regular minimization via beta function. Key link in representability chain.
- **Content Directives**:
  - Formal items to preserve: lem[lem:prim-rec] (primitive recursion reducible to composition + regular minimization)
  - Formal items to drop: (none)
  - Prose: compress to statement + 2-sentence proof idea
  - Examples: cut all
  - Proofs: preserve sketch only

### inc/req/bre -- Basic Functions are Representable in Q
- **Action**: CONDENSE
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.5: Coding and Universality
- **Rationale**: STEPPING-STONE. Base cases for the representability theorem. Many individual propositions, each a small verification. Compress to a summary statement with key proof idea.
- **Content Directives**:
  - Formal items to preserve: prop[prop:rep-zero] (Zero representable); prop[prop:rep-succ] (Succ representable); prop[prop:rep-add] (Add representable); prop[prop:rep-mult] (Mult representable); lem[lem:q-proves-neq] (Q proves numerals distinct) -- needed downstream
  - Formal items to drop: prop[prop:rep-proj] (Projection representable) -- trivial; prop[prop:rep-id] (Char= representable) -- minor; lem[lem:q-proves-add] -- intermediate; lem[lem:q-proves-mult] -- intermediate
  - Prose: compress to summary of which functions are representable + key proof techniques
  - Examples: cut all
  - Proofs: preserve sketch only for Add and Mult (hardest cases); cut proofs for Zero, Succ, Proj (trivial)

### inc/req/cmp -- Composition is Representable in Q
- **Action**: CONDENSE
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.5: Coding and Universality
- **Rationale**: STEPPING-STONE. Closure of representable functions under composition. Essential step.
- **Content Directives**:
  - Formal items to preserve: prop[prop:rep-composition] (representable functions closed under composition)
  - Formal items to drop: (none)
  - Prose: compress to statement
  - Examples: cut all
  - Proofs: preserve sketch only

### inc/req/min -- Regular Minimization is Representable in Q
- **Action**: CONDENSE
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.5: Coding and Universality
- **Rationale**: STEPPING-STONE. Closure under regular minimization. Most technically demanding step of the representability proof.
- **Content Directives**:
  - Formal items to preserve: prop[prop:rep-minimization] (representable functions closed under regular minimization); lem[lem:less-nsucc] (Q proves x < n+1 implies disjunction of equalities) -- needed in Rosser proof; lem[lem:trichotomy] (Q proves trichotomy for numerals) -- needed in Rosser proof
  - Formal items to drop: lem[lem:succ] (Q proves a'+n = (a+n)') -- intermediate; lem[lem:less-zero] (Q proves not x < 0) -- intermediate
  - Prose: compress to statement of closure result + key lemma statements
  - Examples: cut all
  - Proofs: preserve sketch only for prop:rep-minimization; cut proofs of intermediate lemmas (state as used facts)

### inc/req/crq -- Computable Functions are Representable in Q
- **Action**: ABSORB:{inc/req/cee, inc/req/cre}
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.5: Coding and Universality
- **Rationale**: CORE-THM. Assembles all preceding results to complete the "computable implies representable" direction. Together with inc/req/rpc, establishes the full representability theorem. This is a key stepping stone for CP-005. Absorbs inc/req/cee and inc/req/cre (alternative proof path via class C) as a brief remark noting the alternative approach.
- **Content Directives**:
  - Formal items to preserve: thm (every computable function is representable in Q)
  - Formal items to drop: (none)
  - From inc/req/cee: absorb as 1-sentence remark noting alternative approach via class C
  - From inc/req/cre: absorb nothing (duplicate content)
  - Prose: preserve -- short assembly of results + remark on alternative approach
  - Examples: cut all
  - Proofs: preserve full (short: assembles base cases + closure results)

### inc/req/cee -- The Functions C
- **Action**: MERGE-INTO:inc/req/crq
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.5: Coding and Universality
- **Rationale**: STEPPING-STONE. Alternative proof path defining class C. Redundant with the main approach (inc/req/bre through inc/req/crq). The lean text uses one proof path only.
- **Content Directives**:
  - Formal items to preserve: (none -- subsumed by main proof path)
  - Formal items to drop: DEF-INC014 (Class C) -- redundant alternative approach
  - Prose: replace with cross-ref note in inc/req/crq mentioning alternative approach
  - Examples: cut all
  - Proofs: cut all

### inc/req/cre -- Functions in C are Representable in Q
- **Action**: MERGE-INTO:inc/req/crq
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.5: Coding and Universality
- **Rationale**: STEPPING-STONE. Alternative proof presentation that duplicates material from inc/req/bre and others. Redundant with the main proof chain.
- **Content Directives**:
  - Formal items to preserve: (none -- content duplicated in main proof chain)
  - Formal items to drop: all -- duplicate of bre/cmp/min content
  - Prose: cut entirely
  - Examples: cut all
  - Proofs: cut all

### inc/req/rel -- Representing Relations
- **Action**: CONDENSE
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.5: Coding and Universality
- **Rationale**: STEPPING-STONE. Extends representability theorem from functions to relations. Important for downstream use (proof predicate, undecidability).
- **Content Directives**:
  - Formal items to preserve: defn[defn:representing-relations] (representable relation) -- restates DEF-INC009; thm[thm:representing-rels] (relation representable iff computable)
  - Formal items to drop: (none)
  - Prose: compress to definition + theorem statement
  - Examples: cut all
  - Proofs: preserve sketch only

### inc/req/und -- Undecidability
- **Action**: KEEP
- **Lean Chapter**: CH-META
- **Lean Section**: META.8: Undecidability (CP-008)
- **Rationale**: CORE-THM. Proves undecidability of Q by reduction from the halting problem. The corollary that first-order logic is undecidable is CP-008 (Church's Undecidability of Validity). This is the authoritative section for CP-008.
- **Content Directives**:
  - Formal items to preserve: thm (Q is undecidable); cor (first-order logic is undecidable) [CP-008]
  - Formal items to drop: (none)
  - Prose: preserve
  - Examples: N/A
  - Proofs: preserve full (both the main theorem and the corollary)

### inc/inp/s1c -- Sigma-1 Completeness
- **Action**: KEEP
- **Lean Chapter**: CH-META
- **Lean Section**: META.5: First Incompleteness (supports CP-005)
- **Rationale**: CORE-THM. Defines the arithmetic hierarchy (DEF-INC015 Delta_0, DEF-INC016 Sigma_1, DEF-INC017 Pi_1) and proves Sigma_1-completeness of Q. This is a crucial result used in incompleteness proofs.
- **Content Directives**:
  - Formal items to preserve: defn[defn:bd-quant] (bounded quantifiers); defn[defn:delta0-sigma1-pi1-frm] (Delta_0, Sigma_1, Pi_1 formulas) [DEF-INC015, DEF-INC016, DEF-INC017]; thm[thm:sigma1-completeness] (Sigma_1 completeness of Q)
  - Formal items to drop: (none -- all lemmas are essential stepping stones for the main theorem)
  - Prose: preserve (definitions + theorem + lemma chain)
  - Examples: N/A
  - Proofs: preserve full (lem:q-proves-clterm-id, lem:atomic-completeness, lem:bounded-quant-equiv, lem:delta0-completeness all lead to thm:sigma1-completeness)

---

## Chapter 4: Theories and Computability (`inc/tcp/`)

### inc/tcp/int -- Introduction (Theories and Computability)
- **Action**: CUT
- **Lean Chapter**: (none)
- **Lean Section**: (none)
- **Rationale**: PEDAGOGICAL only. Brief intro summarizing previous results. No formal items. Editorially marked as needing rewrite.
- **Content Directives**:
  - Formal items to preserve: (none)
  - Formal items to drop: (none -- no formal items)
  - Prose: cut entirely
  - Examples: cut all
  - Proofs: N/A

### inc/tcp/qce -- Q is c.e.-Complete
- **Action**: CONDENSE
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.7: Theorems
- **Rationale**: STEPPING-STONE. Shows Q is c.e.-complete (K reduces to Q). Important stepping stone for the undecidability chain but the detailed reduction proof can be compressed.
- **Content Directives**:
  - Formal items to preserve: thm (Q is c.e.-complete)
  - Formal items to drop: (none)
  - Prose: compress to statement
  - Examples: cut all
  - Proofs: preserve sketch only (note K reduces to Q via representability of T predicate)

### inc/tcp/oqn -- Omega-Consistent Extensions of Q are Undecidable
- **Action**: CONDENSE
- **Lean Chapter**: CH-DED
- **Lean Section**: DED.6: Theories and Arithmetic (DEF-INC018 omega-consistency)
- **Rationale**: STEPPING-STONE. Introduces DEF-INC018 (omega-consistency) and proves a stepping stone. The omega-consistency definition is important (used in G1 original form). The undecidability result is superseded by inc/tcp/cqn.
- **Content Directives**:
  - Formal items to preserve: defn[thm:oconsis-q] (omega-consistency) [DEF-INC018] -> DED.6
  - Formal items to drop: thm (omega-consistent extension of Q is not decidable) -- superseded by inc/tcp/cqn
  - Prose: compress to omega-consistency definition + 1 sentence noting the result
  - Examples: cut all
  - Proofs: cut (superseded by stronger result)

### inc/tcp/cqn -- Consistent Extensions of Q are Undecidable
- **Action**: CONDENSE
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.7: Theorems
- **Rationale**: STEPPING-STONE. Strengthens omega-consistency result to simple consistency. Key stepping stone for inc/tcp/inc. Uses diagonal argument (no universal computable relation).
- **Content Directives**:
  - Formal items to preserve: thm (consistent extension of Q is not decidable)
  - Formal items to drop: lem (no universal computable relation) -- fold into proof sketch; cor (true arithmetic not decidable) -- immediate corollary, state as remark
  - Prose: compress to theorem statement + proof sketch
  - Examples: cut all
  - Proofs: preserve sketch only (key idea: if T decidable, construct universal computable relation via representability)

### inc/tcp/cax -- Axiomatizable Theories
- **Action**: CONDENSE
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.6: Computability Theory
- **Rationale**: STEPPING-STONE. Short section establishing axiomatizable implies c.e. Important linking lemma.
- **Content Directives**:
  - Formal items to preserve: lem (axiomatizable implies c.e.)
  - Formal items to drop: (none)
  - Prose: compress to statement
  - Examples: cut all
  - Proofs: preserve sketch only (enumerate all derivations from decidable axiom set)

### inc/tcp/cdc -- Axiomatizable Complete Theories are Decidable
- **Action**: CONDENSE
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.7: Theorems
- **Rationale**: STEPPING-STONE. Key connecting lemma: complete + axiomatizable + consistent => decidable. Directly used in inc/tcp/inc for the computability-theoretic first incompleteness theorem. Note: this result also appears as stepping stone in inc/int/dec; the authoritative treatment is here.
- **Content Directives**:
  - Formal items to preserve: lem (complete + axiomatizable implies decidable)
  - Formal items to drop: (none)
  - Prose: compress to statement + 2-sentence proof idea
  - Examples: cut all
  - Proofs: preserve sketch only (simultaneous search for proof of A and proof of not-A)

### inc/tcp/inc -- Q has no Complete, Consistent, Axiomatizable Extensions
- **Action**: MERGE-INTO:inc/inp/1in
- **Lean Chapter**: CH-META
- **Lean Section**: META.5: First Incompleteness (CP-005)
- **Rationale**: CORE-THM but CP-005 redundancy. This is the computability-theoretic version of the First Incompleteness Theorem, which is weaker than the Rosser version (inc/inp/ros) because it does not construct an explicit independent sentence. The lean text presents CP-005 via the Godel sentence + Rosser improvement in META.5. This section's short proof (combining cqn + cdc) is noted as a remark/alternative proof in META.5.
- **Content Directives**:
  - Formal items to preserve: thm[thm:first-incompleteness] (no complete, consistent, axiomatizable extension of Q) -- survives as remark/alternative proof in inc/inp/1in
  - Formal items to drop: (none)
  - Prose: replace with 2-sentence remark in META.5 noting the alternative computability-theoretic proof
  - Examples: cut all
  - Proofs: preserve sketch only (3-line proof: cqn + cdc => result)

### inc/tcp/ins -- Sentences Provable and Refutable in Q are Computably Inseparable
- **Action**: CONDENSE
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.7: Theorems
- **Rationale**: STEPPING-STONE. Shows computable inseparability of Q and Q-bar (DEF-INC019). Used in inc/tcp/con for the strongest undecidability results.
- **Content Directives**:
  - Formal items to preserve: lem (Q and Q-bar are computably inseparable) [DEF-INC019]
  - Formal items to drop: (none)
  - Prose: compress to definition of computable inseparability + lemma statement
  - Examples: cut all
  - Proofs: preserve sketch only (uses non-existence of universal computable relation)

### inc/tcp/con -- Theories Consistent with Q are Undecidable
- **Action**: CONDENSE
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.7: Theorems
- **Rationale**: STEPPING-STONE. Stronger than cqn: theory need not extend Q, only be consistent with it. The corollary (CP-008 alternative proof) is secondary to the authoritative CP-008 in inc/req/und.
- **Content Directives**:
  - Formal items to preserve: thm (theory consistent with Q is undecidable)
  - Formal items to drop: cor (FOL for language of arithmetic is undecidable) -- duplicate of CP-008, already in inc/req/und
  - Prose: compress to theorem statement
  - Examples: cut all
  - Proofs: preserve sketch only (uses computable inseparability)

### inc/tcp/itp -- Theories in which Q is Interpretable are Undecidable
- **Action**: CONDENSE
- **Lean Chapter**: CH-CMP
- **Lean Section**: CMP.7: Theorems
- **Rationale**: STEPPING-STONE. Most general undecidability result. Introduces interpretability informally (DEF-INC020). Applications to ZFC.
- **Content Directives**:
  - Formal items to preserve: thm (theory interpreting Q and consistent with it is undecidable); cor (no decidable extension of ZFC); cor (FOL for language with binary relation is undecidable) -- strongest form of CP-008
  - Formal items to drop: cor (no complete consistent axiomatizable extension of ZFC) -- follows immediately; DEF-INC020 (Interpretability informal) -- keep as remark, not formal definition
  - Prose: compress to theorem + corollaries + 1 remark about decidability boundary (unary predicates + at most one unary function)
  - Examples: cut all
  - Proofs: preserve sketch only (small modification of inc/tcp/con proof)

---

## Chapter 5: Incompleteness and Provability (`inc/inp/`)

### inc/inp/int -- Introduction (Incompleteness and Provability)
- **Action**: CUT
- **Lean Chapter**: (none)
- **Lean Section**: (none)
- **Rationale**: PEDAGOGICAL only. Motivates the Godel sentence via the Epimenides/liar paradox and Quine's version. No formal items (fixed-point lemma merely previewed informally). The fixed-point lemma explanation in inc/inp/fix already contains the necessary motivation.
- **Content Directives**:
  - Formal items to preserve: (none)
  - Formal items to drop: lem (fixed-point lemma -- informal preview) -- pedagogical
  - Prose: cut entirely
  - Examples: cut all
  - Proofs: N/A

### inc/inp/fix -- The Fixed-Point Lemma
- **Action**: KEEP
- **Lean Chapter**: CH-META
- **Lean Section**: META.5: First Incompleteness (DEF-INC021)
- **Rationale**: CORE-THM. The fixed-point (diagonalization) lemma is the fundamental technical tool for all major incompleteness results. Must be preserved in full including the diag function construction and the formal proof.
- **Content Directives**:
  - Formal items to preserve: lem[lem:fixed-point] (fixed-point lemma) [DEF-INC021]
  - Formal items to drop: prob (no truth definition via fixed point) -- pedagogical exercise (but the idea reappears in inc/inp/tar)
  - Prose: preserve (the explanation of diag function construction is essential for understanding)
  - Examples: N/A
  - Proofs: preserve full

### inc/inp/1in -- The First Incompleteness Theorem
- **Action**: ABSORB:{inc/tcp/inc}
- **Lean Chapter**: CH-META
- **Lean Section**: META.5: First Incompleteness (CP-005)
- **Rationale**: CORE-THM. This is Godel's original proof of the First Incompleteness Theorem via the Godel sentence construction. This is the authoritative section for CP-005. Absorbs inc/tcp/inc (computability-theoretic version) as an alternative proof remark.
- **Content Directives**:
  - Formal items to preserve: lem[lem:cons-G-unprov] (if T consistent, T does not derive G_T); defn[thm:oconsis-q] (omega-consistency) -- cross-ref to DED.6 for authoritative definition; lem[lem:omega-cons-G-unref] (if T omega-consistent, T does not derive not-G_T); thm[thm:first-incompleteness] (First Incompleteness Theorem, omega-consistency version) [CP-005]
  - Formal items to drop: prob (consistent but omega-inconsistent theory) -- pedagogical exercise
  - From inc/tcp/inc: absorb as remark "Alternative proof via computability theory: combining undecidability of consistent extensions of Q with the fact that axiomatizable complete theories are decidable yields the result without constructing an explicit Godel sentence."
  - Prose: preserve (proof construction is essential)
  - Examples: N/A
  - Proofs: preserve full (both lemmas + theorem)

### inc/inp/ros -- Rosser's Theorem
- **Action**: KEEP
- **Lean Chapter**: CH-META
- **Lean Section**: META.5: First Incompleteness (CP-005 strengthened)
- **Rationale**: CORE-THM. Rosser's improvement replaces omega-consistency with simple consistency. Introduces the Rosser provability predicate (DEF-INC022) and Rosser sentence (DEF-INC023). This is the standard modern form of the First Incompleteness Theorem.
- **Content Directives**:
  - Formal items to preserve: thm[thm:rosser] (Rosser's Theorem: consistent + axiomatizable + extends Q => incomplete) [CP-005 strengthened]; DEF-INC022 (Rosser provability predicate RProv_T); DEF-INC023 (Rosser sentence R_T)
  - Formal items to drop: prob (computable inseparability) -- exercise, already covered in inc/tcp/ins
  - Prose: preserve (the Rosser provability predicate construction is essential)
  - Examples: N/A
  - Proofs: preserve full (both directions of the independence argument)

### inc/inp/gop -- Comparison with Godel's Original Paper
- **Action**: CUT
- **Lean Chapter**: (none)
- **Lean Section**: (none)
- **Rationale**: PEDAGOGICAL only. Brief historical comparison with Godel's 1931 paper. No formal items. Historical details about the 45 primitive recursive functions and the beta-lemma are not needed in the lean text.
- **Content Directives**:
  - Formal items to preserve: (none)
  - Formal items to drop: (none -- no formal items)
  - Prose: cut entirely
  - Examples: cut all
  - Proofs: N/A

### inc/inp/prc -- The Derivability Conditions for PA
- **Action**: KEEP
- **Lean Chapter**: CH-META
- **Lean Section**: META.6: Second Incompleteness (DEF-INC024)
- **Rationale**: CORE-DEF. Defines the three Hilbert-Bernays-Lob derivability conditions (P1-P3) that are the hypotheses for the Second Incompleteness Theorem and Lob's Theorem. These are essential for understanding the proof structure of G2 and Lob.
- **Content Directives**:
  - Formal items to preserve: P1 (provability implies provable provability); P2 (provable implication distributes over provability); P3 (provable provability of provability) [DEF-INC024]; P4 (mentioned but noted as not needed)
  - Formal items to drop: (none)
  - Prose: preserve (conditions P1-P3 + the discussion of why P3 requires work)
  - Examples: N/A
  - Proofs: N/A (conditions stated, verification not carried out -- following Godel's practice)

### inc/inp/2in -- The Second Incompleteness Theorem
- **Action**: KEEP
- **Lean Chapter**: CH-META
- **Lean Section**: META.6: Second Incompleteness (CP-006)
- **Rationale**: CORE-THM. The Second Incompleteness Theorem is CP-006. Both the PA-specific version and the general version (for any T satisfying P1-P3) are essential. The proof sketch using derivability conditions is the standard modern presentation.
- **Content Directives**:
  - Formal items to preserve: thm[thm:second-incompleteness] (PA consistent => PA does not derive Con(PA)) [CP-006]; thm[thm:second-incompleteness-gen] (general version for T with P1-P3) [CP-006 generalized]
  - Formal items to drop: prob (PA derives G_PA -> Con(PA)) -- exercise
  - Prose: preserve (the step-by-step derivation using P1-P3 is the heart of the proof)
  - Examples: N/A
  - Proofs: preserve full (both specific and general versions)

### inc/inp/lob -- Lob's Theorem
- **Action**: KEEP
- **Lean Chapter**: CH-META
- **Lean Section**: META.6: Second Incompleteness (DEF-INC025)
- **Rationale**: CORE-THM. Lob's Theorem (DEF-INC025) generalizes the Second Incompleteness Theorem. The proof uses the fixed-point lemma applied to Prov(y) -> A. The corollary that G2 follows from Lob (take A = falsum) provides an elegant alternative derivation.
- **Content Directives**:
  - Formal items to preserve: thm[thm:lob] (Lob's Theorem) [DEF-INC025]; the corollary deriving G2 from Lob; the observation about the fixed point of Prov(x) being derivable
  - Formal items to drop: prob (conditions for derivability statements) -- exercise
  - Prose: preserve (the Santa Claus heuristic is the best available explanation of the proof idea, and doubles as motivation)
  - Examples: N/A
  - Proofs: preserve full

### inc/inp/tar -- The Undefinability of Truth
- **Action**: KEEP
- **Lean Chapter**: CH-META
- **Lean Section**: META.7: Undefinability (CP-007)
- **Rationale**: CORE-THM. Tarski's Undefinability of Truth theorem is CP-007. The section defines "definable in N," proves every computable relation is definable, proves the halting relation is definable, and then proves the set of true sentences is NOT definable. Clean, self-contained proof.
- **Content Directives**:
  - Formal items to preserve: defn (definable in N); lem (every computable relation is definable in N); lem (halting relation is definable in N); thm[thm:tarski] (set of true sentences not definable) [CP-007]
  - Formal items to drop: prob (Q-provable set is definable) -- exercise
  - Prose: preserve (including Tarski's philosophical analysis of truth predicates -- this is a 1-paragraph remark that contextualizes the result, not pedagogical fluff)
  - Examples: N/A
  - Proofs: preserve full (all lemmas + main theorem)

---

### INC Batch Summary
- **Total sections**: 44
- **Action distribution**: 8 KEEP, 21 CONDENSE, 5 MERGE-INTO, 3 ABSORB, 6 CUT, 1 DISTRIBUTE
- **Verification**: 8 + 21 + 5 + 3 + 6 + 1 = 44 (correct)
- **Detailed action tally**:
  - KEEP (8): inc/req/und, inc/inp/s1c, inc/inp/fix, inc/inp/ros, inc/inp/prc, inc/inp/2in, inc/inp/lob, inc/inp/tar
  - ABSORB (3): inc/art/plk [absorbs pnd, pax], inc/inp/1in [absorbs tcp/inc], inc/req/crq [absorbs cee, cre]
  - CONDENSE (21): inc/int/dec, inc/art/cod, inc/art/trm, inc/art/frm, inc/art/sub, inc/req/int, inc/req/rpc, inc/req/bet, inc/req/pri, inc/req/bre, inc/req/cmp, inc/req/min, inc/req/rel, inc/tcp/qce, inc/tcp/oqn, inc/tcp/cqn, inc/tcp/cax, inc/tcp/cdc, inc/tcp/ins, inc/tcp/con, inc/tcp/itp
  - MERGE-INTO (5): inc/art/pnd -> plk, inc/art/pax -> plk, inc/tcp/inc -> 1in, inc/req/cee -> crq, inc/req/cre -> crq
  - CUT (6): inc/int/bgr, inc/int/ovr, inc/art/int, inc/tcp/int, inc/inp/int, inc/inp/gop
  - DISTRIBUTE (1): inc/int/def
- **Taxonomy coverage**: All INC-related taxonomy items have authoritative homes:
  - CP-005 (First Incompleteness) -> inc/inp/1in (ABSORB from inc/tcp/inc)
  - CP-006 (Second Incompleteness) -> inc/inp/2in (KEEP)
  - CP-007 (Tarski Undefinability) -> inc/inp/tar (KEEP)
  - CP-008 (Church Undecidability) -> inc/req/und (KEEP)
  - DEF-INC010, DEF-INC011 (Symbol code, Godel number) -> inc/art/cod (CONDENSE)
  - DEF-INC012 (Proof Predicate) -> inc/art/plk (ABSORB from pnd, pax)
  - DEF-INC013 (Beta function) -> inc/req/bet (CONDENSE)
  - DEF-INC015-017 (Arithmetic Hierarchy) -> inc/inp/s1c (KEEP)
  - DEF-INC018 (Omega-consistency) -> inc/tcp/oqn (CONDENSE, definition goes to DED.6)
  - DEF-INC019 (Computable inseparability) -> inc/tcp/ins (CONDENSE)
  - DEF-INC020 (Interpretability) -> inc/tcp/itp (CONDENSE, kept as remark)
  - DEF-INC021 (Fixed-Point Lemma) -> inc/inp/fix (KEEP)
  - DEF-INC022 (Rosser provability) -> inc/inp/ros (KEEP)
  - DEF-INC023 (Rosser sentence) -> inc/inp/ros (KEEP)
  - DEF-INC024 (Derivability Conditions) -> inc/inp/prc (KEEP)
  - DEF-INC025 (Lob's Theorem) -> inc/inp/lob (KEEP)
  - DEF-CMP009 (Representability) -> inc/int/def DISTRIBUTE to CMP.5
  - DEF-DED011 (Q) -> inc/int/def DISTRIBUTE to DED.6
  - DEF-DED012 (PA) -> inc/int/def DISTRIBUTE to DED.6
  - DEF-SEM017 (Standard Model) -> inc/int/def DISTRIBUTE to SEM.5
  - DEF-SEM018 (True Arithmetic) -> inc/int/def DISTRIBUTE to SEM.5
  - DEF-CMP011 (Axiomatizable Theory) -> inc/int/def DISTRIBUTE to CMP.6
- **Compression targets resolved**:
  - DEF-INC012 (Proof Predicate, 3 variants): inc/art/plk primary, inc/art/pnd and inc/art/pax MERGE-INTO
  - CP-005 (2 formulations): inc/inp/1in primary (Godel sentence), inc/tcp/inc MERGE-INTO
  - DEF-CMP009 (Representability): inc/int/def distributes to CMP.5; inc/req/int provides the representability theorem context
  - DEF-INC014 (Class C) + inc/req/cre: alternative proof path MERGE-INTO inc/req/crq
  - DEF-INC018 (Omega-consistency, defined in both inc/tcp/oqn and inc/inp/1in): inc/tcp/oqn is authoritative for definition -> DED.6, inc/inp/1in cross-references
- **Lean chapter distribution** (surviving sections only, excluding CUT and MERGE-INTO sources):
  - CH-META: 8 sections (inc/inp/fix, inc/inp/1in [+absorb], inc/inp/ros, inc/inp/prc, inc/inp/2in, inc/inp/lob, inc/inp/tar, inc/req/und)
  - CH-CMP: 20 sections (inc/int/dec, inc/art/cod, inc/art/trm, inc/art/frm, inc/art/sub, inc/art/plk [+absorb], inc/req/int, inc/req/rpc, inc/req/bet, inc/req/pri, inc/req/bre, inc/req/cmp, inc/req/min, inc/req/crq [+absorb], inc/req/rel, inc/tcp/qce, inc/tcp/cqn, inc/tcp/cax, inc/tcp/cdc, inc/tcp/ins, inc/tcp/con, inc/tcp/itp)
  - CH-DED: 1 section (inc/tcp/oqn omega-consistency definition -> DED.6)
  - CH-SEM: 0 sections directly (SEM.5 items come from DISTRIBUTE of inc/int/def)
  - DISTRIBUTE across CH-DED + CH-SEM + CH-CMP: 1 section (inc/int/def)

**MERGE-INTO/ABSORB pairing verification (QC-8)**:
- inc/art/pnd MERGE-INTO inc/art/plk <-> inc/art/plk ABSORB:{inc/art/pnd, inc/art/pax} -- paired
- inc/art/pax MERGE-INTO inc/art/plk <-> (same ABSORB entry) -- paired
- inc/tcp/inc MERGE-INTO inc/inp/1in <-> inc/inp/1in ABSORB:{inc/tcp/inc} -- paired
- inc/req/cee MERGE-INTO inc/req/crq <-> inc/req/crq ABSORB:{inc/req/cee, inc/req/cre} -- paired
- inc/req/cre MERGE-INTO inc/req/crq <-> (same ABSORB entry) -- paired
- All 5 MERGE-INTO entries have corresponding ABSORB entries. QC-8 passes.

## CH-SET: Formal Set Theory (Level-1)

---

## Chapter 1: story/ -- The Iterative Conception

### sth/story/extensionality -- Extensionality
- **Action**: KEEP
- **Lean Chapter**: CH-SET
- **Lean Section**: SET.2: ZFC Axioms
- **Rationale**: CORE-DEF. Authoritative introduction of AX-SET001 (Extensionality), the first ZFC axiom. The formal statement is clean and standalone.
- **Content Directives**:
  - Formal items to preserve: axiom[Extensionality] (AX-SET001)
  - Formal items to drop: none
  - Prose: preserve (brief, directly supports axiom statement)
  - Examples: preserve (implicit in the axiom statement)
  - Proofs: N/A (no proofs in this section)

---

### sth/story/rus -- Russell's Paradox (again)
- **Action**: CUT
- **Lean Chapter**: CH-SET
- **Lean Section**: N/A
- **Rationale**: PEDAGOGICAL. Re-derives Russell's Paradox already covered in sfr/. No taxonomy items introduced; Naive Comprehension and Russell's Paradox are OL-ONLY.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: defish[Naive Comprehension] (OL-ONLY, rejected principle), thm[Russell's Paradox] (OL-ONLY, redundant with sfr/)
  - Prose: N/A
  - Examples: N/A
  - Proofs: N/A

---

### sth/story/predicative -- Predicative and Impredicative
- **Action**: CUT
- **Lean Chapter**: CH-SET
- **Lean Section**: N/A
- **Rationale**: PEDAGOGICAL. Philosophical discussion of predicativity vs. impredicativity. No formal definitions or taxonomy items.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: defish[Predicative Comprehension] (OL-ONLY, informal)
  - Prose: N/A
  - Examples: N/A
  - Proofs: N/A

---

### sth/story/approach -- The Cumulative-Iterative Approach
- **Action**: CUT
- **Lean Chapter**: CH-SET
- **Lean Section**: N/A
- **Rationale**: PEDAGOGICAL. Informal motivational narrative about the cumulative-iterative conception. No formal items or taxonomy content. The lean text's SET.1 and SET.2 opening prose can incorporate a compressed version of this motivation (1-2 sentences).
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: none (no formal items)
  - Prose: N/A
  - Examples: N/A
  - Proofs: N/A

---

### sth/story/urelements -- Urelements or Not?
- **Action**: CUT
- **Lean Chapter**: CH-SET
- **Lean Section**: N/A
- **Rationale**: PEDAGOGICAL. Design-decision discussion about excluding urelements. No formal content, no taxonomy items.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: none (no formal items)
  - Prose: N/A
  - Examples: N/A
  - Proofs: N/A

---

### sth/story/blv -- Appendix: Frege's Basic Law V
- **Action**: CUT
- **Lean Chapter**: CH-SET
- **Lean Section**: N/A
- **Rationale**: TANGENTIAL. Historical appendix on Frege's system. OL-ONLY items (lem[Fregeextensions], etc.) are purely historical and outside taxonomy scope.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: lem[Fregeextensions] (OL-ONLY, historical), lem (Naive Comprehension from BLV) (OL-ONLY, historical)
  - Prose: N/A
  - Examples: N/A
  - Proofs: N/A

---

## Chapter 2: z/ -- Steps towards Z

### sth/z/story -- The Story in More Detail
- **Action**: CONDENSE
- **Lean Chapter**: CH-SET
- **Lean Section**: SET.2: ZFC Axioms (introductory subsection)
- **Rationale**: STEPPING-STONE. The informal principles StagesHier, StagesOrd, StagesAcc provide philosophical context for the axioms. Compress to 1-paragraph summary that precedes the axiom statements in SET.2.
- **Content Directives**:
  - Formal items to preserve: none (no formal items -- informal principles only)
  - Formal items to drop: none
  - Prose: compress to 1 paragraph stating the three informal principles and their role in justifying ZFC
  - Examples: cut all
  - Proofs: N/A

---

### sth/z/sep -- Separation
- **Action**: KEEP
- **Lean Chapter**: CH-SET
- **Lean Section**: SET.2: ZFC Axioms
- **Rationale**: CORE-DEF. Authoritative introduction of AX-SET006 (Separation) and derives AX-SET002 (Empty Set existence) as consequence. The no-universal-set theorem is a key early result.
- **Content Directives**:
  - Formal items to preserve: axiom[Scheme of Separation] (AX-SET006), prop[emptyexists] (AX-SET002 derivation)
  - Formal items to drop: thm[NoUniversalSet] (OL-ONLY, but preserve as a 1-line corollary remark), prop (A\B exists) (OL-ONLY, technical), prop[intersectionsexist] (OL-ONLY, technical)
  - Prose: preserve (directly supports axiom definitions)
  - Examples: preserve
  - Proofs: preserve full for prop[emptyexists]; cut proofs for OL-ONLY technical props

---

### sth/z/union -- Union
- **Action**: KEEP
- **Lean Chapter**: CH-SET
- **Lean Section**: SET.2: ZFC Axioms
- **Rationale**: CORE-DEF. Authoritative introduction of AX-SET004 (Union).
- **Content Directives**:
  - Formal items to preserve: axiom[Union] (AX-SET004)
  - Formal items to drop: none
  - Prose: preserve
  - Examples: preserve
  - Proofs: N/A (no proofs)

---

### sth/z/pairs -- Pairs
- **Action**: KEEP
- **Lean Chapter**: CH-SET
- **Lean Section**: SET.2: ZFC Axioms
- **Rationale**: CORE-DEF. Authoritative introduction of AX-SET003 (Pairing). Also derives singletons, binary union, and ordered pairs as consequences.
- **Content Directives**:
  - Formal items to preserve: axiom[Pairs] (AX-SET003)
  - Formal items to drop: prop[pairsconsequences] (OL-ONLY, but preserve statement as a remark -- these are standard consequences)
  - Prose: preserve
  - Examples: preserve
  - Proofs: preserve sketch only for pairsconsequences

---

### sth/z/power -- Powersets
- **Action**: KEEP
- **Lean Chapter**: CH-SET
- **Lean Section**: SET.2: ZFC Axioms
- **Rationale**: CORE-DEF. Authoritative introduction of AX-SET005 (Power Set).
- **Content Directives**:
  - Formal items to preserve: axiom[Powersets] (AX-SET005)
  - Formal items to drop: prop[thm:Products] (OL-ONLY, Cartesian product existence -- preserve as 1-line remark)
  - Prose: preserve
  - Examples: preserve
  - Proofs: cut proof for Products (standard consequence)

---

### sth/z/infinity-again -- Infinity
- **Action**: KEEP
- **Lean Chapter**: CH-SET
- **Lean Section**: SET.2: ZFC Axioms
- **Rationale**: CORE-DEF. Authoritative introduction of AX-SET008 (Infinity). Also defines omega informally.
- **Content Directives**:
  - Formal items to preserve: axiom[Infinity] (AX-SET008), defn[defnomega] (OL-ONLY but critical -- defines omega, keep as remark)
  - Formal items to drop: prop[naturalnumbersarentinfinite] (OL-ONLY, technical consequence)
  - Prose: preserve
  - Examples: preserve
  - Proofs: cut proof for naturalnumbersarentinfinite (technical)

---

### sth/z/milestone -- Z^-: a Milestone
- **Action**: CONDENSE
- **Lean Chapter**: CH-SET
- **Lean Section**: SET.2: ZFC Axioms (closing remark)
- **Rationale**: STEPPING-STONE. Collects axioms of Z^- into named theory. Useful as a 2-sentence summary remark at end of axiom block, not a standalone section.
- **Content Directives**:
  - Formal items to preserve: defn (Z^-) as inline remark (OL-ONLY)
  - Formal items to drop: none
  - Prose: compress to 2-sentence remark defining Z^- = {Extensionality, Pairing, Union, Power Set, Separation, Infinity}
  - Examples: cut all
  - Proofs: N/A

---

### sth/z/nat -- Selecting our Natural Numbers
- **Action**: CUT
- **Lean Chapter**: CH-SET
- **Lean Section**: N/A
- **Rationale**: PEDAGOGICAL. Philosophical discussion of Benacerraf's problem. No formal content, no taxonomy items.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: none (no formal items)
  - Prose: N/A
  - Examples: N/A
  - Proofs: N/A

---

### sth/z/arbintersections -- Appendix: Closure, Comprehension, and Intersection
- **Action**: CONDENSE
- **Lean Chapter**: CH-SET
- **Lean Section**: SET.2: ZFC Axioms (appendix note)
- **Rationale**: STEPPING-STONE. Technical appendix showing intersections via Separation. Useful as a brief remark establishing that Z^- supports closure definitions from BST, but does not need standalone treatment.
- **Content Directives**:
  - Formal items to preserve: none in taxonomy (all OL-ONLY)
  - Formal items to drop: all (technical details)
  - Prose: compress to 1-paragraph remark on intersection existence via Separation
  - Examples: cut all
  - Proofs: cut (technical)

---

## Chapter 3: ordinals/ -- Ordinals

### sth/ordinals/intro -- Introduction
- **Action**: CUT
- **Lean Chapter**: CH-SET
- **Lean Section**: N/A
- **Rationale**: PEDAGOGICAL. Brief motivational introduction with no formal content. The lean text's SET.3 opening can incorporate any necessary motivation in 1-2 sentences.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: none (no formal items)
  - Prose: N/A
  - Examples: N/A
  - Proofs: N/A

---

### sth/ordinals/idea -- The General Idea of an Ordinal
- **Action**: CUT
- **Lean Chapter**: CH-SET
- **Lean Section**: N/A
- **Rationale**: PEDAGOGICAL. Informal examples of ordinal orderings on natural numbers. No formal definitions or taxonomy items.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: none (no formal items)
  - Prose: N/A
  - Examples: N/A
  - Proofs: N/A

---

### sth/ordinals/wo -- Well-Orderings
- **Action**: KEEP
- **Lean Chapter**: CH-SET
- **Lean Section**: SET.3: Ordinals
- **Rationale**: CORE-DEF. Defines well-ordering (DEF-SET009 in taxonomy, though SECTION-MAP maps propwoinduction to DEF-SET006 kernel). Establishes the strong induction principle on well-orderings, which is the foundation for transfinite induction. Also provides the authoritative home for DEF-SET009 (Well-Ordering).
- **Content Directives**:
  - Formal items to preserve: defn (well-ordering) (DEF-SET009), prop[wo:strictorder], prop[propwoinduction] (kernel of DEF-SET006/DEF-SET005)
  - Formal items to drop: none
  - Prose: preserve
  - Examples: preserve
  - Proofs: preserve full

---

### sth/ordinals/iso -- Order-Isomorphisms
- **Action**: CONDENSE
- **Lean Chapter**: CH-SET
- **Lean Section**: SET.3: Ordinals
- **Rationale**: STEPPING-STONE. Extensive technical development of order-isomorphism theory. Key result thm[woalwayscomparable] is needed by sth/ordinals/vn and the ordinal representation theorem. Compress verification proofs to sketches.
- **Content Directives**:
  - Formal items to preserve: defn (order-isomorphism), defn (initial segment A_a), thm[thm:woalwayscomparable] (key theorem), lem[wellordnotinitial] (needed by basic), lem[wellordinitialsegment] (needed by ordtype), lem[lemordsegments] (needed by ordtype)
  - Formal items to drop: lem[isoscompose] (trivial), cor[ordisoisequiv] (trivial consequence), prop[ordisounique] (OL-ONLY, preserve statement only)
  - Prose: compress to intro + definitions only
  - Examples: cut all
  - Proofs: preserve sketch only for thm[woalwayscomparable]; cut detailed verification proofs for other lemmas (preserve statements)

---

### sth/ordinals/vn -- Von Neumann's Construction of the Ordinals
- **Action**: KEEP
- **Lean Chapter**: CH-SET
- **Lean Section**: SET.3: Ordinals
- **Rationale**: CORE-DEF. Authoritative introduction of DEF-SET001 (Ordinal), DEF-SET002 (Transitive Set), DEF-SET003 (Von Neumann Ordinal). These are the central definitions of ordinal theory.
- **Content Directives**:
  - Formal items to preserve: defn (transitive set) (DEF-SET002), defn (ordinal = transitive + well-ordered by membership) (DEF-SET001/DEF-SET003)
  - Formal items to drop: none
  - Prose: preserve
  - Examples: preserve (first few ordinals as natural numbers)
  - Proofs: N/A

---

### sth/ordinals/basic -- Basic Properties of the Ordinals
- **Action**: KEEP
- **Lean Chapter**: CH-SET
- **Lean Section**: SET.3: Ordinals
- **Rationale**: CORE-THM. Central section establishing DEF-SET006 (Transfinite Induction), Trichotomy, and PRIM-SET003 (Proper Class via Burali-Forti Paradox). Multiple taxonomy items have their authoritative home here.
- **Content Directives**:
  - Formal items to preserve: thm[ordinductionschema] (DEF-SET006, Transfinite Induction), thm[ordtrichotomy] (Trichotomy), thm[buraliforti] (PRIM-SET003, Burali-Forti Paradox), cor[corordtransitiveord], lem[ordmemberord]
  - Formal items to drop: cor[ordissetofsmallerord] (OL-ONLY, immediate), prop (no infinite descending chain) (OL-ONLY, standard), prop[ordinalsaresubsets] (OL-ONLY, preserve statement), prop[ordisoidentity] (OL-ONLY, preserve statement)
  - Prose: preserve
  - Examples: preserve
  - Proofs: preserve full for ordinductionschema, ordtrichotomy, buraliforti; preserve sketch only for others

---

### sth/ordinals/replacement -- Replacement
- **Action**: KEEP
- **Lean Chapter**: CH-SET
- **Lean Section**: SET.2: ZFC Axioms
- **Rationale**: CORE-DEF. Authoritative introduction of AX-SET007 (Replacement). Although placed in the ordinals chapter in OL, the axiom statement itself belongs in SET.2 in the lean text.
- **Content Directives**:
  - Formal items to preserve: axiom[Scheme of Replacement] (AX-SET007)
  - Formal items to drop: cor (image of set under term exists) (OL-ONLY, standard consequence)
  - Prose: preserve (axiom motivation is relevant)
  - Examples: preserve
  - Proofs: N/A for axiom statement

---

### sth/ordinals/zfm -- ZF^-: a milestone
- **Action**: CONDENSE
- **Lean Chapter**: CH-SET
- **Lean Section**: SET.2: ZFC Axioms (closing remark)
- **Rationale**: STEPPING-STONE. Milestone collecting axioms of ZF^- = Z^- + Replacement. Useful as a 1-sentence inline remark, not standalone.
- **Content Directives**:
  - Formal items to preserve: defn (ZF^-) as inline remark (OL-ONLY)
  - Formal items to drop: none
  - Prose: compress to 1-sentence remark
  - Examples: cut all
  - Proofs: N/A

---

### sth/ordinals/ordtype -- Ordinals as Order-Types
- **Action**: KEEP
- **Lean Chapter**: CH-SET
- **Lean Section**: SET.3: Ordinals
- **Rationale**: CORE-THM. Proves the Ordinal Representation Theorem (thm[thmOrdinalRepresentation]): every well-ordering is isomorphic to a unique ordinal. Major theorem requiring Replacement. Defines order type.
- **Content Directives**:
  - Formal items to preserve: thm[thmOrdinalRepresentation], defn (order type ordtype(A,<)), cor[ordtypesworklikeyouwant]
  - Formal items to drop: none
  - Prose: preserve
  - Examples: preserve
  - Proofs: preserve full

---

### sth/ordinals/opps -- Successor and Limit Ordinals
- **Action**: KEEP
- **Lean Chapter**: CH-SET
- **Lean Section**: SET.3: Ordinals
- **Rationale**: CORE-DEF. Authoritative introduction of DEF-SET004 (Successor Ordinal) and DEF-SET005 (Limit Ordinal). Also provides Simple Transfinite Induction, needed throughout the development.
- **Content Directives**:
  - Formal items to preserve: defn (successor ordinal, limit ordinal) (DEF-SET004, DEF-SET005), thm[simpletransrecursion] (Simple Transfinite Induction), defn[defsupstrict] (lsub/supstrict)
  - Formal items to drop: none
  - Prose: preserve
  - Examples: preserve
  - Proofs: preserve full

---

## Chapter 4: spine/ -- Stages and Ranks

### sth/spine/valpha -- Defining the Stages as the V_alpha's
- **Action**: KEEP
- **Lean Chapter**: CH-SET
- **Lean Section**: SET.5: Advanced Topics (Von Neumann Hierarchy)
- **Rationale**: CORE-DEF. Authoritative introduction of DEF-SET012 (Von Neumann Hierarchy). Defines V_alpha by transfinite recursion, formalizing the cumulative hierarchy.
- **Content Directives**:
  - Formal items to preserve: defn[defValphas] (DEF-SET012, V_alpha definition)
  - Formal items to drop: none
  - Prose: preserve
  - Examples: preserve
  - Proofs: N/A (definition, not theorem)

---

### sth/spine/recursion -- The Transfinite Recursion Theorem(s)
- **Action**: KEEP
- **Lean Chapter**: CH-SET
- **Lean Section**: SET.3: Ordinals (or SET.6: Theorems)
- **Rationale**: CORE-THM. Proves DEF-SET007 / THM-SET002 (Transfinite Recursion Theorem). Key technical section using Transfinite Induction + Replacement. Vindicates V_alpha definition.
- **Content Directives**:
  - Formal items to preserve: defn (alpha-approximation), lem[transrecursionfun] (Bounded Recursion), thm[transrecursionschema] (General Recursion, DEF-SET007/THM-SET002), thm[simplerecursionschema] (Simple Recursion)
  - Formal items to drop: none
  - Prose: preserve
  - Examples: preserve (vindication of V_alpha at end)
  - Proofs: preserve full for all three results (they form a tight chain)

---

### sth/spine/Valphabasic -- Basic Properties of Stages
- **Action**: CONDENSE
- **Lean Chapter**: CH-SET
- **Lean Section**: SET.5: Advanced Topics
- **Rationale**: STEPPING-STONE. Technical properties of V_alpha hierarchy. Preserve key statements, compress verification proofs.
- **Content Directives**:
  - Formal items to preserve: lem[Valphabasicprops] (V_alpha transitive, potent, cumulative -- statement only), lem[Valphanotref] (V_alpha not in V_alpha -- statement only)
  - Formal items to drop: defn (potent set) (OL-ONLY, auxiliary), cor (alpha in beta iff V_alpha in V_beta) (OL-ONLY)
  - Prose: compress to intro + key lemma statements
  - Examples: cut all
  - Proofs: preserve sketch only

---

### sth/spine/foundation -- Foundation
- **Action**: CONDENSE
- **Lean Chapter**: CH-SET
- **Lean Section**: SET.2: ZFC Axioms
- **Rationale**: STEPPING-STONE. Introduces Foundation axiom (AX-SET008 in the DOMAIN-SET-FORMAL numbering, where AX-SET008 = Foundation/Regularity). The SECTION-MAP lists this as OL-ONLY for Foundation, but the taxonomy's AX-SET008 is "Foundation (Regularity)." This section provides the authoritative Foundation axiom statement. Compress the lengthy proof of Foundation => Regularity.
- **Content Directives**:
  - Formal items to preserve: axiom[Foundation] (maps to AX-SET008 per domain spec), defish[Regularity] (informal equivalent), defn (transitive closure trcl(A))
  - Formal items to drop: prop[subsetoftrcl] (OL-ONLY, technical), lem[lem:TransitiveWellFounded] (OL-ONLY, technical stepping stone), thm[zfentailsregularity] (OL-ONLY, preserve statement with proof sketch)
  - Prose: compress to intro + axiom statement + brief remark on Foundation-Regularity equivalence
  - Examples: cut all
  - Proofs: preserve sketch only for zfentailsregularity; cut detailed proofs

---

### sth/spine/zf -- Z and ZF: A Milestone
- **Action**: CONDENSE
- **Lean Chapter**: CH-SET
- **Lean Section**: SET.2: ZFC Axioms (closing remark)
- **Rationale**: STEPPING-STONE. Milestone defining Z = Z^- + Foundation, ZF = ZF^- + Foundation = Z + Replacement. Compress to 2-sentence remark.
- **Content Directives**:
  - Formal items to preserve: defn (Z), defn (ZF) as inline remarks (OL-ONLY)
  - Formal items to drop: none
  - Prose: compress to 2-sentence remark defining Z and ZF
  - Examples: cut all
  - Proofs: N/A

---

### sth/spine/rank -- Rank
- **Action**: CONDENSE
- **Lean Chapter**: CH-SET
- **Lean Section**: SET.5: Advanced Topics
- **Rationale**: STEPPING-STONE. Defines rank and proves epsilon-induction. Compress proofs; preserve key definitions and statements.
- **Content Directives**:
  - Formal items to preserve: defn[defnsetrank] (rank of a set), thm (epsilon-Induction Scheme -- statement), cor[ordsetrankalpha] (rank(alpha) = alpha for ordinals -- statement)
  - Formal items to drop: prop[ranksexist] (OL-ONLY, technical), prop[valphalowerrank] (OL-ONLY, technical), prop[rankmemberslower] (OL-ONLY, technical), prop[ranksupstrict] (OL-ONLY, technical), prop[zfminusregularityfoundation] (OL-ONLY, preserve statement as remark)
  - Prose: compress to intro + definition + key results
  - Examples: cut all
  - Proofs: preserve sketch only for epsilon-Induction; cut other proofs

---

## Chapter 5: replacement/ -- Replacement

### sth/replacement/intro -- Introduction
- **Action**: CUT
- **Lean Chapter**: CH-SET
- **Lean Section**: N/A
- **Rationale**: PEDAGOGICAL. Brief introduction framing the question of justifying Replacement. No formal content.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: none (no formal items)
  - Prose: N/A
  - Examples: N/A
  - Proofs: N/A

---

### sth/replacement/strength -- The Strength of Replacement
- **Action**: CONDENSE
- **Lean Chapter**: CH-SET
- **Lean Section**: SET.5: Advanced Topics
- **Rationale**: STEPPING-STONE. Shows Z cannot prove existence of omega+omega. Introduces formula relativization. Useful result but compress the model-theoretic argument.
- **Content Directives**:
  - Formal items to preserve: defn[formularelativization] (relativization of formulas to a set M -- OL-ONLY but useful for SET.5)
  - Formal items to drop: none beyond compression
  - Prose: compress to intro + relativization definition + 1-paragraph summary of V_{omega+omega} model argument
  - Examples: cut all
  - Proofs: preserve sketch only

---

### sth/replacement/extrinsic -- Extrinsic Considerations about Replacement
- **Action**: CUT
- **Lean Chapter**: CH-SET
- **Lean Section**: N/A
- **Rationale**: PEDAGOGICAL. Philosophical discussion of extrinsic justification (Boolos). No formal content, no taxonomy items.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: none (no formal items)
  - Prose: N/A
  - Examples: N/A
  - Proofs: N/A

---

### sth/replacement/limofsize -- Limitation-of-size
- **Action**: CUT
- **Lean Chapter**: CH-SET
- **Lean Section**: N/A
- **Rationale**: PEDAGOGICAL. Philosophical discussion of limitation-of-size as justification for Replacement. No formal items, no taxonomy content.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: (informal principle: LimOfSize) (OL-ONLY)
  - Prose: N/A
  - Examples: N/A
  - Proofs: N/A

---

### sth/replacement/absinf -- Replacement and "Absolute Infinity"
- **Action**: CUT
- **Lean Chapter**: CH-SET
- **Lean Section**: N/A
- **Rationale**: PEDAGOGICAL. Philosophical discussion of Shoenfield's cofinality-based justification. Informal principles StagesInex, StagesCofin are OL-ONLY. No formal content.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: (informal principles: StagesInex, StagesCofin) (OL-ONLY)
  - Prose: N/A
  - Examples: N/A
  - Proofs: N/A

---

### sth/replacement/ref -- Replacement and Reflection
- **Action**: CONDENSE
- **Lean Chapter**: CH-SET
- **Lean Section**: SET.5: Advanced Topics
- **Rationale**: STEPPING-STONE. States the Reflection Schema (equivalent to Replacement over Z). Preserve the statement as a key metatheoretic result; compress philosophical discussion.
- **Content Directives**:
  - Formal items to preserve: thm[reflectionschema] (Reflection Schema -- OL-ONLY, statement only)
  - Formal items to drop: none
  - Prose: compress to intro + theorem statement + 1-sentence remark on Montague-Levy equivalence
  - Examples: cut all
  - Proofs: cut (proof is in refproofs appendix)

---

### sth/replacement/refproofs -- Appendix: Results surrounding Replacement
- **Action**: CONDENSE
- **Lean Chapter**: CH-SET
- **Lean Section**: SET.5: Advanced Topics
- **Rationale**: STEPPING-STONE. Most advanced mathematics in the textbook: proves Reflection in ZF and Replacement from Weak-Reflection. Preserve key theorem statements; compress lengthy proofs to sketches.
- **Content Directives**:
  - Formal items to preserve: thm[thm:replacement] (Weak-Reflection implies Replacement over Z -- OL-ONLY, statement)
  - Formal items to drop: lem[lemreflection] (OL-ONLY, technical), defish[Weak-Reflection] (OL-ONLY, preserve as remark), lem[lem:reflect] (OL-ONLY, technical)
  - Prose: compress to intro + key theorem statement
  - Examples: cut all
  - Proofs: preserve sketch only for Reflection proof; cut detailed verification

---

### sth/replacement/finiteaxiomatizability -- Appendix: Finite axiomatizability
- **Action**: CONDENSE
- **Lean Chapter**: CH-SET
- **Lean Section**: SET.5: Advanced Topics
- **Rationale**: STEPPING-STONE. Proves ZF is not finitely axiomatizable (Montague). Notable metatheoretic result. Preserve statement; compress proof.
- **Content Directives**:
  - Formal items to preserve: thm[zfnotfinitely] (ZF is not finitely axiomatizable -- OL-ONLY, statement)
  - Formal items to drop: prop[finiteextensionofZ] (OL-ONLY, consequence)
  - Prose: compress to statement + 1-paragraph proof sketch
  - Examples: cut all
  - Proofs: preserve sketch only

---

## Chapter 6: ord-arithmetic/ -- Ordinal Arithmetic

### sth/ord-arithmetic/intro -- Introduction
- **Action**: CUT
- **Lean Chapter**: CH-SET
- **Lean Section**: N/A
- **Rationale**: PEDAGOGICAL. Brief motivational introduction. No formal content.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: none (no formal items)
  - Prose: N/A
  - Examples: N/A
  - Proofs: N/A

---

### sth/ord-arithmetic/add -- Ordinal Addition
- **Action**: CONDENSE
- **Lean Chapter**: CH-SET
- **Lean Section**: SET.5: Advanced Topics (Ordinal Arithmetic)
- **Rationale**: STEPPING-STONE. Defines ordinal addition. OL-ONLY items but needed for the ordinal arithmetic development that supports cardinal theory. Preserve definition and recursion equations; compress verification proofs.
- **Content Directives**:
  - Formal items to preserve: defn[defordplus] (ordinal addition -- OL-ONLY), lem[ordadditionrecursion] (recursion equations -- statement), prop[ordsumnotcommute] (non-commutativity -- statement)
  - Formal items to drop: defn[defdissum] (disjoint sum -- OL-ONLY, auxiliary), defn (reverse lexicographic ordering -- OL-ONLY, auxiliary), lem[ordsumlessiswo] (OL-ONLY, technical), lem[ordinaladditionisnice] (OL-ONLY, compress to statement)
  - Prose: compress to intro + definition + recursion equations + non-commutativity remark
  - Examples: keep 1 (1+omega = omega vs omega+1)
  - Proofs: cut all (preserve statements only)

---

### sth/ord-arithmetic/using-addition -- Using Ordinal Addition
- **Action**: CONDENSE
- **Lean Chapter**: CH-SET
- **Lean Section**: SET.5: Advanced Topics
- **Rationale**: STEPPING-STONE. Rank computations and characterizations of infinite ordinals. The 5 equivalent characterizations of infinite ordinals (lem[ordinfinitycharacter]) are referenced by cardinal development.
- **Content Directives**:
  - Formal items to preserve: lem[ordinfinitycharacter] (5 equivalent characterizations of infinite ordinals -- statement)
  - Formal items to drop: lem[rankcomputation] (OL-ONLY, technical rank computations)
  - Prose: compress to statement of ordinfinitycharacter + brief context
  - Examples: cut all
  - Proofs: preserve sketch only for ordinfinitycharacter

---

### sth/ord-arithmetic/mult -- Ordinal Multiplication
- **Action**: CONDENSE
- **Lean Chapter**: CH-SET
- **Lean Section**: SET.5: Advanced Topics (Ordinal Arithmetic)
- **Rationale**: STEPPING-STONE. Defines ordinal multiplication. Compress to definition + recursion equations + non-commutativity.
- **Content Directives**:
  - Formal items to preserve: defn (ordinal multiplication -- OL-ONLY), lem[ordtimesrecursion] (recursion equations -- statement), prop (non-commutativity -- statement)
  - Formal items to drop: lem[ordtimeslessiswo] (OL-ONLY, technical), lem[ordinalmultiplicationisnice] (OL-ONLY, compress to statement)
  - Prose: compress to intro + definition + recursion equations + non-commutativity remark
  - Examples: keep 1 (2*omega = omega vs omega*2)
  - Proofs: cut all

---

### sth/ord-arithmetic/expo -- Ordinal Exponentiation
- **Action**: CONDENSE
- **Lean Chapter**: CH-SET
- **Lean Section**: SET.5: Advanced Topics (Ordinal Arithmetic)
- **Rationale**: STEPPING-STONE. Defines ordinal exponentiation by transfinite recursion. Compress to definition only.
- **Content Directives**:
  - Formal items to preserve: defn[ordexporecursion] (ordinal exponentiation -- OL-ONLY)
  - Formal items to drop: none
  - Prose: compress to definition + 1-sentence remark on non-commutativity (2^omega = omega vs omega^2)
  - Examples: keep 1 (2^omega = omega)
  - Proofs: N/A

---

## Chapter 7: cardinals/ -- Cardinals

### sth/cardinals/cp -- Cantor's Principle
- **Action**: CONDENSE
- **Lean Chapter**: CH-SET
- **Lean Section**: SET.4: Cardinals
- **Rationale**: STEPPING-STONE. Motivates cardinal notion via Cantor's Principle. The SECTION-MAP lists this as introducing DEF-SET008 (motivation), but the formal definition is in cardsasords. Compress to the statement of Cantor's Principle as a desideratum for the cardinal definition.
- **Content Directives**:
  - Formal items to preserve: (Cantor's Principle stated informally -- preserve as motivating remark)
  - Formal items to drop: none
  - Prose: compress to 1 paragraph stating Cantor's Principle: |A| = |B| iff A equinumerous B
  - Examples: cut all
  - Proofs: N/A

---

### sth/cardinals/cardsasords -- Cardinals as Ordinals
- **Action**: ABSORB:{sth/cardinals/cp motivation}
- **Lean Chapter**: CH-SET
- **Lean Section**: SET.4: Cardinals
- **Rationale**: CORE-DEF. Authoritative introduction of DEF-SET008 (Cardinal Number as least ordinal equinumerous to A). Also introduces AX-SET009 (Well-Ordering axiom). This is the primary section for both DEF-SET008 and AX-SET009 (first occurrence). The Well-Ordering axiom is later shown equivalent to Choice in sth/choice/woproblem. Absorbs motivation from cp.
- **Content Directives**:
  - Formal items to preserve: defn[defcardinalasordinal] (DEF-SET008), axiom[Well-Ordering] (AX-SET009), lem[lem:CardinalsExist], lem[lem:CardinalsBehaveRight] (Cantor's Principle verified)
  - Formal items to drop: proof (re-proof of Schroder-Bernstein) (OL-ONLY, redundant with sfr/)
  - Prose: preserve (directly supports cardinal definition)
  - Examples: preserve
  - Proofs: preserve full for CardinalsExist and CardinalsBehaveRight; cut Schroder-Bernstein re-proof

---

### sth/cardinals/zfc -- ZFC: A Milestone
- **Action**: CONDENSE
- **Lean Chapter**: CH-SET
- **Lean Section**: SET.2: ZFC Axioms (final remark)
- **Rationale**: STEPPING-STONE. Final milestone: ZFC = ZF + Well-Ordering = ZF + Choice. Compress to 2-sentence remark at end of SET.2.
- **Content Directives**:
  - Formal items to preserve: defn (ZFC = ZF + Well-Ordering) as inline remark (OL-ONLY)
  - Formal items to drop: none
  - Prose: compress to 2-sentence remark defining ZFC and noting equivalence of Well-Ordering and Choice
  - Examples: cut all
  - Proofs: N/A

---

### sth/cardinals/classing -- Finite, Enumerable, Nonenumerable
- **Action**: CONDENSE
- **Lean Chapter**: CH-SET
- **Lean Section**: SET.4: Cardinals
- **Rationale**: STEPPING-STONE. Classifies cardinals as finite/infinite. Key results: omega is least infinite cardinal, no largest cardinal (via THM-SET002/Cantor's Theorem reference). Preserve key definitions and results; compress proofs.
- **Content Directives**:
  - Formal items to preserve: defn[defnfinite] (finite/infinite sets), cor[omegaisacardinal] (omega is least infinite cardinal), thm[lem:NoLargestCardinal] (no largest cardinal -- THM-SET002 reference), prop[unioncardinalscardinal] (union of cardinals is cardinal)
  - Formal items to drop: prop[finitecardisoequal] (OL-ONLY), cor[naturalsarecardinals] (OL-ONLY, immediate), thm[generalinfinitycharacter] (OL-ONLY, preserve statement), cor (infinite cardinal = limit ordinal) (OL-ONLY), thm (no set of all cardinals) (OL-ONLY, preserve as 1-line remark)
  - Prose: compress to definitions + key theorems
  - Examples: cut all
  - Proofs: preserve sketch only for NoLargestCardinal; cut others

---

### sth/cardinals/hp -- Appendix: Hume's Principle
- **Action**: CUT
- **Lean Chapter**: CH-SET
- **Lean Section**: N/A
- **Rationale**: TANGENTIAL. Philosophical appendix on Hume's Principle and neo-Fregean logicism. No formal set-theoretic content, no taxonomy items.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: (Hume's Principle -- discussed informally) (OL-ONLY)
  - Prose: N/A
  - Examples: N/A
  - Proofs: N/A

---

## Chapter 8: card-arithmetic/ -- Cardinal Arithmetic

### sth/card-arithmetic/opps -- Defining the Basic Operations
- **Action**: KEEP
- **Lean Chapter**: CH-SET
- **Lean Section**: SET.4: Cardinals (Cardinal Arithmetic)
- **Rationale**: CORE-DEF. Defines cardinal addition, multiplication, exponentiation (OL-ONLY but essential operations). Also proves |P(A)| = 2^|A| and the cardinal Cantor's Theorem (THM-SET002 reference: a < 2^a), and |R| = 2^omega. Key section for cardinal arithmetic.
- **Content Directives**:
  - Formal items to preserve: defn (cardinal addition, multiplication, exponentiation), prop[cardplustimescommute], lem[lem:SizePowerset2Exp] (|P(A)| = 2^|A|), cor[cantorcor] (a < 2^a, THM-SET002 cardinal form), thm[continuumis2aleph0] (|R| = 2^omega)
  - Formal items to drop: none
  - Prose: preserve
  - Examples: preserve
  - Proofs: preserve full

---

### sth/card-arithmetic/simp -- Simplifying Addition and Multiplication
- **Action**: CONDENSE
- **Lean Chapter**: CH-SET
- **Lean Section**: SET.4: Cardinals (Cardinal Arithmetic)
- **Rationale**: STEPPING-STONE. Major simplification: for infinite cardinals, addition and multiplication collapse to max. Key lemma alpha*alpha = alpha for infinite alpha. Preserve key results; compress the canonical ordering proof.
- **Content Directives**:
  - Formal items to preserve: lem[alphatimesalpha] (alpha equinumerous alpha x alpha for infinite alpha -- statement + sketch), thm[cardplustimesmax] (a * b = a + b = max(a,b) for infinite cardinals), prop[kappaunionkappasize] (kappa-union of kappa-size sets has size kappa)
  - Formal items to drop: defn (canonical ordering on pairs of ordinals) (OL-ONLY, auxiliary), prop[simplecardproduct] (OL-ONLY, intermediate)
  - Prose: compress to intro + key theorem statements + sketch of alpha*alpha = alpha
  - Examples: cut all
  - Proofs: preserve sketch only for alphatimesalpha; preserve statement + sketch for cardplustimesmax

---

### sth/card-arithmetic/expotough -- Some Simplification with Cardinal Exponentiation
- **Action**: CONDENSE
- **Lean Chapter**: CH-SET
- **Lean Section**: SET.4: Cardinals (Cardinal Arithmetic)
- **Rationale**: STEPPING-STONE. Partial simplification of cardinal exponentiation. Cannot fully simplify due to CH-related issues. Preserve key results as statements.
- **Content Directives**:
  - Formal items to preserve: prop[simplecardexpo] (exponent laws -- statement), prop[cardexpo2reduct] (a^b = 2^b when 2 <= a <= b, b infinite -- statement)
  - Formal items to drop: prop (a^n = a for infinite a, finite n) (OL-ONLY, compress to remark), prop (a^b = 2^b when...) (OL-ONLY, redundant with cardexpo2reduct)
  - Prose: compress to key results + remark on CH-related limitations
  - Examples: cut all
  - Proofs: cut (preserve statements only)

---

### sth/card-arithmetic/ch -- The Continuum Hypothesis
- **Action**: KEEP
- **Lean Chapter**: CH-SET
- **Lean Section**: SET.5: Advanced Topics
- **Rationale**: CORE-DEF. Authoritative introduction of DEF-SET013 (Aleph Numbers) and DEF-SET015 (Continuum Hypothesis). Defines aleph_alpha and beth_alpha sequences, states CH and GCH, notes independence.
- **Content Directives**:
  - Formal items to preserve: defn (aleph numbers, beth numbers) (DEF-SET013), defish[GCH] (DEF-SET015), defish[CH] (DEF-SET015), prop (every infinite cardinal is an aleph)
  - Formal items to drop: none
  - Prose: preserve (includes essential independence result statements)
  - Examples: preserve
  - Proofs: preserve full for prop (every infinite cardinal is an aleph)

---

### sth/card-arithmetic/fix -- Aleph-Fixed Points
- **Action**: CONDENSE
- **Lean Chapter**: CH-SET
- **Lean Section**: SET.5: Advanced Topics
- **Rationale**: STEPPING-STONE. Illustrates the "height" forced by Replacement via aleph-fixed-points and beth-fixed-points. Preserve key statements; compress proofs and philosophical discussion.
- **Content Directives**:
  - Formal items to preserve: prop[alephfixed] (existence of aleph-fixed-point -- statement), prop[stagesize] (|V_{omega+alpha}| = beth_alpha -- statement)
  - Formal items to drop: prop[bethfixed] (OL-ONLY, similar to alephfixed, mention in remark), cor (exists kappa with |V_kappa| = kappa) (OL-ONLY, consequence)
  - Prose: compress to key statements + 1-paragraph context
  - Examples: cut all
  - Proofs: cut (preserve statements only)

---

## Chapter 9: choice/ -- Choice

### sth/choice/intro -- Introduction
- **Action**: CUT
- **Lean Chapter**: CH-SET
- **Lean Section**: N/A
- **Rationale**: PEDAGOGICAL. Brief introduction to Choice chapter. No formal content.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: none (no formal items)
  - Prose: N/A
  - Examples: N/A
  - Proofs: N/A

---

### sth/choice/tarskiscott -- The Tarski-Scott Trick
- **Action**: CONDENSE
- **Lean Chapter**: CH-SET
- **Lean Section**: SET.4: Cardinals (alternative definition remark)
- **Rationale**: STEPPING-STONE. Shows how to define cardinals without Choice using least-rank representatives. Interesting alternative definition but secondary to the standard (Well-Ordering-based) approach. Compress to brief remark.
- **Content Directives**:
  - Formal items to preserve: defn[Tarski-Scott] (Tarski-Scott trick -- OL-ONLY, statement only)
  - Formal items to drop: defn (TS-cardinality, TS-ordinality) (OL-ONLY, alternative definitions)
  - Prose: compress to 1-paragraph remark on the Tarski-Scott alternative
  - Examples: cut all
  - Proofs: N/A

---

### sth/choice/hartogs -- Comparability and Hartogs' Lemma
- **Action**: CONDENSE
- **Lean Chapter**: CH-SET
- **Lean Section**: SET.6: Theorems (or SET.4: Cardinals supplement)
- **Rationale**: STEPPING-STONE. Proves Hartogs' Lemma (key ingredient for Well-Ordering => Choice proof) and the equivalence of Well-Ordering with Comparability. Preserve key results; compress proofs.
- **Content Directives**:
  - Formal items to preserve: lem[HartogsLemma] (for any set A there is an ordinal not injectable into A), thm (Well-Ordering iff Comparability -- statement)
  - Formal items to drop: none
  - Prose: compress to key theorem statements + brief context
  - Examples: cut all
  - Proofs: preserve sketch only for HartogsLemma; cut proof for equivalence theorem

---

### sth/choice/woproblem -- The Well-Ordering Problem
- **Action**: KEEP
- **Lean Chapter**: CH-SET
- **Lean Section**: SET.6: Theorems
- **Rationale**: CORE-THM. Authoritative proof of THM-SET001 (Well-Ordering and Choice are equivalent). Also defines choice function and Axiom of Choice (AX-SET009 equivalent formulation). Primary section for AX-SET009's Choice formulation and THM-SET001.
- **Content Directives**:
  - Formal items to preserve: defn (choice function, choice function for A), axiom[Choice] (AX-SET009), thm[thmwochoice] (THM-SET001)
  - Formal items to drop: none
  - Prose: preserve
  - Examples: preserve
  - Proofs: preserve full (both directions of the equivalence)

---

### sth/choice/countablechoice -- Countable Choice
- **Action**: CONDENSE
- **Lean Chapter**: CH-SET
- **Lean Section**: SET.5: Advanced Topics (Choice variants)
- **Rationale**: STEPPING-STONE. Discusses Countable Choice as weaker principle. Preserve key results; compress historical discussion and Russell's boots-and-socks example.
- **Content Directives**:
  - Formal items to preserve: defish[Countable Choice] (OL-ONLY, statement), thm (countable union of countable sets is countable -- in Z^- + Countable Choice, statement)
  - Formal items to drop: lem (every finite set has a choice function -- in Z^-) (OL-ONLY, technical), thm (every set is finite or infinite -- in Z^- + Countable Choice) (OL-ONLY, preserve as remark)
  - Prose: compress to definition of Countable Choice + key consequences (2-3 sentences)
  - Examples: cut all (Russell's boots-and-socks is pedagogical)
  - Proofs: cut (preserve statements only)

---

### sth/choice/justifications -- Intrinsic Considerations about Choice
- **Action**: CONDENSE
- **Lean Chapter**: CH-SET
- **Lean Section**: SET.5: Advanced Topics (Choice justification remark)
- **Rationale**: PEDAGOGICAL. Philosophical justification of Choice via StagesAcc. However, it introduces THM-SET003 (Zorn's Lemma as equivalent) by mention. The lean text needs Zorn's Lemma stated somewhere. Compress to: (1) statement of Zorn's Lemma equivalence (THM-SET003), (2) brief justification remark.
- **Content Directives**:
  - Formal items to preserve: thm[choiceset] (Choice iff choice sets -- OL-ONLY, statement), THM-SET003 mention (Zorn's Lemma equivalence -- state formally per domain spec DEF-SET010)
  - Formal items to drop: none
  - Prose: compress to statement of Zorn's Lemma equivalence + 2-sentence justification remark
  - Examples: cut all
  - Proofs: cut (proof left as exercise in OL anyway)

---

### sth/choice/banach -- The Banach-Tarski Paradox
- **Action**: CUT
- **Lean Chapter**: CH-SET
- **Lean Section**: N/A
- **Rationale**: TANGENTIAL. Discussion of Banach-Tarski Paradox as consequence of Choice. Stated but not proved. No taxonomy items.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: thm[Banach-Tarski Paradox] (OL-ONLY, stated not proved)
  - Prose: N/A
  - Examples: N/A
  - Proofs: N/A

---

### sth/choice/vitali -- Appendix: Vitali's Paradox
- **Action**: CUT
- **Lean Chapter**: CH-SET
- **Lean Section**: N/A
- **Rationale**: TANGENTIAL. Detailed proof of Vitali's Paradox and Hausdorff's Paradox. Outside taxonomy scope -- these are applications of Choice in analysis/measure theory, not formal set theory for logic.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: thm[vitaliparadox] (OL-ONLY), lem[rotationsgroupabelian] (OL-ONLY), lem[disjointgroup] (OL-ONLY), lem[vitalicover] (OL-ONLY), lem[vitalinooverlap] (OL-ONLY), lem[pseudobanachtarski] (OL-ONLY), cor[Vitali] (OL-ONLY), thm[Hausdorff's Paradox] (OL-ONLY)
  - Prose: N/A
  - Examples: N/A
  - Proofs: N/A

---

### SET Batch Summary

- **Total sections**: 62
- **Action distribution**:

| Action | Count |
|--------|-------|
| KEEP | 17 |
| CONDENSE | 27 |
| ABSORB | 1 |
| MERGE-INTO | 0 |
| CUT | 17 |
| DISTRIBUTE | 0 |
| **Total** | **62** |

**Per-chapter breakdown**:

| Chapter | Sections | KEEP | CONDENSE | ABSORB | CUT |
|---------|----------|------|----------|--------|-----|
| story/ | 6 | 1 | 0 | 0 | 5 |
| z/ | 9 | 5 | 3 | 0 | 1 |
| ordinals/ | 10 | 6 | 2 | 0 | 2 |
| spine/ | 6 | 2 | 4 | 0 | 0 |
| replacement/ | 8 | 0 | 4 | 0 | 4 |
| ord-arithmetic/ | 5 | 0 | 4 | 0 | 1 |
| cardinals/ | 5 | 0 | 3 | 1 | 1 |
| card-arithmetic/ | 5 | 2 | 3 | 0 | 0 |
| choice/ | 8 | 1 | 4 | 0 | 3 |
| **Total** | **62** | **17** | **27** | **1** | **17** |

- **Taxonomy coverage**: All SET taxonomy items (3 PRIM + 15 DEF + 9 AX + 3 THM) have authoritative homes:

| ID | Concept | Authoritative Section | Action |
|----|---------|----------------------|--------|
| PRIM-SET001 | Set (formal) | SET.1 opening | FORMALIZE (per A4) |
| PRIM-SET002 | Membership (formal) | sth/story/extensionality | KEEP (implicit in AX-SET001) |
| PRIM-SET003 | Class (informal) | sth/ordinals/basic | KEEP (via Burali-Forti) |
| AX-SET001 | Extensionality | sth/story/extensionality | KEEP |
| AX-SET002 | Empty Set | sth/z/sep | KEEP (derived) |
| AX-SET003 | Pairing | sth/z/pairs | KEEP |
| AX-SET004 | Union | sth/z/union | KEEP |
| AX-SET005 | Power Set | sth/z/power | KEEP |
| AX-SET006 | Separation | sth/z/sep | KEEP |
| AX-SET007 | Replacement | sth/ordinals/replacement | KEEP |
| AX-SET008 | Foundation | sth/spine/foundation | CONDENSE (axiom preserved) |
| AX-SET009 | Choice/Well-Ordering | sth/choice/woproblem (Choice); sth/cardinals/cardsasords (WO) | KEEP; ABSORB |
| DEF-SET001 | Ordinal | sth/ordinals/vn | KEEP |
| DEF-SET002 | Transitive Set | sth/ordinals/vn | KEEP |
| DEF-SET003 | Von Neumann Ordinal | sth/ordinals/vn | KEEP |
| DEF-SET004 | Successor Ordinal | sth/ordinals/opps | KEEP |
| DEF-SET005 | Limit Ordinal | sth/ordinals/opps | KEEP |
| DEF-SET006 | Transfinite Induction | sth/ordinals/basic | KEEP |
| DEF-SET007 | Transfinite Recursion | sth/spine/recursion | KEEP |
| DEF-SET008 | Cardinal Number | sth/cardinals/cardsasords | ABSORB |
| DEF-SET009 | Well-Ordering | sth/ordinals/wo | KEEP |
| DEF-SET010 | Zorn's Lemma | sth/choice/justifications | CONDENSE |
| DEF-SET011 | Cantor's Theorem (formal) | sth/card-arithmetic/opps | KEEP |
| DEF-SET012 | Von Neumann Hierarchy | sth/spine/valpha | KEEP |
| DEF-SET013 | Aleph Numbers | sth/card-arithmetic/ch | KEEP |
| DEF-SET014 | Cofinality | (no OL section) | DEFER (deferred, per domain spec) |
| DEF-SET015 | Continuum Hypothesis | sth/card-arithmetic/ch | KEEP |
| THM-SET001 | WO iff Zorn iff AC | sth/choice/woproblem | KEEP |
| THM-SET002 | Transfinite Recursion Thm | sth/spine/recursion | KEEP |
| THM-SET003 | Cantor's Thm (in ZFC) | sth/card-arithmetic/opps | KEEP |

- **Compression targets resolved**:
  - **AX-SET009** (Choice, 2 sections): Primary = sth/choice/woproblem (KEEP, proves equivalence THM-SET001). Secondary = sth/cardinals/cardsasords (ABSORB, introduces Well-Ordering axiom first). Both preserved: cardsasords defines Well-Ordering as axiom for cardinal theory; woproblem proves Choice equivalent and is the authoritative proof of THM-SET001.
  - **DEF-SET008** (Cardinal Number, 2 sections): Primary = sth/cardinals/cardsasords (ABSORB, formal definition defn[defcardinalasordinal]). Secondary = sth/cardinals/cp (CONDENSE to motivation paragraph absorbed into cardsasords).

- **Surviving sections**: 17 KEEP + 27 CONDENSE + 1 ABSORB = 45 surviving (out of 62)
- **Sections cut**: 17 (all PEDAGOGICAL or TANGENTIAL with no taxonomy items)
- **Compression ratio**: 27% of sections eliminated entirely; effective content volume reduction significantly higher due to 27 CONDENSE entries compressing prose, examples, and proofs
- **Estimated page count**: ~40-50 pages for CH-SET in the lean text (17 full sections + 27 condensed sections + 1 absorbed)

## CH-MOD (feeds into CH-META and CH-SEM)

### mod/bas/red -- Reducts and Expansions
- **Action**: CONDENSE
- **Lean Chapter**: CH-SEM
- **Lean Section**: SEM.6: Model-Theoretic Concepts
- **Rationale**: STEPPING-STONE. Introduces reduct/expansion notation (SUPPORT-DEF) used heavily by interpolation (Expan{M}{R} notation) and substructure definitions. No taxonomy items introduced, but structurally necessary for DEF-SEM011 and CP-011/CP-012.
- **Content Directives**:
  - Formal items to preserve: defn[defn:reduct] (reduct/expansion definition), defn (Expan{M}{R} notation)
  - Formal items to drop: prop[prop:reduct] -- stepping stone; statement can be preserved as a one-line remark, proof cut (exercise in OL)
  - Prose: compress to intro+definition only
  - Examples: cut all
  - Proofs: cut (prop:reduct proof is an exercise)

---

### mod/bas/sub -- Substructures
- **Action**: KEEP
- **Lean Chapter**: CH-SEM
- **Lean Section**: SEM.6: Model-Theoretic Concepts
- **Rationale**: CORE-DEF. Defining occurrence of DEF-SEM011 (Substructure). Note: SECTION-MAP identifies this as DEF-SEM011 but the taxonomy spec DOMAIN-SEMANTICS.md uses PRIM-SEM013 for Substructure. The SECTION-MAP maps defn[defn:substructure] to DEF-SEM011. We follow the SECTION-MAP: this is the authoritative home for the substructure definition regardless of ID numbering. Short section, minimal editing needed.
- **Content Directives**:
  - Formal items to preserve: defn[defn:substructure] (DEF-SEM011 / PRIM-SEM013 -- substructure definition)
  - Formal items to drop: none
  - Prose: preserve (brief and on-point)
  - Examples: preserve rem[rem:substructure] -- relational substructure simplification used by Lindstrom chapter
  - Proofs: N/A

---

### mod/bas/ove -- Overspill
- **Action**: CONDENSE
- **Lean Chapter**: CH-SEM
- **Lean Section**: SEM.7: Theorems (as application of compactness)
- **Rationale**: STEPPING-STONE. The overspill theorem and the non-expressibility of finiteness in FOL are classic compactness applications. The finiteness result (prop[inf-not-fo]) is significant for CP-013 context (FOL expressiveness limits). No taxonomy items introduced, but both results merit preservation as compact statements.
- **Content Directives**:
  - Formal items to preserve: thm[overspill] (overspill theorem), prop[inf-not-fo] (finiteness not FO-expressible)
  - Formal items to drop: none
  - Prose: compress to intro+definition only (one sentence motivation)
  - Examples: cut all
  - Proofs: preserve sketch only for thm[overspill] (compactness argument in 2 sentences); preserve full for prop[inf-not-fo] (already a 3-line proof)

---

### mod/bas/iso -- Isomorphic Structures
- **Action**: KEEP
- **Lean Chapter**: CH-SEM
- **Lean Section**: SEM.6: Model-Theoretic Concepts
- **Rationale**: CORE-DEF. Defining occurrence of PRIM-SEM013 (Elementary Equivalence, mapped as defn[defn:elem-equiv]), DEF-SEM013 (Isomorphism of Structures, mapped as defn[defn:isomorphism]), and THM-SEM001 (Isomorphism Lemma, mapped as thm[thm:isom]). Three taxonomy items introduced in one section -- all are authoritative. Critical section referenced throughout model theory.
- **Content Directives**:
  - Formal items to preserve: defn[defn:elem-equiv] (PRIM-SEM013 / DEF-SEM008), defn[defn:isomorphism] (DEF-SEM013 / PRIM-SEM012), thm[thm:isom] (THM-SEM001), defn (automorphism) -- useful SUPPORT-DEF
  - Formal items to drop: none
  - Prose: preserve (introductory paragraph motivating the distinction between elementary equivalence and isomorphism is pedagogically tight)
  - Examples: cut all (no examples in section, only exercises)
  - Proofs: preserve full for thm[thm:isom] (the term-valuation part (a) is given; part (b) is an exercise -- preserve part (a), note part (b) as exercise)

---

### mod/bas/thm -- The Theory of a Structure
- **Action**: KEEP
- **Lean Chapter**: CH-SEM
- **Lean Section**: SEM.6: Model-Theoretic Concepts
- **Rationale**: CORE-DEF. Defining occurrence of PRIM-SEM012 (Theory of a Structure, Th(M)). Note: The taxonomy DOMAIN-SEMANTICS.md uses DEF-SEM006 for "Theory of a Structure" while the SECTION-MAP uses PRIM-SEM012. We follow the SECTION-MAP entry. This is the authoritative home for the Th(M) definition. Also establishes that Th(M) is complete and connects elementary equivalence to Th(M).
- **Content Directives**:
  - Formal items to preserve: defn (Theory of M, Th(M)) -- PRIM-SEM012 / DEF-SEM006, prop (Th(M) is complete), prop[prop:equiv] (models of Th(M) are elementarily equivalent)
  - Formal items to drop: none
  - Prose: preserve
  - Examples: keep rem[remark:R] (Lowenheim-Skolem counterexample showing iso is strictly stronger than elem-equiv -- canonical example, referenced by mod/bas/dlo)
  - Proofs: preserve full (all proofs are 2-4 lines)

---

### mod/bas/pis -- Partial Isomorphisms
- **Action**: CONDENSE
- **Lean Chapter**: CH-META
- **Lean Section**: META.11: Lindstrom's Theorem (technical infrastructure)
- **Rationale**: STEPPING-STONE for Lindstrom's theorem. Heavy section developing the back-and-forth method, Ehrenfeucht-Fraisse games (I_n relations), quantifier rank, and n-equivalence. None are taxonomy items, but all are essential infrastructure for CP-013. The back-and-forth results (thm:p-isom1, thm:p-isom2, thm:b-n-f) are used directly in the Lindstrom proof chain. Condense by preserving all key definitions and theorem statements but compressing proofs.
- **Content Directives**:
  - Formal items to preserve: defn (partial isomorphism), defn[defn:partialisom] (partial isomorphism with back-and-forth), thm[thm:p-isom1] (enumerable partially iso structures are iso), thm[thm:p-isom2] (partial iso implies elem equiv for relational languages), defn (quantifier rank, n-equivalence), prop[prop:qr-finite] (finitely many sentences per quantifier rank), defn (I_n relations), defn (approx_n), thm[thm:b-n-f] (I_n and n-equivalence connection), cor[cor:b-n-f]
  - Formal items to drop: rem (function case for thm:p-isom2) -- one-sentence remark, can be inlined as a note
  - Prose: compress to intro+definition only; cut the connecting narrative between definitions
  - Examples: cut all
  - Proofs: preserve sketch only for thm[thm:p-isom1] (back-and-forth construction outline in 3 sentences); preserve sketch only for thm[thm:p-isom2] (induction sketch in 2 sentences); cut proof of prop[prop:qr-finite] (stated as "by induction on n" in OL); preserve sketch only for thm[thm:b-n-f] (forward direction easy induction; converse uses prop:qr-finite -- 4-sentence sketch)

---

### mod/bas/dlo -- Dense Linear Orders
- **Action**: KEEP
- **Lean Chapter**: CH-SEM
- **Lean Section**: SEM.6: Model-Theoretic Concepts
- **Rationale**: CORE-THM. Demonstrates DEF-SEM006 / DEF-SEM014 (Categoricity) via the canonical example: Cantor's theorem on aleph-0 categoricity of DLO (thm[thm:cantorQ]). This is the defining exemplification of categoricity in OL. The proof applies the back-and-forth method. GAP: An explicit formal definition of "kappa-categorical" should be added by Phase 4 (from DOMAIN-SEMANTICS DEF-SEM014) before this theorem.
- **Content Directives**:
  - Formal items to preserve: defn (DLO axioms), thm[thm:cantorQ] (Cantor's theorem: aleph-0 categoricity of DLO)
  - Formal items to drop: none
  - Prose: preserve (tight)
  - Examples: keep rem (R elementarily equivalent to Q) -- directly illustrates the theorem and connects to mod/bas/thm remark:R
  - Proofs: preserve full for thm[thm:cantorQ] (clean back-and-forth proof, canonical example of the technique)

---

### mod/bas/nsa -- Non-standard Models of Arithmetic (COMMENTED OUT)
- **Action**: CUT
- **Lean Chapter**: N/A
- **Lean Section**: N/A
- **Rationale**: PEDAGOGICAL. Section is commented out in basics.tex (line 24: `%\olimport{nonstandard-arithmetic}`). Content substantially overlaps with mod/mar/nst (non-standard models via compactness) and mod/mar/mpa (block structure analysis). The standard model/true arithmetic definitions duplicate mod/mar/int and mod/mar/stm. The existence proof for non-standard models is the same compactness argument in mod/mar/nst. The block analysis (items 1-13) is reproduced with more detail in mod/mar/mpa.
- **Content Directives**:
  - Formal items to preserve: none (all subsumed by mod/mar/*)
  - Formal items to drop: all -- defn (standard model, true arithmetic) subsumed by mod/mar/stm; defn (standard/non-standard structure) subsumed by mod/mar/nst; thm[thm:non-std] subsumed by mod/mar/nst; block analysis (items 1-13) subsumed by mod/mar/mpa
  - Prose: cut entirely
  - Examples: cut all
  - Proofs: cut all

---

### mod/mar/int -- Introduction (Models of Arithmetic)
- **Action**: CUT
- **Lean Chapter**: N/A
- **Lean Section**: N/A
- **Rationale**: PEDAGOGICAL. Narrative introduction with no labeled formal environments. Motivational paragraph connecting non-standard models to incompleteness phenomena (Con(PA) and its negation). The content about non-standard witnesses for Con(PA) is interesting but tangential -- it is better placed as a remark in the incompleteness chapter (CH-META, META.6) rather than in the model theory feed. No taxonomy items introduced.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: none (no formal items)
  - Prose: cut entirely (motivational only)
  - Examples: cut all
  - Proofs: N/A

---

### mod/mar/stm -- Standard Models of Arithmetic
- **Action**: CONDENSE
- **Lean Chapter**: CH-SEM
- **Lean Section**: SEM.5: Arithmetic Models
- **Rationale**: STEPPING-STONE. Establishes the technical notion of "standard structure" (isomorphic to N) and proves key stepping-stone results: domain = values of standard numerals, model of Q with only standard elements is standard, uniqueness of isomorphism. These support the non-standard model existence proof in mod/mar/nst. No taxonomy items introduced (these are SUPPORT-DEFs), but they are needed by the mod/mar chain.
- **Content Directives**:
  - Formal items to preserve: defn (standard structure = isomorphic to N), prop[prop:standard-domain] (domain equals numeral values), prop[prop:thq-standard] (model of Q with only standard elements is standard)
  - Formal items to drop: prop[prop:thq-unique-iso] (uniqueness of isomorphism -- stepping stone not needed downstream)
  - Prose: compress to intro+definition only
  - Examples: cut all (explain blocks cut)
  - Proofs: preserve sketch only for prop[prop:standard-domain] (surjectivity from isomorphism, 2 sentences); preserve sketch only for prop[prop:thq-standard] (injectivity via Q provability, 3 sentences)

---

### mod/mar/nst -- Non-Standard Models
- **Action**: KEEP
- **Lean Chapter**: CH-SEM
- **Lean Section**: SEM.5: Arithmetic Models
- **Rationale**: CORE-THM. Contains the canonical compactness-based existence proof for non-standard models of true arithmetic (TA). This is a fundamental application of CP-003 (Compactness). The existence of non-standard models is prerequisite for the structural analysis in mod/mar/mpa and connects to Tennenbaum's theorem in mod/mar/cmp. The proof is clean and self-contained.
- **Content Directives**:
  - Formal items to preserve: defn (non-standard structure, non-standard numbers), prop (non-standard element implies non-standard structure), prop (TA has enumerable non-standard model -- existence proof)
  - Formal items to drop: none
  - Prose: preserve
  - Examples: keep explain block (Z as trivial non-standard structure for LA, showing it is not a model of arithmetic -- simple motivating example)
  - Proofs: preserve full (compactness argument is the canonical application)

---

### mod/mar/mdq -- Models of Q
- **Action**: CUT
- **Lean Chapter**: N/A
- **Lean Section**: N/A
- **Rationale**: PEDAGOGICAL. Purely pedagogical section constructing explicit models K and L of Robinson arithmetic Q. Demonstrates Q is weak enough to have simple non-standard models (successor-fixed-point) and that Q does not prove commutativity of addition. While illustrative, no taxonomy items are introduced, and the content is not needed by any downstream proof chain. The lean text's coverage of non-standard models (mod/mar/nst, mod/mar/mpa) focuses on TA/PA, where Q-specific models are not relevant.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: ex[ex:model-K-of-Q] (pedagogical), ex[ex:model-L-of-Q] (pedagogical) -- both are detailed constructions with no downstream dependencies
  - Prose: cut entirely
  - Examples: cut all
  - Proofs: N/A (no theorems)

---

### mod/mar/mpa -- Models of PA
- **Action**: CONDENSE
- **Lean Chapter**: CH-SEM
- **Lean Section**: SEM.5: Arithmetic Models
- **Rationale**: STEPPING-STONE. Detailed structural analysis of non-standard models of PA, culminating in the result that non-standard blocks are ordered like the rationals (omega + Q*Z structure). This is a rich structural analysis that deeply applies categoricity (DLO) and elementary equivalence. No taxonomy items introduced, but the block structure result is a significant model-theoretic fact. Condense by preserving key propositions (discrete ordering, block definition, density of blocks) while cutting detailed verification steps.
- **Content Directives**:
  - Formal items to preserve: prop (nsless is linear strict order), prop[prop:M-discrete] (0 least, successor immediate, predecessor exists), prop (standard less than nonstandard), prop (block of x -- definition), prop[prop:blocks-dense] (blocks are dense)
  - Formal items to drop: cor (disjoint blocks) -- immediate consequence; prop (nonstandard addition leaves block) -- stepping stone for density; prop (no least nonstandard block) -- can be stated as remark; prop (no largest block) -- can be stated as remark
  - Prose: compress to intro+definition only; preserve the concluding explain block summarizing omega+Q*Z structure (key result statement)
  - Examples: cut all
  - Proofs: preserve sketch only for prop[prop:M-discrete] (exercise in OL; note "follows from PA-provable sentences"); preserve sketch only for prop[prop:blocks-dense] (divisibility-by-2 argument in 3 sentences); cut remaining proofs (stepping-stone verifications)

---

### mod/mar/cmp -- Computable Models of Arithmetic
- **Action**: CONDENSE
- **Lean Chapter**: CH-SEM
- **Lean Section**: SEM.5: Arithmetic Models
- **Rationale**: CORE-THM (Tennenbaum's theorem statement). Introduces the notion of computable model (SUPPORT-DEF) and states Tennenbaum's theorem (N is the only computable model of PA) without proof. The theorem connects model theory to computability and is a significant structural result. However, no proof is given in OL, so the section is already minimal. Condense by cutting the pedagogical example (K' computable model of Q) and preserving the definition and theorem statement.
- **Content Directives**:
  - Formal items to preserve: defn (computable structure), thm (Tennenbaum's Theorem -- statement only, no proof in OL)
  - Formal items to drop: ex[ex:comp-model-q] (pedagogical -- explicit construction of computable K' isomorphic to model K of Q; depends on cut section mod/mar/mdq)
  - Prose: compress to intro+definition only (2 sentences motivating computable models + definition + theorem)
  - Examples: cut ex[ex:comp-model-q]
  - Proofs: N/A (Tennenbaum stated without proof)

---

### mod/int/int -- Introduction (Interpolation)
- **Action**: CUT
- **Lean Chapter**: N/A
- **Lean Section**: N/A
- **Rationale**: PEDAGOGICAL. Brief motivational paragraph (6 sentences) stating the interpolation theorem informally and previewing Beth definability and Robinson joint consistency. No formal items. The lean text's META.9 section will have its own brief introduction.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: none (no formal items)
  - Prose: cut entirely
  - Examples: cut all
  - Proofs: N/A

---

### mod/int/sep -- Separation of Sentences
- **Action**: CONDENSE
- **Lean Chapter**: CH-META
- **Lean Section**: META.9: Craig Interpolation (technical infrastructure)
- **Rationale**: STEPPING-STONE. Introduces the dual formulation of interpolation (separation/inseparability) and proves two key lemmas (lem:sep1 on constant expansion preserving inseparability, lem:sep2 on witnessing preserving inseparability) used directly in the interpolation proof (mod/int/prf). Essential technical machinery. Condense by preserving all formal items but compressing the prose and the diagram.
- **Content Directives**:
  - Formal items to preserve: defn (separation, inseparability), lem[lem:sep1] (inseparability preserved under constant expansion), lem[lem:sep2] (inseparability preserved under witnessing)
  - Formal items to drop: none
  - Prose: compress to intro+definition only (drop the figure; keep 2-sentence motivation connecting separation to interpolation)
  - Examples: cut all (drop figure fig:sep)
  - Proofs: preserve full for lem[lem:sep1] (compactness + generalization argument, essential for interpolation proof); preserve full for lem[lem:sep2] (two-case argument, essential for interpolation proof)

---

### mod/int/prf -- Craig's Interpolation Theorem
- **Action**: KEEP
- **Lean Chapter**: CH-META
- **Lean Section**: META.9: Craig Interpolation
- **Rationale**: CORE-THM. Defining occurrence of CP-011 (Craig's Interpolation Theorem). Full proof via the inseparability/maximally consistent pair construction. The proof uses compactness (CP-003) and completeness (CP-002). This is one of the 13 composition patterns and must be preserved in full.
- **Content Directives**:
  - Formal items to preserve: thm[thm:interpol] (CP-011 -- Craig's Interpolation Theorem, full statement + proof)
  - Formal items to drop: none
  - Prose: preserve
  - Examples: cut all (none present)
  - Proofs: preserve full (the complete proof is the core content; it is the defining occurrence of CP-011)

---

### mod/int/def -- The Definability Theorem
- **Action**: KEEP
- **Lean Chapter**: CH-META
- **Lean Section**: META.10: Beth Definability
- **Rationale**: CORE-THM. Defining occurrence of CP-012 (Beth's Definability Theorem). Full proof as a consequence of Craig's Interpolation Theorem (CP-011). Also introduces the formal notions of explicit and implicit definability (SUPPORT-DEFs needed for the theorem statement). Must be preserved in full.
- **Content Directives**:
  - Formal items to preserve: defn (explicit definition of P), defn (implicit definition of P), thm (Beth Definability Theorem -- CP-012, full statement + proof)
  - Formal items to drop: none
  - Prose: preserve (the motivating paragraph connecting implicit to explicit definability is essential context)
  - Examples: cut all (none present beyond the in-proof notation)
  - Proofs: preserve full (the proof via Craig interpolation is the core content; it is the defining occurrence of CP-012)

---

### mod/lin/int -- Introduction (Lindstrom)
- **Action**: CUT
- **Lean Chapter**: N/A
- **Lean Section**: N/A
- **Rationale**: PEDAGOGICAL. Single motivational paragraph (4 sentences) stating the goal of characterizing FOL as maximal logic with compactness + downward Lowenheim-Skolem. No formal items. The lean text's META.11 section will have its own brief introduction.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: none (no formal items)
  - Prose: cut entirely
  - Examples: cut all
  - Proofs: N/A

---

### mod/lin/alg -- Abstract Logics
- **Action**: MERGE-INTO:mod/lin/prf
- **Lean Chapter**: CH-META
- **Lean Section**: META.11: Lindstrom's Theorem
- **Rationale**: STEPPING-STONE. Introduces the framework of abstract logics (4 definitions: abstract logic, Mod/elementary equivalence in L, normal abstract logic with 7 properties, expressiveness comparison) needed for Lindstrom's theorem statement. These are SUPPORT-DEFs for CP-013 -- none are standalone taxonomy items. The definitions are compact and should be absorbed into the Lindstrom section (mod/lin/prf) as preliminary definitions, since they serve no purpose outside the Lindstrom proof. The remark that FOL is normal is a useful sanity check to preserve.
- **Content Directives**:
  - Formal items surviving in merge target (mod/lin/prf): defn (abstract logic), defn (Mod(L), elementary equivalence in L), defn (normal abstract logic, 7 properties), defn (at least as expressive, equivalent logics)
  - Formal items to drop: rem (first-order logic is normal) -- can be compressed to a one-line note after the normal logic definition
  - Prose: compress to definitions only (cut the explanatory paragraph about infinitary logics)
  - Examples: cut all
  - Proofs: N/A (no proofs)

---

### mod/lin/lsp -- Compactness and Lowenheim-Skolem Properties
- **Action**: MERGE-INTO:mod/lin/prf
- **Lean Chapter**: CH-META
- **Lean Section**: META.11: Lindstrom's Theorem
- **Rationale**: STEPPING-STONE. Defines the Compactness Property and Downward Lowenheim-Skolem Property for abstract logics, and proves the key theorem (thm:abstract-p-isom) that partially isomorphic structures are L-equivalent under the LS property. All three items are essential infrastructure for the Lindstrom proof but have no standalone role outside CP-013. Merge into mod/lin/prf to create a single self-contained Lindstrom section.
- **Content Directives**:
  - Formal items surviving in merge target (mod/lin/prf): defn (Compactness Property for abstract logics), defn (Downward LS property), thm[thm:abstract-p-isom] (partially isomorphic structures are L-equivalent under LS)
  - Formal items to drop: none
  - Prose: compress connecting text to 2 sentences motivating the generalization from FOL to abstract logics
  - Examples: cut all
  - Proofs: preserve sketch only for thm[thm:abstract-p-isom] (construction of combined structure M with internal partial isomorphism, appeal to LS property for countable model, then isomorphism by thm:p-isom1 -- 5-sentence sketch)

---

### mod/lin/prf -- Lindstrom's Theorem
- **Action**: ABSORB:mod/lin/alg,mod/lin/lsp
- **Lean Chapter**: CH-META
- **Lean Section**: META.11: Lindstrom's Theorem
- **Rationale**: CORE-THM. Defining occurrence of CP-013 (Lindstrom's Theorem). Full proof using compactness to obtain a non-standard element in an ordering encoding I_n relations, then deriving a partial isomorphism contradicting the separation hypothesis. Absorbs the abstract logic framework (mod/lin/alg) and the abstract LS/compactness property definitions (mod/lin/lsp) to create a single self-contained section.
- **Content Directives**:
  - Formal items to preserve: lem[lem:lindstrom] (n-equivalence invariance implies FO equivalence), thm[thm:lindstrom] (CP-013 -- Lindstrom's Theorem)
  - Absorbed from mod/lin/alg: defn (abstract logic), defn (Mod(L), elem equiv in L), defn (normal abstract logic), defn (expressiveness comparison)
  - Absorbed from mod/lin/lsp: defn (Compactness Property), defn (LS Property), thm[thm:abstract-p-isom]
  - Formal items to drop: none
  - Prose: preserve for thm[thm:lindstrom]; compress absorbed definitions to minimal introductory text
  - Examples: cut all
  - Proofs: preserve full for lem[lem:lindstrom] (uses prop:qr-finite; compact argument); preserve full for thm[thm:lindstrom] (the defining proof of CP-013; uses compactness for non-standard element, I_n relations, and partial isomorphism contradiction)

---

### MOD Batch Summary
- **Total sections**: 22
- **Action distribution**: 7 KEEP, 7 CONDENSE, 2 MERGE-INTO, 1 ABSORB, 5 CUT
- **Verification**: 7 + 7 + 2 + 1 + 5 = 22 (confirmed)
- **Taxonomy coverage**: All MOD-related taxonomy items have authoritative homes:
  - DEF-SEM011 (Substructure): mod/bas/sub (KEEP)
  - DEF-SEM013 / PRIM-SEM012 (Isomorphism): mod/bas/iso (KEEP)
  - PRIM-SEM013 / DEF-SEM008 (Elementary Equivalence): mod/bas/iso (KEEP)
  - PRIM-SEM012 / DEF-SEM006 (Theory of a Structure, Th(M)): mod/bas/thm (KEEP)
  - DEF-SEM006 / DEF-SEM014 (Categoricity -- by example): mod/bas/dlo (KEEP)
  - THM-SEM001 (Isomorphism Lemma): mod/bas/iso (KEEP)
  - CP-011 (Craig's Interpolation): mod/int/prf (KEEP)
  - CP-012 (Beth's Definability): mod/int/def (KEEP)
  - CP-013 (Lindstrom's Theorem): mod/lin/prf (ABSORB)
- **Compression targets resolved**:
  - CP-013 (Lindstrom, 2 support sections): mod/lin/alg MERGE-INTO mod/lin/prf; mod/lin/lsp MERGE-INTO mod/lin/prf; primary = mod/lin/prf (ABSORB)
  - mod/bas/nsa (commented out): CUT -- content fully subsumed by mod/mar/{stm,nst,mpa}
- **Lean chapter distribution**:
  - CH-SEM: 10 sections (mod/bas/red, mod/bas/sub, mod/bas/ove, mod/bas/iso, mod/bas/thm, mod/bas/dlo, mod/mar/stm, mod/mar/nst, mod/mar/mpa, mod/mar/cmp)
  - CH-META: 5 sections (mod/bas/pis, mod/int/sep, mod/int/prf, mod/int/def, mod/lin/prf [absorbing mod/lin/alg + mod/lin/lsp])
  - CUT (no lean chapter): 5 sections (mod/bas/nsa, mod/mar/int, mod/mar/mdq, mod/int/int, mod/lin/int)
  - MERGE-INTO (absorbed into mod/lin/prf): 2 sections (mod/lin/alg, mod/lin/lsp)
- **Surviving sections**: 15 (KEEP(7) + CONDENSE(7) + ABSORB(1) = 15 surviving sections. The 2 MERGE-INTO sources are absorbed into the ABSORB target (mod/lin/prf), and 5 CUT sections are removed. Total surviving: 15.)

### ABSENT Items in MOD scope
The following taxonomy items from the model theory supplement are ABSENT from OL's model-theory/ content:
- **PRIM-SEM014** (Elementary Substructure): Not defined in OL. Gap persists.
- **DEF-SEM003** (Semantic Consistency): Defined elsewhere (fol/sem or fol/com).
- **DEF-SEM008** (Decidable Theory): Not formally defined in OL model-theory.
- **DEF-SEM012** (Embedding): Not defined in OL (only isomorphism).
- **DEF-SEM014** (Diagram): Not discussed in OL.
- **DEF-SEM015** (Type): Not discussed in OL.
- **DEF-SEM016** (Omitting Types): Not discussed in OL.

These gaps were identified in Phase 2 SECTION-MAP and will be resolved in Phase 4 via NEW-CONTENT entries written from DOMAIN-SEMANTICS.md definitions, placed in SEM.6: Model-Theoretic Concepts.

### Discrepancies
1. **Taxonomy ID numbering mismatch**: The SECTION-MAP uses different IDs than DOMAIN-SEMANTICS.md for some concepts. Specifically:
   - SECTION-MAP calls the substructure definition "DEF-SEM011" while DOMAIN-SEMANTICS.md has "PRIM-SEM013" for Substructure.
   - SECTION-MAP maps mod/bas/iso's defn[defn:elem-equiv] to "PRIM-SEM013" (Elementary Equivalence) while DOMAIN-SEMANTICS.md uses "DEF-SEM008" for Elementary Equivalence.
   - SECTION-MAP maps mod/bas/thm to "PRIM-SEM012" (Theory of a Structure) while DOMAIN-SEMANTICS.md uses "DEF-SEM006" for Theory of a Structure.
   - SECTION-MAP maps mod/bas/iso's defn[defn:isomorphism] to "DEF-SEM013" (Isomorphism) while DOMAIN-SEMANTICS.md uses "PRIM-SEM012" for Isomorphism.

   **Resolution**: These are Phase 1 vs Phase 2 naming inconsistencies. The concepts themselves are correctly mapped to their authoritative sections. Step 11 (QC) should harmonize the IDs. For this block, both IDs are noted at each entry to ensure traceability.

2. **DEF-SEM006 (Categoricity)**: The SECTION-MAP notes that mod/bas/dlo demonstrates aleph-0 categoricity by example (Cantor's theorem) but never formally defines the concept of kappa-categoricity. DOMAIN-SEMANTICS.md has DEF-SEM014 for Categoricity. Phase 4 should add an explicit formal definition of kappa-categoricity (from DEF-SEM014) before the DLO theorem in the lean text.

## CH-EXT: Extensions (Deferred)

### Topic: Applied Modal Logic (16 sections)

### applied-modal-logic/applied-modal-logic — Applied Modal Logic
- **Action**: DEFER-TO-EXTENSION

### applied-modal-logic/epistemic-logic/bisimulations — Bisimulations
- **Action**: DEFER-TO-EXTENSION

### applied-modal-logic/epistemic-logic/epistemic-logic — Epistemic Logic
- **Action**: DEFER-TO-EXTENSION

### applied-modal-logic/epistemic-logic/introduction — Introduction
- **Action**: DEFER-TO-EXTENSION

### applied-modal-logic/epistemic-logic/language-epistemic-logic — Language Epistemic Logic
- **Action**: DEFER-TO-EXTENSION

### applied-modal-logic/epistemic-logic/properties-accessibility — Properties Accessibility
- **Action**: DEFER-TO-EXTENSION

### applied-modal-logic/epistemic-logic/public-announcement-logic-lang — Public Announcement Logic Lang
- **Action**: DEFER-TO-EXTENSION

### applied-modal-logic/epistemic-logic/public-announcement-logic-semantics — Public Announcement Logic Semantics
- **Action**: DEFER-TO-EXTENSION

### applied-modal-logic/epistemic-logic/relational-models — Relational Models
- **Action**: DEFER-TO-EXTENSION

### applied-modal-logic/epistemic-logic/truth-at-w — Truth At W
- **Action**: DEFER-TO-EXTENSION

### applied-modal-logic/temporal-logic/extra-temporal-operators — Extra Temporal Operators
- **Action**: DEFER-TO-EXTENSION

### applied-modal-logic/temporal-logic/introduction — Introduction
- **Action**: DEFER-TO-EXTENSION

### applied-modal-logic/temporal-logic/possible-histories — Possible Histories
- **Action**: DEFER-TO-EXTENSION

### applied-modal-logic/temporal-logic/properties-accessibility — Properties Accessibility
- **Action**: DEFER-TO-EXTENSION

### applied-modal-logic/temporal-logic/temporal-logic — Temporal Logic
- **Action**: DEFER-TO-EXTENSION

### applied-modal-logic/temporal-logic/temporal-logic-semantics — Temporal Logic Semantics
- **Action**: DEFER-TO-EXTENSION


### Topic: Counterfactuals (13 sections)

### counterfactuals/counterfactuals — Counterfactuals
- **Action**: DEFER-TO-EXTENSION

### counterfactuals/introduction/counterfactuals — Counterfactuals
- **Action**: DEFER-TO-EXTENSION

### counterfactuals/introduction/introduction — Introduction
- **Action**: DEFER-TO-EXTENSION

### counterfactuals/introduction/material-conditional — Material Conditional
- **Action**: DEFER-TO-EXTENSION

### counterfactuals/introduction/paradoxes-material — Paradoxes Material
- **Action**: DEFER-TO-EXTENSION

### counterfactuals/introduction/strict-conditional — Strict Conditional
- **Action**: DEFER-TO-EXTENSION

### counterfactuals/minimal-change-semantics/antecedent-strengthening — Antecedent Strengthening
- **Action**: DEFER-TO-EXTENSION

### counterfactuals/minimal-change-semantics/contraposition — Contraposition
- **Action**: DEFER-TO-EXTENSION

### counterfactuals/minimal-change-semantics/introduction — Introduction
- **Action**: DEFER-TO-EXTENSION

### counterfactuals/minimal-change-semantics/minimal-change-semantics — Minimal Change Semantics
- **Action**: DEFER-TO-EXTENSION

### counterfactuals/minimal-change-semantics/sphere-models — Sphere Models
- **Action**: DEFER-TO-EXTENSION

### counterfactuals/minimal-change-semantics/transitivity — Transitivity
- **Action**: DEFER-TO-EXTENSION

### counterfactuals/minimal-change-semantics/true-false — True False
- **Action**: DEFER-TO-EXTENSION


### Topic: History (20 sections)

### history/biographies/alan-turing — Alan Turing
- **Action**: DEFER-TO-EXTENSION

### history/biographies/alfred-tarski — Alfred Tarski
- **Action**: DEFER-TO-EXTENSION

### history/biographies/alonzo-church — Alonzo Church
- **Action**: DEFER-TO-EXTENSION

### history/biographies/bertrand-russell — Bertrand Russell
- **Action**: DEFER-TO-EXTENSION

### history/biographies/biographies — Biographies
- **Action**: DEFER-TO-EXTENSION

### history/biographies/emmy-noether — Emmy Noether
- **Action**: DEFER-TO-EXTENSION

### history/biographies/ernst-zermelo — Ernst Zermelo
- **Action**: DEFER-TO-EXTENSION

### history/biographies/georg-cantor — Georg Cantor
- **Action**: DEFER-TO-EXTENSION

### history/biographies/gerhard-gentzen — Gerhard Gentzen
- **Action**: DEFER-TO-EXTENSION

### history/biographies/julia-robinson — Julia Robinson
- **Action**: DEFER-TO-EXTENSION

### history/biographies/kurt-goedel — Kurt Goedel
- **Action**: DEFER-TO-EXTENSION

### history/biographies/rozsa-peter — Rozsa Peter
- **Action**: DEFER-TO-EXTENSION

### history/history — History
- **Action**: DEFER-TO-EXTENSION

### history/set-theory/cantor-plane — Cantor Plane
- **Action**: DEFER-TO-EXTENSION

### history/set-theory/hilbert-curve — Hilbert Curve
- **Action**: DEFER-TO-EXTENSION

### history/set-theory/infinitesimals — Infinitesimals
- **Action**: DEFER-TO-EXTENSION

### history/set-theory/limits — Limits
- **Action**: DEFER-TO-EXTENSION

### history/set-theory/mythology — Mythology
- **Action**: DEFER-TO-EXTENSION

### history/set-theory/pathologies — Pathologies
- **Action**: DEFER-TO-EXTENSION

### history/set-theory/set-theory — Set Theory
- **Action**: DEFER-TO-EXTENSION


### Topic: Intuitionistic Logic (34 sections)

### intuitionistic-logic/introduction/axiomatic-derivations — Axiomatic Derivations
- **Action**: DEFER-TO-EXTENSION

### intuitionistic-logic/introduction/bhk-interpretation — Bhk Interpretation
- **Action**: DEFER-TO-EXTENSION

### intuitionistic-logic/introduction/constructive-reasoning — Constructive Reasoning
- **Action**: DEFER-TO-EXTENSION

### intuitionistic-logic/introduction/introduction — Introduction
- **Action**: DEFER-TO-EXTENSION

### intuitionistic-logic/introduction/natural-deduction — Natural Deduction
- **Action**: DEFER-TO-EXTENSION

### intuitionistic-logic/introduction/syntax — Syntax
- **Action**: DEFER-TO-EXTENSION

### intuitionistic-logic/intuitionistic-logic — Intuitionistic Logic
- **Action**: DEFER-TO-EXTENSION

### intuitionistic-logic/propositions-as-types/introduction — Introduction
- **Action**: DEFER-TO-EXTENSION

### intuitionistic-logic/propositions-as-types/normalization — Normalization
- **Action**: DEFER-TO-EXTENSION

### intuitionistic-logic/propositions-as-types/proof-terms — Proof Terms
- **Action**: DEFER-TO-EXTENSION

### intuitionistic-logic/propositions-as-types/proofs-to-terms — Proofs To Terms
- **Action**: DEFER-TO-EXTENSION

### intuitionistic-logic/propositions-as-types/propositions-as-types — Propositions As Types
- **Action**: DEFER-TO-EXTENSION

### intuitionistic-logic/propositions-as-types/reduction — Reduction
- **Action**: DEFER-TO-EXTENSION

### intuitionistic-logic/propositions-as-types/sequent-natural-deduction — Sequent Natural Deduction
- **Action**: DEFER-TO-EXTENSION

### intuitionistic-logic/propositions-as-types/terms-to-proofs — Terms To Proofs
- **Action**: DEFER-TO-EXTENSION

### intuitionistic-logic/semantics/introduction — Introduction
- **Action**: DEFER-TO-EXTENSION

### intuitionistic-logic/semantics/propositions — Propositions
- **Action**: DEFER-TO-EXTENSION

### intuitionistic-logic/semantics/relational-models — Relational Models
- **Action**: DEFER-TO-EXTENSION

### intuitionistic-logic/semantics/semantic-notions — Semantic Notions
- **Action**: DEFER-TO-EXTENSION

### intuitionistic-logic/semantics/semantics — Semantics
- **Action**: DEFER-TO-EXTENSION

### intuitionistic-logic/semantics/topological-semantics — Topological Semantics
- **Action**: DEFER-TO-EXTENSION

### intuitionistic-logic/soundness-completeness/canonical-model — Canonical Model
- **Action**: DEFER-TO-EXTENSION

### intuitionistic-logic/soundness-completeness/completeness-thm — Completeness Thm
- **Action**: DEFER-TO-EXTENSION

### intuitionistic-logic/soundness-completeness/decidability — Decidability
- **Action**: DEFER-TO-EXTENSION

### intuitionistic-logic/soundness-completeness/lindenbaum — Lindenbaum
- **Action**: DEFER-TO-EXTENSION

### intuitionistic-logic/soundness-completeness/soundness-axd — Soundness Axd
- **Action**: DEFER-TO-EXTENSION

### intuitionistic-logic/soundness-completeness/soundness-completeness — Soundness Completeness
- **Action**: DEFER-TO-EXTENSION

### intuitionistic-logic/soundness-completeness/soundness-nd — Soundness Nd
- **Action**: DEFER-TO-EXTENSION

### intuitionistic-logic/soundness-completeness/truth-lemma — Truth Lemma
- **Action**: DEFER-TO-EXTENSION

### intuitionistic-logic/tableaux/introduction — Introduction
- **Action**: DEFER-TO-EXTENSION

### intuitionistic-logic/tableaux/proofs — Proofs
- **Action**: DEFER-TO-EXTENSION

### intuitionistic-logic/tableaux/rules — Rules
- **Action**: DEFER-TO-EXTENSION

### intuitionistic-logic/tableaux/soundness — Soundness
- **Action**: DEFER-TO-EXTENSION

### intuitionistic-logic/tableaux/tableaux — Tableaux
- **Action**: DEFER-TO-EXTENSION


### Topic: Lambda Calculus (44 sections)

### lambda-calculus/church-rosser/beta-eta-reduction — Beta Eta Reduction
- **Action**: DEFER-TO-EXTENSION

### lambda-calculus/church-rosser/beta-reduction — Beta Reduction
- **Action**: DEFER-TO-EXTENSION

### lambda-calculus/church-rosser/church-rosser — Church Rosser
- **Action**: DEFER-TO-EXTENSION

### lambda-calculus/church-rosser/definitions-and-properties — Definitions And Properties
- **Action**: DEFER-TO-EXTENSION

### lambda-calculus/church-rosser/parallel-beta-eta-reduction — Parallel Beta Eta Reduction
- **Action**: DEFER-TO-EXTENSION

### lambda-calculus/church-rosser/parallel-beta-reduction — Parallel Beta Reduction
- **Action**: DEFER-TO-EXTENSION

### lambda-calculus/introduction/basic-pr-lambda — Basic Pr Lambda
- **Action**: DEFER-TO-EXTENSION

### lambda-calculus/introduction/church-rosser — Church Rosser
- **Action**: DEFER-TO-EXTENSION

### lambda-calculus/introduction/composition — Composition
- **Action**: DEFER-TO-EXTENSION

### lambda-calculus/introduction/computable-lambda — Computable Lambda
- **Action**: DEFER-TO-EXTENSION

### lambda-calculus/introduction/currying — Currying
- **Action**: DEFER-TO-EXTENSION

### lambda-calculus/introduction/fixed-point-combinator — Fixed Point Combinator
- **Action**: DEFER-TO-EXTENSION

### lambda-calculus/introduction/introduction — Introduction
- **Action**: DEFER-TO-EXTENSION

### lambda-calculus/introduction/lambda-computable — Lambda Computable
- **Action**: DEFER-TO-EXTENSION

### lambda-calculus/introduction/lambda-definability — Lambda Definability
- **Action**: DEFER-TO-EXTENSION

### lambda-calculus/introduction/minimization — Minimization
- **Action**: DEFER-TO-EXTENSION

### lambda-calculus/introduction/overview — Overview
- **Action**: DEFER-TO-EXTENSION

### lambda-calculus/introduction/primitive-recursion — Primitive Recursion
- **Action**: DEFER-TO-EXTENSION

### lambda-calculus/introduction/reduction — Reduction
- **Action**: DEFER-TO-EXTENSION

### lambda-calculus/introduction/syntax — Syntax
- **Action**: DEFER-TO-EXTENSION

### lambda-calculus/lambda-calculus — Lambda Calculus
- **Action**: DEFER-TO-EXTENSION

### lambda-calculus/lambda-definability/arithmetical-functions — Arithmetical Functions
- **Action**: DEFER-TO-EXTENSION

### lambda-calculus/lambda-definability/fixpoints — Fixpoints
- **Action**: DEFER-TO-EXTENSION

### lambda-calculus/lambda-definability/introduction — Introduction
- **Action**: DEFER-TO-EXTENSION

### lambda-calculus/lambda-definability/lambda-definability — Lambda Definability
- **Action**: DEFER-TO-EXTENSION

### lambda-calculus/lambda-definability/lambda-definable-recursive — Lambda Definable Recursive
- **Action**: DEFER-TO-EXTENSION

### lambda-calculus/lambda-definability/lists — Lists
- **Action**: DEFER-TO-EXTENSION

### lambda-calculus/lambda-definability/minimization — Minimization
- **Action**: DEFER-TO-EXTENSION

### lambda-calculus/lambda-definability/pairs — Pairs
- **Action**: DEFER-TO-EXTENSION

### lambda-calculus/lambda-definability/partial-recursive-functions — Partial Recursive Functions
- **Action**: DEFER-TO-EXTENSION

### lambda-calculus/lambda-definability/primitive-recursive-functions — Primitive Recursive Functions
- **Action**: DEFER-TO-EXTENSION

### lambda-calculus/lambda-definability/truth-values — Truth Values
- **Action**: DEFER-TO-EXTENSION

### lambda-calculus/syntax/abbreviated-syntax — Abbreviated Syntax
- **Action**: DEFER-TO-EXTENSION

### lambda-calculus/syntax/alpha — Alpha
- **Action**: DEFER-TO-EXTENSION

### lambda-calculus/syntax/beta — Beta
- **Action**: DEFER-TO-EXTENSION

### lambda-calculus/syntax/conversion — Conversion
- **Action**: DEFER-TO-EXTENSION

### lambda-calculus/syntax/de-bruijn — De Bruijn
- **Action**: DEFER-TO-EXTENSION

### lambda-calculus/syntax/eta — Eta
- **Action**: DEFER-TO-EXTENSION

### lambda-calculus/syntax/free-variables — Free Variables
- **Action**: DEFER-TO-EXTENSION

### lambda-calculus/syntax/substitution — Substitution
- **Action**: DEFER-TO-EXTENSION

### lambda-calculus/syntax/syntax — Syntax
- **Action**: DEFER-TO-EXTENSION

### lambda-calculus/syntax/term-revisited — Term Revisited
- **Action**: DEFER-TO-EXTENSION

### lambda-calculus/syntax/terms — Terms
- **Action**: DEFER-TO-EXTENSION

### lambda-calculus/syntax/unique-readability — Unique Readability
- **Action**: DEFER-TO-EXTENSION


### Topic: Many Valued Logic (25 sections)

### many-valued-logic/infinite-valued-logics/goedel — Goedel
- **Action**: DEFER-TO-EXTENSION

### many-valued-logic/infinite-valued-logics/infinite-valued-logics — Infinite Valued Logics
- **Action**: DEFER-TO-EXTENSION

### many-valued-logic/infinite-valued-logics/introduction — Introduction
- **Action**: DEFER-TO-EXTENSION

### many-valued-logic/infinite-valued-logics/lukasiewicz — Lukasiewicz
- **Action**: DEFER-TO-EXTENSION

### many-valued-logic/many-valued-logic — Many Valued Logic
- **Action**: DEFER-TO-EXTENSION

### many-valued-logic/sequent-calculus/introduction — Introduction
- **Action**: DEFER-TO-EXTENSION

### many-valued-logic/sequent-calculus/proof-theoretic-notions — Proof Theoretic Notions
- **Action**: DEFER-TO-EXTENSION

### many-valued-logic/sequent-calculus/propositional-rules — Propositional Rules
- **Action**: DEFER-TO-EXTENSION

### many-valued-logic/sequent-calculus/rules-and-proofs — Rules And Proofs
- **Action**: DEFER-TO-EXTENSION

### many-valued-logic/sequent-calculus/sequent-calculus — Sequent Calculus
- **Action**: DEFER-TO-EXTENSION

### many-valued-logic/sequent-calculus/structural-rules — Structural Rules
- **Action**: DEFER-TO-EXTENSION

### many-valued-logic/syntax-and-semantics/connectives — Connectives
- **Action**: DEFER-TO-EXTENSION

### many-valued-logic/syntax-and-semantics/formulas — Formulas
- **Action**: DEFER-TO-EXTENSION

### many-valued-logic/syntax-and-semantics/introduction — Introduction
- **Action**: DEFER-TO-EXTENSION

### many-valued-logic/syntax-and-semantics/matrices — Matrices
- **Action**: DEFER-TO-EXTENSION

### many-valued-logic/syntax-and-semantics/semantic-notions — Semantic Notions
- **Action**: DEFER-TO-EXTENSION

### many-valued-logic/syntax-and-semantics/sublogics — Sublogics
- **Action**: DEFER-TO-EXTENSION

### many-valued-logic/syntax-and-semantics/syntax-and-semantics — Syntax And Semantics
- **Action**: DEFER-TO-EXTENSION

### many-valued-logic/syntax-and-semantics/valuations-sat — Valuations Sat
- **Action**: DEFER-TO-EXTENSION

### many-valued-logic/three-valued-logics/goedel — Goedel
- **Action**: DEFER-TO-EXTENSION

### many-valued-logic/three-valued-logics/introduction — Introduction
- **Action**: DEFER-TO-EXTENSION

### many-valued-logic/three-valued-logics/kleene — Kleene
- **Action**: DEFER-TO-EXTENSION

### many-valued-logic/three-valued-logics/lukasiewicz — Lukasiewicz
- **Action**: DEFER-TO-EXTENSION

### many-valued-logic/three-valued-logics/multiple-designation — Multiple Designation
- **Action**: DEFER-TO-EXTENSION

### many-valued-logic/three-valued-logics/three-valued-logics — Three Valued Logics
- **Action**: DEFER-TO-EXTENSION


### Topic: Methods (19 sections)

### methods/induction/induction — Induction
- **Action**: DEFER-TO-EXTENSION

### methods/induction/induction-on-N — Induction On N
- **Action**: DEFER-TO-EXTENSION

### methods/induction/inductive-definitions — Inductive Definitions
- **Action**: DEFER-TO-EXTENSION

### methods/induction/introduction — Introduction
- **Action**: DEFER-TO-EXTENSION

### methods/induction/relations — Relations
- **Action**: DEFER-TO-EXTENSION

### methods/induction/strong-induction — Strong Induction
- **Action**: DEFER-TO-EXTENSION

### methods/induction/structural-induction — Structural Induction
- **Action**: DEFER-TO-EXTENSION

### methods/methods — Methods
- **Action**: DEFER-TO-EXTENSION

### methods/proofs/cant-do-it — Cant Do It
- **Action**: DEFER-TO-EXTENSION

### methods/proofs/example-1 — Example 1
- **Action**: DEFER-TO-EXTENSION

### methods/proofs/example-2 — Example 2
- **Action**: DEFER-TO-EXTENSION

### methods/proofs/inference-patterns — Inference Patterns
- **Action**: DEFER-TO-EXTENSION

### methods/proofs/introduction — Introduction
- **Action**: DEFER-TO-EXTENSION

### methods/proofs/proof-by-contradiction — Proof By Contradiction
- **Action**: DEFER-TO-EXTENSION

### methods/proofs/proofs — Proofs
- **Action**: DEFER-TO-EXTENSION

### methods/proofs/reading-proofs — Reading Proofs
- **Action**: DEFER-TO-EXTENSION

### methods/proofs/resources — Resources
- **Action**: DEFER-TO-EXTENSION

### methods/proofs/starting-proofs — Starting Proofs
- **Action**: DEFER-TO-EXTENSION

### methods/proofs/using-definitions — Using Definitions
- **Action**: DEFER-TO-EXTENSION


### Topic: Normal Modal Logic (69 sections)

### normal-modal-logic/axioms-systems/axioms-systems — Axioms Systems
- **Action**: DEFER-TO-EXTENSION

### normal-modal-logic/axioms-systems/consistency — Consistency
- **Action**: DEFER-TO-EXTENSION

### normal-modal-logic/axioms-systems/derived-rules — Derived Rules
- **Action**: DEFER-TO-EXTENSION

### normal-modal-logic/axioms-systems/duals — Duals
- **Action**: DEFER-TO-EXTENSION

### normal-modal-logic/axioms-systems/introduction — Introduction
- **Action**: DEFER-TO-EXTENSION

### normal-modal-logic/axioms-systems/logics-proofs — Logics Proofs
- **Action**: DEFER-TO-EXTENSION

### normal-modal-logic/axioms-systems/more-proofs-in-K — More Proofs In K
- **Action**: DEFER-TO-EXTENSION

### normal-modal-logic/axioms-systems/normal-logics — Normal Logics
- **Action**: DEFER-TO-EXTENSION

### normal-modal-logic/axioms-systems/proofs-in-K — Proofs In K
- **Action**: DEFER-TO-EXTENSION

### normal-modal-logic/axioms-systems/proofs-modal-systems — Proofs Modal Systems
- **Action**: DEFER-TO-EXTENSION

### normal-modal-logic/axioms-systems/provability-from-set — Provability From Set
- **Action**: DEFER-TO-EXTENSION

### normal-modal-logic/axioms-systems/provability-properties — Provability Properties
- **Action**: DEFER-TO-EXTENSION

### normal-modal-logic/axioms-systems/soundness — Soundness
- **Action**: DEFER-TO-EXTENSION

### normal-modal-logic/axioms-systems/systems-distinct — Systems Distinct
- **Action**: DEFER-TO-EXTENSION

### normal-modal-logic/completeness/canonical-models — Canonical Models
- **Action**: DEFER-TO-EXTENSION

### normal-modal-logic/completeness/complete-consistent-sets — Complete Consistent Sets
- **Action**: DEFER-TO-EXTENSION

### normal-modal-logic/completeness/completeness — Completeness
- **Action**: DEFER-TO-EXTENSION

### normal-modal-logic/completeness/completeness-K — Completeness K
- **Action**: DEFER-TO-EXTENSION

### normal-modal-logic/completeness/frame-completeness — Frame Completeness
- **Action**: DEFER-TO-EXTENSION

### normal-modal-logic/completeness/introduction — Introduction
- **Action**: DEFER-TO-EXTENSION

### normal-modal-logic/completeness/lindenbaums-lemma — Lindenbaums Lemma
- **Action**: DEFER-TO-EXTENSION

### normal-modal-logic/completeness/modalities-ccs — Modalities Ccs
- **Action**: DEFER-TO-EXTENSION

### normal-modal-logic/completeness/truth-lemma — Truth Lemma
- **Action**: DEFER-TO-EXTENSION

### normal-modal-logic/filtrations/S5-decidable — S5 Decidable
- **Action**: DEFER-TO-EXTENSION

### normal-modal-logic/filtrations/S5-fmp — S5 Fmp
- **Action**: DEFER-TO-EXTENSION

### normal-modal-logic/filtrations/euclidean-filtrations — Euclidean Filtrations
- **Action**: DEFER-TO-EXTENSION

### normal-modal-logic/filtrations/examples-of-filtrations — Examples Of Filtrations
- **Action**: DEFER-TO-EXTENSION

### normal-modal-logic/filtrations/filtrations — Filtrations
- **Action**: DEFER-TO-EXTENSION

### normal-modal-logic/filtrations/filtrations-def — Filtrations Def
- **Action**: DEFER-TO-EXTENSION

### normal-modal-logic/filtrations/finite — Finite
- **Action**: DEFER-TO-EXTENSION

### normal-modal-logic/filtrations/introduction — Introduction
- **Action**: DEFER-TO-EXTENSION

### normal-modal-logic/filtrations/more-filtrations — More Filtrations
- **Action**: DEFER-TO-EXTENSION

### normal-modal-logic/filtrations/preliminaries — Preliminaries
- **Action**: DEFER-TO-EXTENSION

### normal-modal-logic/frame-definability/definability — Definability
- **Action**: DEFER-TO-EXTENSION

### normal-modal-logic/frame-definability/equivalence-S5 — Equivalence S5
- **Action**: DEFER-TO-EXTENSION

### normal-modal-logic/frame-definability/first-order-definability — First Order Definability
- **Action**: DEFER-TO-EXTENSION

### normal-modal-logic/frame-definability/frame-definability — Frame Definability
- **Action**: DEFER-TO-EXTENSION

### normal-modal-logic/frame-definability/frames — Frames
- **Action**: DEFER-TO-EXTENSION

### normal-modal-logic/frame-definability/introduction — Introduction
- **Action**: DEFER-TO-EXTENSION

### normal-modal-logic/frame-definability/properties-accessibility — Properties Accessibility
- **Action**: DEFER-TO-EXTENSION

### normal-modal-logic/frame-definability/second-order-definability — Second Order Definability
- **Action**: DEFER-TO-EXTENSION

### normal-modal-logic/normal-modal-logic — Normal Modal Logic
- **Action**: DEFER-TO-EXTENSION

### normal-modal-logic/sequent-calculus/introduction — Introduction
- **Action**: DEFER-TO-EXTENSION

### normal-modal-logic/sequent-calculus/more-rules — More Rules
- **Action**: DEFER-TO-EXTENSION

### normal-modal-logic/sequent-calculus/proofs-in-K — Proofs In K
- **Action**: DEFER-TO-EXTENSION

### normal-modal-logic/sequent-calculus/rules-for-K — Rules For K
- **Action**: DEFER-TO-EXTENSION

### normal-modal-logic/sequent-calculus/sequent-calculus — Sequent Calculus
- **Action**: DEFER-TO-EXTENSION

### normal-modal-logic/syntax-and-semantics/entailment — Entailment
- **Action**: DEFER-TO-EXTENSION

### normal-modal-logic/syntax-and-semantics/introduction — Introduction
- **Action**: DEFER-TO-EXTENSION

### normal-modal-logic/syntax-and-semantics/language-modal-logic — Language Modal Logic
- **Action**: DEFER-TO-EXTENSION

### normal-modal-logic/syntax-and-semantics/modal-validity — Modal Validity
- **Action**: DEFER-TO-EXTENSION

### normal-modal-logic/syntax-and-semantics/normal-modal-logics — Normal Modal Logics
- **Action**: DEFER-TO-EXTENSION

### normal-modal-logic/syntax-and-semantics/relational-models — Relational Models
- **Action**: DEFER-TO-EXTENSION

### normal-modal-logic/syntax-and-semantics/schemas — Schemas
- **Action**: DEFER-TO-EXTENSION

### normal-modal-logic/syntax-and-semantics/substitution — Substitution
- **Action**: DEFER-TO-EXTENSION

### normal-modal-logic/syntax-and-semantics/syntax-and-semantics — Syntax And Semantics
- **Action**: DEFER-TO-EXTENSION

### normal-modal-logic/syntax-and-semantics/tautological-instances — Tautological Instances
- **Action**: DEFER-TO-EXTENSION

### normal-modal-logic/syntax-and-semantics/truth-at-w — Truth At W
- **Action**: DEFER-TO-EXTENSION

### normal-modal-logic/syntax-and-semantics/truth-in-model — Truth In Model
- **Action**: DEFER-TO-EXTENSION

### normal-modal-logic/tableaux/completeness — Completeness
- **Action**: DEFER-TO-EXTENSION

### normal-modal-logic/tableaux/countermodels — Countermodels
- **Action**: DEFER-TO-EXTENSION

### normal-modal-logic/tableaux/introduction — Introduction
- **Action**: DEFER-TO-EXTENSION

### normal-modal-logic/tableaux/more-rules — More Rules
- **Action**: DEFER-TO-EXTENSION

### normal-modal-logic/tableaux/more-soundness — More Soundness
- **Action**: DEFER-TO-EXTENSION

### normal-modal-logic/tableaux/proofs-in-K — Proofs In K
- **Action**: DEFER-TO-EXTENSION

### normal-modal-logic/tableaux/rules-for-K — Rules For K
- **Action**: DEFER-TO-EXTENSION

### normal-modal-logic/tableaux/simple-S5 — Simple S5
- **Action**: DEFER-TO-EXTENSION

### normal-modal-logic/tableaux/soundness — Soundness
- **Action**: DEFER-TO-EXTENSION

### normal-modal-logic/tableaux/tableaux — Tableaux
- **Action**: DEFER-TO-EXTENSION


### Topic: Reference (3 sections)

### reference/fraktur-alphabet/fraktur-alphabet — Fraktur Alphabet
- **Action**: DEFER-TO-EXTENSION

### reference/greek-alphabet/greek-alphabet — Greek Alphabet
- **Action**: DEFER-TO-EXTENSION

### reference/reference — Reference
- **Action**: DEFER-TO-EXTENSION


### Topic: Second Order Logic (20 sections)

### second-order-logic/metatheory/compactness — Compactness
- **Action**: DEFER-TO-EXTENSION

### second-order-logic/metatheory/introduction — Introduction
- **Action**: DEFER-TO-EXTENSION

### second-order-logic/metatheory/loewenheim-skolem — Loewenheim Skolem
- **Action**: DEFER-TO-EXTENSION

### second-order-logic/metatheory/metatheory — Metatheory
- **Action**: DEFER-TO-EXTENSION

### second-order-logic/metatheory/second-order-arithmetic — Second Order Arithmetic
- **Action**: DEFER-TO-EXTENSION

### second-order-logic/metatheory/undecidability-and-axiomatizability — Undecidability And Axiomatizability
- **Action**: DEFER-TO-EXTENSION

### second-order-logic/second-order-logic — Second Order Logic
- **Action**: DEFER-TO-EXTENSION

### second-order-logic/sol-and-set-theory/cardinalities — Cardinalities
- **Action**: DEFER-TO-EXTENSION

### second-order-logic/sol-and-set-theory/comparing-sets — Comparing Sets
- **Action**: DEFER-TO-EXTENSION

### second-order-logic/sol-and-set-theory/introduction — Introduction
- **Action**: DEFER-TO-EXTENSION

### second-order-logic/sol-and-set-theory/power-of-continuum — Power Of Continuum
- **Action**: DEFER-TO-EXTENSION

### second-order-logic/sol-and-set-theory/sol-and-set-theory — Sol And Set Theory
- **Action**: DEFER-TO-EXTENSION

### second-order-logic/syntax-and-semantics/expressive-power — Expressive Power
- **Action**: DEFER-TO-EXTENSION

### second-order-logic/syntax-and-semantics/inf-count — Inf Count
- **Action**: DEFER-TO-EXTENSION

### second-order-logic/syntax-and-semantics/introduction — Introduction
- **Action**: DEFER-TO-EXTENSION

### second-order-logic/syntax-and-semantics/language-of-sol — Language Of Sol
- **Action**: DEFER-TO-EXTENSION

### second-order-logic/syntax-and-semantics/satisfaction — Satisfaction
- **Action**: DEFER-TO-EXTENSION

### second-order-logic/syntax-and-semantics/semantic-notions — Semantic Notions
- **Action**: DEFER-TO-EXTENSION

### second-order-logic/syntax-and-semantics/syntax-and-semantics — Syntax And Semantics
- **Action**: DEFER-TO-EXTENSION

### second-order-logic/syntax-and-semantics/terms-formulas — Terms Formulas
- **Action**: DEFER-TO-EXTENSION


---

## Summary

- **Total extension sections**: 263
- **Extension topics**: 10
- **Core sections (already in COMPRESSION-PLAN)**: 353
- **Total known sections**: 616
