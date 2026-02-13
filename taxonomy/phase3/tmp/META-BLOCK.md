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
