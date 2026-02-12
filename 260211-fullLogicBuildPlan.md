# Phase 1: Build the Primitive Taxonomy of Mathematical Logic

## Context

We're creating a lean, Metamath-inspired systematization of mathematical logic. The OpenLogic textbook (1000+ pages, 20 topic areas) serves as scope reference but not starting point — we build bottom-up from first principles, then validate top-down.

**Inspiration**: substrateresearch's approach — identify irreducible domains, enumerate primitives per domain, establish cross-domain conventions with boundary principles, prove completeness via gap analysis.

**This phase**: Produce the foundational taxonomy — the "periodic table" of logic concepts that everything else maps onto. This is a **reference taxonomy** for readers who have some logic exposure, not a first-encounter textbook. Pedagogical sequencing (guided paths for learners) is provided via README but the specs themselves prioritize correctness and traceability.

**Estimated effort**: ~60–80 focused hours total. Steps 3–8 (domain specs) are ~8–12 hours each. Steps 2, 9, 10, 11 are ~4–6 hours each. Steps 1, 12 are ~1–2 hours each.

## Deliverables

All files go in a new `taxonomy/` directory at project root.

```
taxonomy/
├── README.md                          # Index, overview, guided learning path, dependency diagram
├── CONVENTIONS.md                     # Cross-domain conventions, ID scheme, boundary principles,
│                                      #   reference format, metatheory protocol, ownership rules,
│                                      #   normative language, completeness checklist, primitive registry,
│                                      #   worked example, redundancy detection procedure
├── DOMAIN-SET-BOOTSTRAP.md            # Domain BST — naive set theory for metalanguage (Level-0)
├── DOMAIN-SYNTAX.md                   # Domain SYN
├── DOMAIN-SEMANTICS.md                # Domain SEM
├── DOMAIN-DEDUCTION.md                # Domain DED
├── DOMAIN-COMPUTATION.md              # Domain CMP
├── DOMAIN-SET-FORMAL.md               # Domain SET — ZFC as a first-order theory (Level-1)
├── CROSS-DOMAIN-MAP.md                # Primitive ownership table, dependency graph,
│                                      #   composition patterns (metatheorems), variant compatibility
└── GAP-ANALYSIS.md                    # Completeness argument, OL coverage mapping,
                                       #   domain sufficiency argument
```

---

## Foundational Principles

### Principle 1: Closed Domain Catalog, Open Pattern Catalog

The **domain catalog is closed**: 5 domains + BST. No 6th domain will be added. Any concept that appears to need a new domain MUST be resolved by: (a) assigning it to an existing domain via boundary principles, or (b) documenting it as a composition pattern.

The **composition pattern catalog is open**: new metatheorems, new cross-domain results, and new application-level patterns can be added indefinitely without restructuring the taxonomy.

New logics (modal, intuitionistic, etc.) are **extensions within existing domains**, not new domains. They plug in via documented extension points.

This mirrors substrateresearch: 9 substrates (closed) + 14+ composition patterns (open).

### Principle 2: Semi-Formal Specification Standard

**"Semi-formal" is defined as follows**:

- Every primitive, definition, axiom, and theorem MUST have both a **formal statement** (using LaTeX math notation: `$...$`) and a **natural language explanation** (≥1 complete sentence).
- Every primitive and key definition MUST have ≥1 **motivating example** — a concrete instance that makes the abstract concept tangible.
- Notation follows standard mathematical logic conventions (Enderton, Mendelson). When conventions differ between sources, the chosen convention is noted with SRC reference.
- **Balance**: formal notation for precision, prose for intuition, examples for grounding. If a reader with one semester of logic cannot parse a formal statement after reading its explanation and example, the explanation is insufficient.

### Principle 3: One Owner, Zero Redundancy

Every concept has **exactly one owning domain**. Other domains reference it, never redefine it. This is enforced by:
- Boundary principles P1–P5 (resolve ownership disputes)
- Primitive Registry (single source of truth, maintained in CONVENTIONS.md)
- Systematic redundancy detection (run during reconciliation)
- Self-audit checklists (per-domain structural verification)

### Principle 4: Divergences from Substrateresearch

The substrate methodology was designed for software systems. We adapt it for mathematics with these **deliberate divergences**:

| Substrate Feature | Logic Adaptation | Justification |
|---|---|---|
| Operational lifecycle (create/update/archive) | Not applicable | Mathematical objects are timeless; they don't have lifecycle states |
| Event bus (cross-substrate communication) | Static cross-domain references | Mathematical dependencies are permanent, not event-driven |
| Envelope chain (authority restriction) | Dependency DAG (prerequisite ordering) | Mathematics has prerequisites, not authority hierarchies |
| Concurrency & ordering | Not applicable | Mathematical proof is sequential; no concurrent access issues |
| Security & privacy | Not applicable | No sensitive data in pure mathematics |
| 24-section template | 13-section template | Sections 10, 13–17, 19 (persistence, migration, operational profile, observability) are irrelevant to mathematics |

What we **preserve fully**: Sources/Assumptions/Unknowns discipline. Normative language (MUST/SHOULD/MAY). Traceability IDs on every item. Boundary principles for ownership. Primitive ownership table. Gap analysis. Completeness checklist. Composition patterns.

---

## Key Architectural Decisions

### 1. Five irreducible domains + the metatheory stratification

| Code | Domain | Irreducible Question | Target Primitives | Target Definitions |
|------|--------|---------------------|-------------------|--------------------|
| **BST** | SET-BOOTSTRAP | What naive mathematical objects does the metalanguage use? | ~15 | ~5 |
| **SYN** | SYNTAX | How are well-formed expressions constructed? | ~18 | ~8 |
| **SEM** | SEMANTICS | How is meaning assigned to expressions? | ~15 | ~12 |
| **DED** | DEDUCTION | How are truths derived from assumptions? | ~12 | ~10 |
| **CMP** | COMPUTATION | What is effectively decidable/computable? | ~12 | ~10 |
| **SET** | SET-FOUNDATIONS | What is the formal mathematical universe? | ~10 (axioms) | ~15 |

**Note on counts**: Primitives (PRIM) are truly undefined notions. Axioms (AX) are not primitives — they are formal constraints on primitives. Definitions (DEF) are conservative extensions. The target counts above distinguish these. Total items per domain: 20–35. Total across taxonomy (PRIM+DEF+AX): ~150–190 items. Key theorems (THM) are additional items tracked separately. If actual counts during authoring exceed targets by >20%, apply the SEM triage strategy pattern: split into core (needed for basic composition patterns) and supplement (needed for advanced patterns).

**SEM triage strategy**: If SEM exceeds 30 items, split model-theoretic concepts (elementary equivalence, types, categoricity, etc.) into a "Model Theory Supplement" subsection within SEM, clearly marked as "needed only for advanced composition patterns (CP-003, CP-004, CP-011)." Core SEM (satisfaction, truth, validity, consequence, model) stays at ~15 items.

**METATHEORY** = composition patterns (soundness, completeness, compactness, Löwenheim-Skolem, incompleteness, undecidability). These live at domain intersections in CROSS-DOMAIN-MAP.md, not in a separate domain.

**INCOMPLETENESS** = crown-jewel composition result: SYN (arithmetization) × DED (formal provability) × CMP (undecidability) × SET (arithmetic).

### Dissolution arguments (why each domain is irreducible)

Each domain spec MUST include a dissolution argument. Summary:

- **BST**: Naive set concepts (set, function, sequence, induction) are shared infrastructure consumed by ALL other domains. Without BST, every domain would independently introduce "set," "function," "sequence" — causing massive redundancy. BST factors out the common mathematical substrate. Cannot be merged into SET because BST is un-axiomatized metalanguage while SET is a formal first-order theory (see Level-0/Level-1 below).

- **SYN**: Symbol manipulation is definable without reference to truth, meaning, or computation. Formation rules are purely syntactic — they determine which strings are well-formed without assigning meaning. Cannot be merged into SEM because syntax exists prior to and independent of any interpretation (you can study syntax of a language without ever interpreting it).

- **SEM**: Meaning assignment requires interpretation functions and truth values that are not reducible to symbol manipulation or derivation. The concept of "truth in a structure" ($\mathfrak{A} \vDash \varphi$) is fundamentally different from "derivability" ($\Gamma \vdash \varphi$). Cannot be merged into DED because the completeness theorem connecting $\vDash$ and $\vdash$ is a non-trivial result — the fact that you need a deep theorem to bridge them proves they are not the same thing. **Note on model theory**: Model theory is semantics, not set theory, despite being built with set-theoretic tools (BST). Elementary equivalence, types, and categoricity are about what structures satisfy — they answer "what does this theory mean?" not "what sets exist?" Boundary principle P1 applies.

- **DED**: Syntactic consequence ($\vdash$) is a formal, combinatorial notion about symbol manipulation following rules. It is distinct from semantic consequence ($\vDash$) — again, the completeness theorem bridges them. Cannot be merged into SYN because deduction involves *sequences* of formulas organized by rules (not just formation of individual formulas). Cannot be merged into SEM because proof systems are purely syntactic objects that can be studied without any notion of truth.

- **CMP**: "Effective procedure" is an **informal, pre-mathematical concept**. The Church-Turing thesis identifies this intuitive notion with formal models (Turing machines, recursive functions, lambda calculus), but this identification is **not itself a theorem** — it is an empirical thesis supported by evidence, not a mathematical proof. This means CMP's core concept cannot be defined in terms of the other four domains' formal primitives. Cannot be dissolved into SET (Turing machines are set-theoretic constructions, but the *claim* that they capture "all effective procedures" is not set theory). Cannot be dissolved into SYN because CMP's primitives inherently involve the concept of **termination and non-termination** — whether a procedure halts on a given input is about the infinite behavior of a process, which is fundamentally beyond SYN's concern with finite string formation. A Turing machine that runs forever is not a syntactic object; it is a computational phenomenon.

- **SET**: Set membership ($\in$) and the ZFC axioms form the formal foundation for virtually all of mathematics. The cumulative hierarchy ($V_\alpha$), ordinals, and cardinals provide the raw material from which structures, domains, and functions used by other domains are built. Cannot be merged into BST because BST is naive/un-axiomatized while SET is a specific first-order theory amenable to metatheoretic analysis. Cannot be merged into SEM because SET is a *theory* with semantics, not semantics itself.

### 2. The metatheory stratification (resolving SET ↔ SEMANTICS circularity)

This is the single most critical architectural decision. We operate at **two levels**:

- **LEVEL-0 (Metalanguage)**: Naive set theory — sets, functions, relations, sequences, inductive definitions, natural numbers. Documented in `DOMAIN-SET-BOOTSTRAP.md` (code: BST). Used by SYNTAX (to define "the set of formulas"), SEMANTICS (to define structures/models), DEDUCTION (to define derivation sequences), and COMPUTATION (to define functions on $\mathbb{N}$). This is NOT axiomatized; it is the ambient mathematical context, same as any standard logic textbook uses.

  **On naive power set**: BST includes "the collection of all subsets of $A$" as a naive concept, used to define things like "the set of all truth-value assignments." We do NOT claim this is constructive or justify it axiomatically — that is SET's job. BST simply notes: "We assume the standard mathematical practice of collecting subsets. Formal justification is provided by AX-SET004 (Power Set Axiom) in DOMAIN-SET-FORMAL.md."

- **LEVEL-1 (Object language)**: Formal set theory (ZFC) as a first-order theory within the taxonomy. Documented in `DOMAIN-SET-FORMAL.md` (code: SET). This is a specific first-order language ($\mathcal{L}_\in = \{\in\}$) + axiom system, analyzed using SYNTAX, SEMANTICS, and DEDUCTION from LEVEL-0.

**The circularity dissolves**: LEVEL-0 sets are used to BUILD the formalism. LEVEL-1 set theory is a SUBJECT OF the formalism. They are not the same thing. (This mirrors Enderton Ch. 1, Shoenfield Ch. 1, and how Metamath handles its metalogic.)

**Distinguishing meta-level and object-level concepts**: Several terms appear at both levels and MUST be clearly separated:

| Concept | LEVEL-0 (BST) | LEVEL-1 (SYN/SEM/SET) |
|---------|---------------|----------------------|
| Function | A meta-mathematical mapping (e.g., interpretation function $f^{\mathfrak{A}}$) | A function symbol in the formal language (e.g., $f$ in $\mathcal{L}$) |
| Relation | A meta-mathematical relation (e.g., $R \subseteq A \times A$) | A relation symbol in the formal language (e.g., $R$ in $\mathcal{L}$) |
| Set | A naive collection (e.g., "the set of all formulas") | A formal object governed by ZFC axioms |
| Natural number | A meta-mathematical number used for counting (e.g., "arity 2") | A formal object in the theory of arithmetic ($\mathbb{N}$ as a structure) |

### 3. Non-classical logics: three extension types

The 5 domains define the **abstract pattern** all logics share. Classical FOL is the **primary instantiation**. Extensions come in three types:

| Extension Type | What Changes | Examples |
|---------------|-------------|----------|
| **Additive** | New operators/semantic structures added, classical core preserved | Modal ($\Box$/$\Diamond$ + Kripke frames), temporal, deontic, epistemic |
| **Replacement** | Core semantic or proof-theoretic machinery replaced | Intuitionistic (BHK replaces Tarski; no LEM), many-valued (truth set $\neq \{0,1\}$) |
| **Structural** | Structural rules of proof systems modified | Linear logic (no contraction/weakening), relevance logic |

Each domain spec documents which of its components are **fixed** (shared across all logics) vs. **parameterizable** (vary by logic system), and which extension type applies.

**Second-order and higher-order logics** are a special case: they modify SYNTAX fundamentally (variables range over predicates/functions) and break key metatheoretic composition results (no completeness theorem for full SOL). These are documented as a named "higher-order tier" with explicit notes on which composition patterns survive.

**Propositional logic** is handled as a **restricted fragment** within each domain: SYN-PL (no quantifiers/terms), SEM-PL (truth-value assignments, not structures), DED-PL (propositional rules only). Each domain spec notes which primitives belong to the propositional fragment. **The PL fragment MUST be self-coherent**: a reader should be able to extract only PL-annotated items from SYN, SEM, and DED and obtain a complete, self-contained propositional logic sub-taxonomy.

**How to add a new logic variant** (protocol for future extension work):
1. Identify which domains are affected and which extension type applies (additive/replacement/structural)
2. For each affected domain, allocate IDs in the reserved range (*-{DOM}100–199 for modal, 200–299 for intuitionistic, etc.)
3. For additive extensions: add new PRIM/DEF/AX entries with "Extends: PRIM-{DOM}NNN" annotations
4. For replacement extensions: create parallel entries (e.g., PRIM-SEM201: "BHK satisfaction" alongside PRIM-SEM005: "Tarski satisfaction") with explicit notes on which one is active in which variant
5. **If the extension requires BST concepts not already in BST** (e.g., accessibility relations for modal logic): add them as new BST primitives, not as domain-specific primitives, to maintain metalanguage universality
6. Update the Variant Compatibility Matrix in CROSS-DOMAIN-MAP.md
7. Run the self-audit checklist for all affected domain specs

### 4. Format: Markdown + LaTeX math, semi-formal, MUST/SHOULD/MAY

- Prose structure in Markdown (readable, iterable, GitHub-renderable)
- Definitions, axioms, theorem statements in LaTeX math (`$...$` / `$$...$$`)
- Traceability IDs on every item using unambiguous domain codes
- Natural language explanations accompany all formal statements (see Principle 2)
- **Normative language** (per RFC 2119, at full strength):
  - **MUST** / **MUST NOT** = axiom-level; violation means the system is inconsistent or the taxonomy is structurally broken
  - **SHOULD** / **SHOULD NOT** = strong convention; deviation requires documented justification
  - **MAY** = optional; extension point or variant-specific

### 5. Traceability ID scheme

**Domain codes** (unambiguous, 3-letter):

| Code | Domain |
|------|--------|
| BST | Set-Bootstrap (Level-0 naive sets) |
| SYN | Syntax |
| SEM | Semantics |
| DED | Deduction |
| CMP | Computation |
| SET | Set-Formal (Level-1 ZFC) |
| GLB | Global (shared references in CONVENTIONS.md) |

**Item types**:

| Prefix | Meaning | Example |
|--------|---------|---------|
| PRIM | Primitive notion (undefined) | PRIM-SYN001 |
| DEF | Definition (conservative extension) | DEF-SEM003 |
| AX | Axiom | AX-SET001 |
| THM | Theorem | THM-DED005 |
| SRC | Source reference | SRC-GLB001 (global) or SRC-SYN001 (domain-specific) |
| ASM | Assumption | ASM-GLB001 (global) or ASM-CMP001 (domain-specific) |
| UNK | Unknown / open question | UNK-SEM002 |
| DEP | Dependency on another domain | DEP-SEM001 |
| INV | Invariant (must always hold) | INV-SYN001 |
| FORBID | Forbidden state | FORBID-DED001 |
| EXT | Extension point | EXT-SYN001 |

**Source reference scoping**: Global SRC entries (SRC-GLB001 through SRC-GLBNNN) live in CONVENTIONS.md and are shared across all domain specs. Domain-specific SRC entries (SRC-{D}NNN) live in their domain spec for sources relevant only to that domain. Domain specs MAY cite global SRCs by their GLB ID.

**Cross-domain reference format**: `{ItemType}-{DomainCode}{Number}`. When domain A references domain B's primitive: write `PRIM-BST003` (not a local alias). The owning domain MUST list it in Exports; the referencing domain MUST list it in Imports.

**ID stability**: IDs are permanent once assigned. Deprecated items use `DEPRECATED-{original-ID}` with pointer to replacement. IDs MUST NOT be renumbered across versions.

**Document versioning**: Domain specs use semantic versioning (v0.1 → v0.2 for non-breaking additions, v1.0 for first stable release). Breaking changes (removing/renaming primitives) require v(N+1).0 and a migration note listing all affected cross-references.

**Reserved ID ranges for future extensions** (extendable if ranges fill up):
- `*-{DOM}001–099`: Classical core
- `*-{DOM}100–199`: Modal extensions
- `*-{DOM}200–299`: Intuitionistic extensions
- `*-{DOM}300–399`: Higher-order extensions
- `*-{DOM}400–499`: Substructural extensions
- `*-{DOM}500–599`: Many-valued extensions

### 6. Boundary principles (ownership disambiguation)

When a concept could belong to multiple domains, these principles resolve ownership:

| Principle | Rule | Example |
|-----------|------|---------|
| **P1 — Formation vs. Interpretation** | If definable purely via symbol manipulation without truth/meaning → SYN. If requires interpretation → SEM. | "formula" → SYN. "satisfaction" → SEM. |
| **P2 — Derivation vs. Truth** | Syntactic consequence ($\vdash$) → DED. Semantic consequence ($\vDash$) → SEM. Results connecting them → composition patterns. | "proof" → DED. "validity" → SEM. "soundness" → CP-001. |
| **P3 — Effective vs. Abstract** | If inherently involves effective procedures / algorithms → CMP. If involves arbitrary existence → SET or BST. | "decidable set" → CMP. "power set" → BST (naive) / SET (formal). |
| **P4 — One Owner, Many References** | Every primitive has exactly one owner. Others reference via cross-domain format. | See pre-analyzed splits below. |
| **P5 — Bootstrap vs. Formal** | Naive metalanguage concepts → BST. Axiomatized formal concepts → SET. | "the set of all formulas" → BST. "the axiom of infinity" → SET. |

**Pre-analyzed ownership splits for contested concepts**:

| Concept | Syntactic Version (Owner) | Semantic Version (Owner) | Connection |
|---------|--------------------------|-------------------------|------------|
| Consistency | "No derivation of $\varphi \land \neg\varphi$" → **DED** (DEF-DED) | "Has a model" → **SEM** (DEF-SEM) | Linked by CP-001 (Soundness) + CP-002 (Completeness) |
| Validity | N/A | "$\vDash \varphi$ (true in all structures)" → **SEM** (DEF-SEM) | DED aims to derive valid formulas; validity itself is semantic |
| Substitution | "$\varphi[t/x]$ (replacing $x$ by $t$ in $\varphi$)" → **SYN** (DEF-SYN) | Referenced by SEM (for variable assignment) and DED (for rule application) | SYN owns the operation; SEM and DED reference it |
| Theory | N/A | "$\text{Th}(\mathfrak{A}) = \{\varphi : \mathfrak{A} \vDash \varphi\}$" → **SEM** (DEF-SEM) | DED references it when discussing "deductively closed sets"; the connection between semantic and deductive closure is CP-002 |
| Completeness (of a theory) | N/A | "For all sentences $\varphi$: $T \vDash \varphi$ or $T \vDash \neg\varphi$" → **SEM** (DEF-SEM) | Not the same as the Completeness Theorem (CP-002) |
| Decidability | N/A (syntactic decidability is a CMP concept) | "Decidable theory" = theory whose set of theorems is decidable → **CMP** (DEF-CMP) | SEM references it ("decidable theory"); DED references it ("decidable proof system"). CMP owns the concept; others reference via DEF-CMP. Boundary: P3. |
| Axiom | "Axiom schema" / "logical axiom" (rule in a proof system) → **DED** (PRIM-DED) | "ZFC axiom" (formal constraint in a first-order theory) → **SET** (AX-SET) | Different uses: DED axioms are proof-system rules; SET axioms are theory-specific postulates. Shared concept "axiom" splits by context. Boundary: P2 (proof system) vs P5 (formal theory). |
| Modus Ponens | A specific named rule of inference → **DED** (AX-DED, not PRIM) | N/A | MP is a specific instance of the PRIM "rule of inference," formalized as an axiom/rule (AX-DED), not a primitive notion. The PRIM is "rule of inference"; MP is a named AX that instantiates it. |

### 7. Redundancy detection procedure

Run **after completing each domain spec** (partial check against existing registry) and **in full during the Reconciliation Pass** (Step 9):

1. **Alphabetical cross-domain sort**: Export all PRIM and DEF entries from all domains into a single list sorted by concept name. Flag any name appearing in more than one domain.
2. **For each flagged name**: Apply boundary principles P1–P5. Determine: is this genuinely two different concepts (like syntactic vs. semantic consistency), or an ownership violation (same concept defined twice)?
3. **If two different concepts**: Ensure both have distinct names (e.g., "syntactic consistency" vs. "semantic consistency"), distinct IDs, and a documented cross-reference linking them via a composition pattern.
4. **If ownership violation**: Remove the duplicate from the non-owning domain. Replace with a REFERENCES annotation pointing to the owner's ID.
5. **Registry update**: After resolution, update the Primitive Registry in CONVENTIONS.md.

### 8. Iteration and backtracking protocol

Writing domain specs is not purely linear. When Step N reveals a needed change to Step M (M < N):

1. **Identify the change**: What primitive/definition/axiom in domain M needs to be added, modified, or have its ownership changed?
2. **Update domain M's spec**: Make the change, update the Primitive Registry, increment version (v0.1 → v0.2).
3. **Cascade check**: Search all domain specs written between M and N for references to the changed item. Update cross-references.
4. **Re-run self-audit**: Run the 12-item checklist on both the modified domain M and any domains with updated cross-references.
5. **Continue**: Resume Step N with the fix in place.

The Reconciliation Pass (Step 9) is the **scheduled** iteration point, but backtracking MAY happen at any step.

---

## Worked Example: One Fully Specified Primitive

This demonstrates exactly what a completed primitive entry looks like in a domain spec:

```markdown
- AX-DED001: **Modus Ponens (MP)**
  - Statement: If $\Gamma \vdash \varphi$ and $\Gamma \vdash (\varphi \to \psi)$,
    then $\Gamma \vdash \psi$.
  - Description: The rule of inference that, given a derivation of $\varphi$ and a
    derivation of $\varphi \to \psi$, produces a derivation of $\psi$. It is the
    fundamental elimination rule for the conditional connective. MP is a specific
    named instance of the primitive PRIM-DED003 (rule of inference).
  - Depends: PRIM-DED003 (rule of inference), PRIM-DED006 (provability),
    PRIM-SYN003 (logical connective, specifically $\to$)
  - Source: SRC-GLB001 (Enderton §2.4), SRC-GLB009 (Gentzen, as "→-elimination")
  - Normative: MUST (every Hilbert-style system includes MP)
  - Natural language: Given any two already-derived statements where one is "if A
    then B" and the other is "A," you may derive "B."
  - Motivating example: From "It is raining" ($p$) and "If it is raining then
    the ground is wet" ($p \to q$), derive "The ground is wet" ($q$).
    Formally: from $\{p, p \to q\} \vdash p$ and $\{p, p \to q\} \vdash (p \to q)$,
    conclude $\{p, p \to q\} \vdash q$.
```

Every item in every domain spec MUST match this level of detail. The example above demonstrates an **AX** entry. For **PRIM** entries, see the template in Section 3 (primitive entries include: Description, Formal, Ownership, Source, Referenced by, Fragment, Motivating example).

---

## Pre-populated Sources and Assumptions

### Global Sources (SRC-GLB)

| ID | Reference |
|----|-----------|
| SRC-GLB001 | Enderton, *A Mathematical Introduction to Logic*, 2nd ed., 2001 |
| SRC-GLB002 | Shoenfield, *Mathematical Logic*, 1967 |
| SRC-GLB003 | Mendelson, *Introduction to Mathematical Logic*, 6th ed., 2015 |
| SRC-GLB004 | Tarski, "The concept of truth in formalized languages," 1935 |
| SRC-GLB005 | Gödel, "On formally undecidable propositions," 1931 |
| SRC-GLB006 | Church, "An unsolvable problem of elementary number theory," 1936 |
| SRC-GLB007 | Turing, "On computable numbers, with an application to the Entscheidungsproblem," 1936 |
| SRC-GLB008 | Kleene, *Introduction to Metamathematics*, 1952 |
| SRC-GLB009 | Gentzen, "Investigations into logical deduction," 1935 |
| SRC-GLB010 | Zermelo, "Investigations in the foundations of set theory I," 1908 |
| SRC-GLB011 | Kripke, "Semantical considerations on modal logic," 1963 |
| SRC-GLB012 | Heyting, *Intuitionism: An Introduction*, 1956 |
| SRC-GLB013 | Chang & Keisler, *Model Theory*, 3rd ed., 1990 |
| SRC-GLB014 | Marker, *Model Theory: An Introduction*, 2002 |
| SRC-GLB015 | Lindström, "On extensions of elementary logic," 1969 |

### Global Assumptions (ASM-GLB)

| ID | Assumption | Justification |
|----|-----------|---------------|
| ASM-GLB001 | Classical logic is the primary instantiation; non-classical logics are extensions | Matches standard curriculum; classical FOL is the foundation all others are defined against |
| ASM-GLB002 | The metalanguage uses naive set theory (Level-0) without formal justification | Standard practice in all major logic textbooks (Enderton, Shoenfield, Mendelson); formal foundations come later via SET |
| ASM-GLB003 | Readers have at least one semester of logic or equivalent mathematical maturity | This is a reference taxonomy, not a first course; prerequisite knowledge includes basic proof techniques and mathematical notation |
| ASM-GLB004 | English is the metalanguage; formulas use standard notation ($\neg, \to, \land, \lor, \forall, \exists$) | Matches OpenLogic and major textbooks; notation variants are noted where they exist |
| ASM-GLB005 | We scope computability and set theory to "for logic" — only what's needed for metatheorems | Prevents Phase 1 from expanding into an encyclopedia of recursion theory or set theory |

### Global Unknowns (UNK-GLB)

| ID | Unknown | Impact |
|----|---------|--------|
| UNK-GLB001 | Optimal granularity for primitives: should "connective" be one primitive or should $\neg$, $\to$, $\land$, $\lor$, $\leftrightarrow$ each be separate? | Affects primitive count and traceability granularity. Resolve during DOMAIN-SYNTAX authoring. |
| UNK-GLB002 | Should proof system architectures (Hilbert, ND, SC, Tableaux) be parallel PRIM entries or parameterized variants of a single DEF? | Affects DED structure. Resolve during DOMAIN-DEDUCTION authoring. |
| UNK-GLB003 | How deep into model theory should SEM go? | Managed by the SEM triage strategy (see Decision 1). |

---

## Domain Spec Template (13 sections)

```markdown
# DOMAIN-{NAME} v0.1

## 0. Sources & Assumptions
- SRC-{D}001: [author, title, year — specific textbook/tradition]
- ASM-{D}001: [explicit assumption, with justification]
- UNK-{D}001: [open question, with impact assessment]

## 1. Domain Intent
- Irreducible question
- Scope (what this domain covers)
- Non-goals (what it explicitly excludes)
- Dissolution argument (why this domain cannot be reduced to others)

## 2. Prerequisites
- DEP-{D}001: Requires {DomainCode} for [specific primitives listed by ID]

## 3. Primitive Notions
For each primitive (see Worked Example above for required detail level):
- PRIM-{D}NNN: **{Term}**
  - Description: [precise informal description, ≥1 sentence]
  - Formal: [LaTeX math notation, where applicable]
  - Ownership: OWNS
  - Source: SRC-{D}NNN or SRC-GLBNNN
  - Referenced by: [{DomainCode} for {purpose}]
  - Fragment: [PL | FOL | both]
  - Motivating example: [concrete instance, ≥1 sentence]

## 4. Axioms
- AX-{D}NNN: [semi-formal statement with LaTeX math]
  - Depends: [PRIM/DEF-###]
  - Source: SRC-{D}NNN
  - Normative: MUST
  - Natural language: [explanation of what this axiom asserts]

## 5. Definitions (conservative extensions)
- DEF-{D}NNN: **{Term}** := [definition in terms of PRIM/DEF]
  - Depends: [PRIM/DEF-###]
  - Ownership: OWNS | REFERENCES {ID}
  - Referenced by: [{DomainCode} for {purpose}]
  - Fragment: [PL | FOL | both]
  - Motivating example: [concrete instance]

## 6. Key Theorems
- THM-{D}NNN: [semi-formal statement]
  - Depends: [AX/DEF/THM-###]
  - Proof sketch: [reference or outline]

## 7. Invariants & Constraints
- INV-{D}NNN: [condition that MUST always hold]
  - Justification: [why this is invariant]
- FORBID-{D}NNN: [state that MUST NOT occur]
  - Consequence: [what goes wrong if violated]

## 8. Extension Points
For each extension point:
- EXT-{D}NNN: **{Component}**
  - Fixed: [what is shared across all logics]
  - Parameterizable: [what varies]
  - Extension type: Additive | Replacement | Structural
  - Examples: [modal, intuitionistic, etc.]

## 9. Intra-Domain Dependency Graph
- Directed acyclic graph showing logical ordering of primitives,
  definitions, and theorems within this domain.
  Format: ASCII art + structured list.

## 10. Cross-Domain Interface
- **Exports**: [structured table: ID | Concept | Consumed by {DomainCode}]
- **Imports**: [structured table: ID | Concept | Provided by {DomainCode}]

## 11. Completeness Argument
- Why these primitives + axioms + definitions cover the domain
- What would be evidence of a gap
- Specific OL chapters that fall within this domain's scope

## 12. OpenLogic Mapping
- [structured table: OL chapter/section path | maps to taxonomy ID(s)]

## 13. Self-Audit Checklist
- [ ] Every PRIM has: description, formal notation, ownership, source, referenced-by, fragment, example
- [ ] Every DEF depends only on previously listed PRIM/DEF (check intra-domain graph)
- [ ] Every THM depends only on previously listed AX/DEF/THM
- [ ] Every cross-domain reference uses full {Type}-{Code}{Number} format
- [ ] Every import is listed in the source domain's exports
- [ ] Dissolution argument is present and non-trivial
- [ ] Extension points cover all three types (additive/replacement/structural) where applicable
- [ ] Intra-domain dependency graph is acyclic
- [ ] Fragment annotations (PL/FOL/both) are present on all PRIM and DEF entries
- [ ] Motivating examples are present for all PRIM and key DEF entries
- [ ] No PRIM/DEF duplicates an entry in another domain (checked against Primitive Registry)
- [ ] Completeness argument addresses all relevant OL chapters
```

---

## Execution Plan (12 Steps)

### Step 1: Create directory structure [Easy, ~30 min]
- Create `taxonomy/` directory
- **File**: (directory only)

### Step 2: Write CONVENTIONS.md [Medium, ~5 hours]
The foundation document. MUST be complete before any domain spec.

Contains:
- Foundational Principles 1–4 (from this plan, fully written out)
- Metatheory stratification protocol (Level-0 / Level-1)
- Traceability ID scheme (codes, prefixes, ranges, stability, versioning)
- Cross-domain reference format
- Boundary principles P1–P5 with worked examples
- Pre-analyzed ownership splits (consistency, validity, substitution, theory, completeness-of-theory)
- Normative language rules (MUST/SHOULD/MAY at RFC 2119)
- Redundancy detection procedure (the 5-step procedure from Section 7 above)
- Iteration/backtracking protocol (from Section 8 above)
- Primitive Registry (initially empty table; columns: ID, Concept, Owner Domain, Referenced By)
- Domain dependency DAG
- Composition pattern template
- Self-audit checklist (the 12-item list from template Section 13)
- Global SRC, ASM, UNK tables (pre-populated from this plan)
- The worked example (Modus Ponens, from this plan)
- "How to add a new logic variant" protocol
- **File**: `taxonomy/CONVENTIONS.md`

### Step 3: Write DOMAIN-SET-BOOTSTRAP.md [Medium, ~6 hours]
**Prerequisites**: None. This is truly the root.
- Documents the naive set-theoretic metalanguage used by all other domains
- Primitives (~15): set, membership ($\in$), subset ($\subseteq$), union ($\cup$), intersection ($\cap$), ordered pair ($\langle a, b \rangle$), Cartesian product ($A \times B$), relation, function, sequence (finite and infinite), natural number ($\mathbb{N}$), mathematical induction, inductive definition, finite/countable/uncountable, power set (naive — with forward-reference to AX-SET004)
- **Distinguishes meta-level concepts from object-level**: These are the tools we use to TALK ABOUT formal systems. They are not themselves formal objects within a system.
- NOT axiomatized. These are the ambient mathematical concepts.
- Scope: ONLY what's needed as metalanguage for SYN/SEM/DED/CMP.
- Non-goals: ordinals, cardinals, transfinite induction, axiom of choice, well-ordering.
- Source: SRC-GLB001 (Enderton Ch. 0), SRC-GLB002 (Shoenfield Ch. 1)
- **File**: `taxonomy/DOMAIN-SET-BOOTSTRAP.md`
- **Registry update**: Add all BST primitives to Primitive Registry in CONVENTIONS.md

### Step 4: Write DOMAIN-SYNTAX.md [Hard, ~10 hours]
**Prerequisites**: DEP-SYN001: Requires BST for PRIM-BST (set, sequence, inductive definition, function, natural number)
- Primitives (~18): symbol, logical connective ($\neg, \to, \land, \lor, \leftrightarrow$), quantifier ($\forall, \exists$), variable, constant symbol, function symbol, relation symbol, arity, language/signature, term, atomic formula, formula (wff), sentence (closed formula), free occurrence, bound occurrence, scope, subformula
- Definitions (~8): substitution ($\varphi[t/x]$), simultaneous substitution, variant (alphabetic), well-formed (defined by inductive formation rules), structural induction on terms, structural induction on formulas, structural recursion, formula complexity/rank
- Axioms: formation rules (inductive definition of terms; inductive definition of formulas)
- Key theorems: unique readability, substitution lemma, structural induction/recursion principles
- PL fragment: propositional variables + connectives (no quantifiers, no terms, no function/relation/constant symbols)
- Extension points:
  - EXT-SYN001: Additive — modal operators ($\Box$, $\Diamond$) — adds new connectives
  - EXT-SYN002: Additive — lambda abstraction ($\lambda x. M$) — adds binding operator
  - EXT-SYN003: Replacement — higher-order variables (predicate/function variables) — changes variable sorts
  - EXT-SYN004: Additive — temporal operators ($\mathbf{G}$, $\mathbf{F}$, $\mathbf{U}$) — adds new connectives
- **File**: `taxonomy/DOMAIN-SYNTAX.md`
- **Registry update**: Add all SYN primitives and definitions to Primitive Registry

### Step 5: Write DOMAIN-SEMANTICS.md [Hard, ~12 hours]
**Prerequisites**: DEP-SEM001: Requires SYN for PRIM-SYN (formula, sentence, term, language/signature, substitution). DEP-SEM002: Requires BST for PRIM-BST (set, function, relation, sequence, Cartesian product)

**Core semantics** (~15 primitives):
- structure ($\mathfrak{A} = \langle |\mathfrak{A}|, \ldots \rangle$), domain/universe ($|\mathfrak{A}|$), interpretation (of constant/function/relation symbols), variable assignment ($s: \text{Var} \to |\mathfrak{A}|$), $x$-variant of assignment, satisfaction ($\mathfrak{A} \vDash \varphi[s]$), truth in a structure ($\mathfrak{A} \vDash \varphi$), logical validity ($\vDash \varphi$), logical consequence ($\Gamma \vDash \varphi$), model ($\mathfrak{A} \vDash T$), isomorphism ($\mathfrak{A} \cong \mathfrak{B}$), substructure, homomorphism

**Core definitions** (~8): semantic consistency (has a model), semantic completeness (of a theory: $T \vDash \varphi$ or $T \vDash \neg\varphi$), theory of a structure ($\text{Th}(\mathfrak{A})$), definable set ($\varphi(\mathfrak{A}) = \{a \in |\mathfrak{A}| : \mathfrak{A} \vDash \varphi[a]\}$), elementarily equivalent ($\mathfrak{A} \equiv \mathfrak{B}$), satisfiable, finitely satisfiable

**Model theory supplement** (needed for CP-003, CP-004, CP-011, CP-012, CP-013; ~6 additional definitions): elementary substructure ($\mathfrak{A} \preccurlyeq \mathfrak{B}$), diagram (atomic/elementary), type (complete type over $A$), categoricity ($\kappa$-categorical), ultraproduct

- Core definition (not an axiom): Tarski's recursive satisfaction definition — the inductive clauses defining $\vDash$. This is a **DEF** (recursive definition of satisfaction from PRIM-SEM: structure, assignment, formula) rather than an AX, because it defines a new concept (satisfaction) from existing primitives rather than postulating a constraint.
- Key theorems: isomorphism lemma, elementary equivalence preservation
- PL fragment: truth-value assignment ($v: \text{PropVar} \to \{0,1\}$), truth table semantics, tautology, PL-validity, PL-consequence
- Extension points:
  - EXT-SEM001: Additive — Kripke frames (possible worlds $W$ + accessibility $R$ + valuation at worlds)
  - EXT-SEM002: Replacement — BHK interpretation (intuitionistic: proofs replace truth values)
  - EXT-SEM003: Replacement — many-valued truth sets ($[0,1]$, $\{0, \frac{1}{2}, 1\}$, etc.)
  - EXT-SEM004: Additive — temporal models (time-indexed worlds, flow of time)
- **File**: `taxonomy/DOMAIN-SEMANTICS.md`
- **Registry update**: Add all SEM primitives and definitions

### Step 6: Write DOMAIN-DEDUCTION.md [Hard, ~10 hours]
**Prerequisites**: DEP-DED001: Requires SYN for PRIM-SYN (formula, sentence, substitution). DEP-DED002: Requires BST for PRIM-BST (sequence, set, natural number)
- Primitives (~10): axiom schema, rule of inference, derivation, proof, theorem, provability ($\Gamma \vdash \varphi$), logical axiom, structural rule (weakening, contraction, exchange, cut), sequent ($\Gamma \Rightarrow \Delta$), assumption discharge
- Axioms/Named rules (~3): Modus Ponens (AX-DED001, instance of PRIM "rule of inference"), generalization rule (AX-DED002), identity axiom schema (AX-DED003)
- Definitions (~10): syntactic consistency ($\Gamma \nvdash \bot$), maximal consistent set, deductive closure ($\text{Cn}(\Gamma)$), conservative extension, Hilbert-style proof system, natural deduction system, sequent calculus, tableau system, derived rule, admissible rule
- Proof system architectures as **parameterized variants** of the abstract "proof system" concept:
  - Hilbert-style: axiom schemas + MP + Gen
  - Natural deduction: introduction/elimination rules for each connective/quantifier
  - Sequent calculus: sequents + structural rules + logical rules + cut
  - Tableaux: signed formulas + expansion rules + closure
- Key theorems: deduction theorem (Hilbert), equivalence of proof systems, normalization (ND), cut elimination (SC)
- PL fragment: propositional axioms/rules only (no quantifier rules, no generalization)
- Extension points:
  - EXT-DED001: Additive — modal axiom schemas (K, T, 4, 5, B) and necessitation rule
  - EXT-DED002: Replacement — intuitionistic restrictions (no double-negation elimination, no excluded middle)
  - EXT-DED003: Structural — substructural modifications (drop contraction → linear; drop weakening → relevance)
- **File**: `taxonomy/DOMAIN-DEDUCTION.md`
- **Registry update**: Add all DED primitives and definitions

### Step 7: Write DOMAIN-COMPUTATION.md [Hard, ~10 hours]
**Prerequisites**: DEP-CMP001: Requires BST for PRIM-BST ($\mathbb{N}$, function, sequence, inductive definition)
- Scope: **Computability for logic** — only what's needed for metatheorems (undecidability, incompleteness).
- Non-goals: degrees of unsolvability, priority arguments, complexity theory (P/NP), oracle hierarchies beyond basics.
- Primitives (~12): computable (recursive) function, primitive recursive function, $\mu$-recursion (unbounded minimization), Turing machine, Church-Turing thesis (NOT a theorem — an empirical identification of the informal "effective procedure" with formal computation models), decidable set, semi-decidable (c.e./r.e.) set, halting problem, many-one reducibility ($\leq_m$), diagonalization (technique), universal Turing machine, Gödel numbering / arithmetization
- Definitions (~10): partial function, total function, characteristic function, enumeration, index/program, lambda-definable function, recursive enumerability (equivalent characterizations), productive/creative set, effective enumeration, representability (in a formal theory — cross-references DED+SYN)
- Key theorems: equivalence of computation models (recursive = Turing-computable = lambda-definable), unsolvability of halting problem, Rice's theorem, $s$-$m$-$n$ theorem, recursion theorem (fixed-point)
- Extension points:
  - EXT-CMP001: Additive — oracle computation, arithmetical hierarchy (for relativized computability)
  - EXT-CMP002: Additive — complexity classes (for decision problem analysis)
- **File**: `taxonomy/DOMAIN-COMPUTATION.md`
- **Registry update**: Add all CMP primitives and definitions

### Step 8: Write DOMAIN-SET-FORMAL.md [Hard, ~10 hours]
**Prerequisites**: DEP-SET001: Requires SYN (this is a first-order language $\mathcal{L}_\in$). DEP-SET002: Requires SEM (models of set theory). DEP-SET003: Requires DED (proofs within ZFC). DEP-SET004: Requires BST (naive sets for the metalanguage in which we discuss ZFC).
- Scope: **Set theory for logic** — ZFC axiomatization, ordinals and cardinals for model theory and metatheorems.
- Non-goals: forcing, large cardinals, descriptive set theory, inner models.
- Primitives (~3): set (formal), membership ($\in$ as the sole relation symbol of $\mathcal{L}_\in$), class (informal, for proper classes)
- Axioms (~9, AX not PRIM): extensionality, pairing, union, power set, infinity, separation (comprehension schema), replacement schema, foundation (regularity), choice
- Core definitions (~11): ordinal number (von Neumann), successor ordinal, limit ordinal, $\omega$, transfinite induction, transfinite recursion, cardinal number, cardinality ($|A|$), well-ordering, Zorn's lemma (equivalent to AC), Cantor's theorem ($|A| < |\mathcal{P}(A)|$)
- Deferred definitions (~4, include only if needed by a specific composition pattern): von Neumann hierarchy ($V_\alpha$), $\aleph$ numbers, cofinality, continuum hypothesis. These are needed mainly for advanced model theory (SEM supplement). Include them if CP-003/CP-004 or SEM supplement requires them; otherwise mark as EXT-SET for future expansion.
- Key theorems: well-ordering ↔ Zorn ↔ AC equivalences, transfinite recursion theorem, Cantor's theorem
- Relationship to BST: BST provides naive working sets; SET formalizes them as objects of a first-order theory $\mathcal{L}_\in = \{\in\}$. A model of SET is a structure in the sense of SEM.
- **File**: `taxonomy/DOMAIN-SET-FORMAL.md`
- **Registry update**: Add all SET primitives, axioms, and definitions

### Step 9: Reconciliation Pass [Medium, ~6 hours]
**Read all 6 domain specs together** and systematically:

1. **Redundancy sweep**: Run the 5-step redundancy detection procedure (Section 7)
2. **Cross-reference audit**: For every import in every domain, verify the corresponding export exists
3. **Primitive Registry verification**: Registry matches the union of all domain specs exactly
4. **Ownership disputes**: Apply P1–P5 to any concept flagged by the redundancy sweep
5. **Missing primitives**: Search all DEF/AX/THM entries for concepts used but never defined as PRIM/DEF in any domain
6. **Acyclicity check**: Verify each intra-domain dependency graph is a DAG
7. **Self-audit**: Run the 13-item checklist on every domain spec
8. **Backtrack as needed**: Apply the iteration protocol (Section 8) for any fixes

This is NOT a new document. It's a revision pass on Steps 3–8 + CONVENTIONS.md (Primitive Registry update).

### Step 10: Write CROSS-DOMAIN-MAP.md [Hard, ~8 hours]
- **Primitive Ownership Table**: every primitive and definition across all domains, with columns:
  - ID | Concept | Owner Domain | Referenced By | Boundary Principle | Fragment
- **Domain Dependency Graph**:
  ```
  BST (Level-0 root, no prerequisites)
   ├── SYN (depends: BST)
   │    ├── SEM (depends: SYN, BST)
   │    └── DED (depends: SYN, BST)
   ├── CMP (depends: BST)
   └── SET (depends: SYN, SEM, DED, BST — it's a first-order theory analyzed
            using the metatheoretic apparatus built from SYN+SEM+DED)
  ```
- **Composition Patterns** for major metatheorems:

  | Pattern | Name | Domains | Key Dependencies |
  |---------|------|---------|-----------------|
  | CP-001 | Soundness | DED × SEM | Induction on proof length; each rule preserves truth |
  | CP-002 | Completeness (Gödel 1930) | SEM × DED × BST | Henkin construction, Lindenbaum's lemma |
  | CP-003 | Compactness | SEM × BST | Via CP-002, or via ultraproducts (SEM supplement) |
  | CP-004 | Löwenheim-Skolem | SEM × BST | Downward: Tarski-Vaught test; Upward: CP-003 |
  | CP-005 | Gödel's First Incompleteness | SYN × DED × CMP × BST | Arithmetization, diagonalization, $\omega$-consistency / $\Sigma_1$-soundness |
  | CP-006 | Gödel's Second Incompleteness | SYN × DED × CMP × BST | Formalized provability predicate, derivability conditions |
  | CP-007 | Tarski's Undefinability of Truth | SYN × SEM × CMP | Diagonal lemma, no formula defines its own truth predicate |
  | CP-008 | Church's Undecidability of Validity | SEM × CMP | Reduction from halting problem to validity |
  | CP-009 | Deduction Theorem | DED (internal) | Structural property of Hilbert-style proofs |
  | CP-010 | Cut Elimination (Gentzen) | DED (internal) | Structural property of sequent calculus |
  | CP-011 | Craig's Interpolation | SEM × SYN | If $\vDash \varphi \to \psi$, there exists $\theta$ in shared language |
  | CP-012 | Beth's Definability | SEM × SYN | Implicit definability → explicit definability |
  | CP-013 | Lindström's Theorem | SEM × SYN × BST | Characterizes FOL as maximal logic with compactness + downward L-S |

- **Variant Compatibility Matrix**:

  | Pattern | Classical FOL | Intuitionistic | Modal | Many-valued | SOL (full) |
  |---------|:---:|:---:|:---:|:---:|:---:|
  | CP-001 Soundness | ✓ | ✓ | ✓ | ✓ | ✓ |
  | CP-002 Completeness | ✓ | ✓ ^1 | ✓ ^2 | varies ^3 | ✗ ^4 |
  | CP-003 Compactness | ✓ | ✓ | ✓ | varies ^3 | ✗ |
  | CP-004 Löwenheim-Skolem | ✓ | ✗ ^5 | limited ^6 | varies | ✗ |
  | CP-005/006 Incompleteness | ✓ | ✓ ^7 | N/A ^8 | N/A ^8 | ✓ |
  | CP-010 Cut Elimination | ✓ | ✓ | ✓ | ✓ | limited |
  | CP-011 Interpolation | ✓ | ✓ | varies ^9 | varies | ✓ |
  | CP-013 Lindström | ✓ | N/A ^10 | N/A ^10 | N/A ^10 | N/A ^10 |

  **Footnotes**:
  1. Completeness for intuitionistic logic: holds w.r.t. Kripke semantics, not classical Tarskian semantics
  2. Modal completeness: via canonical model construction; holds for many but not all normal modal logics
  3. Many-valued: depends on the specific semantics; finite-valued logics typically have completeness and compactness; some infinite-valued logics do not
  4. SOL (full): Gödel's completeness theorem fails; only Henkin semantics (effectively first-order) has completeness
  5. Intuitionistic L-S: fails because intuitionistic logic lacks the classical witness property
  6. Modal L-S: limited forms hold for some modal logics but the standard theorem does not transfer directly
  7. Intuitionistic incompleteness: applies to Heyting Arithmetic (HA) — any sufficiently strong consistent intuitionistic theory is incomplete
  8. Modal/Many-valued G1/G2: not applicable in the standard sense — these logics don't typically formalize arithmetic internally
  9. Modal interpolation: Craig interpolation fails for some normal modal logics (e.g., certain extensions of K)
  10. Lindström: characterizes classical FOL specifically; the theorem does not directly apply to non-classical logics

- **File**: `taxonomy/CROSS-DOMAIN-MAP.md`

### Step 11: Write GAP-ANALYSIS.md [Medium, ~5 hours]
- **OpenLogic Coverage Mapping**: every OL topic area → taxonomy domain(s) + composition pattern(s)

  | OL Part | Primary Domain | Secondary | Composition Patterns |
  |---------|---------------|-----------|---------------------|
  | Sets, Functions, Relations | BST | — | — |
  | Propositional Logic | SYN-PL, SEM-PL, DED-PL | — | CP-001(PL), CP-002(PL) |
  | First-Order Logic | SYN, SEM, DED | BST | CP-001 through CP-004 |
  | Model Theory | SEM (+ supplement) | BST, SYN | CP-003, CP-004, CP-011, CP-012, CP-013 |
  | Computability | CMP | BST | — |
  | Turing Machines | CMP | BST | — |
  | Incompleteness | (composition) | SYN, DED, CMP, BST | CP-005, CP-006, CP-007 |
  | Second-Order Logic | SYN-HOT, SEM-HOT | BST | CP-001 (limited) |
  | Lambda Calculus | CMP | SYN | — |
  | Many-valued Logic | SEM-MV, DED-MV | SYN | CP-001 (varies) |
  | Normal Modal Logic | SYN-MOD, SEM-MOD, DED-MOD | BST | CP-001, CP-002 (canonical) |
  | Applied Modal Logic | SYN-MOD, SEM-MOD | BST | — |
  | Intuitionistic Logic | SEM-INT, DED-INT | SYN | CP-001, CP-002 (Kripke) |
  | Counterfactuals | SEM-MOD | SYN-MOD | — |
  | Set Theory | SET | SYN, SEM, DED, BST | — |
  | Methods | (pedagogical, not domain) | — | — |
  | History | (historical, not domain) | — | — |
  | Reference | (reference, not domain) | — | — |

  Also map specific OL sub-content:
  - `content/model-theory/interpolation/` → CP-011, CP-012
  - `content/model-theory/lindstrom/` → CP-013
  - `content/model-theory/models-of-arithmetic/` → SEM + SET (models of Peano Arithmetic, non-standard models)
  - `content/model-theory/basics/` → SEM (core + supplement)

- **Domain sufficiency argument** (adapted from substrateresearch's 10th-substrate gap analysis, 5 evaluation criteria):
  1. **Primitive completeness**: Can every concept in the OL coverage mapping be expressed using primitives from the 5+1 domains? If yes, no new domain is needed.
  2. **Textbook evidence**: Do major logic textbooks (Enderton, Shoenfield, Mendelson, Marker) organize their material within the boundaries of these 5+1 domains? If yes, the decomposition matches expert consensus.
  3. **Composition resistance**: For every proposed 6th domain, can its primitives be shown to be compositions of existing domain primitives? If yes, it is not irreducible.
  4. **Domain vs. infrastructure**: Is the proposed concept a domain (answers an irreducible question) or infrastructure (shared tooling used by multiple domains)? Infrastructure belongs in BST, not a new domain.
  5. **Cross-domain gap evidence**: Are there composition patterns (metatheorems) that require primitives from a domain not in the catalog? If no, the catalog is sufficient.
- **Gap identification**: concepts in OL with no taxonomy home, concepts in taxonomy with no OL coverage
- **File**: `taxonomy/GAP-ANALYSIS.md`

### Step 12: Write README.md [Easy, ~2 hours]
- Project overview and motivation
- The 5+1 domains table (BST + 5 core)
- Full dependency diagram (ASCII art)
- **Guided learning path** with checkpoints:

  **Path 1: Propositional Logic (entry point)**
  1. BST: sets, functions, sequences, induction
     - *Checkpoint*: Can define "a function from A to B" and "proof by induction"
  2. SYN-PL: propositional variables, connectives, formulas (no quantifiers/terms)
     - *Checkpoint*: Can determine if a string is a well-formed propositional formula
  3. SEM-PL: truth-value assignments, truth tables, tautology, PL-consequence
     - *Checkpoint*: Can evaluate truth of a formula under an assignment; can determine if a formula is a tautology
  4. DED-PL: propositional axioms/rules, proofs in PL
     - *Checkpoint*: Can construct a Hilbert-style proof of a propositional tautology
  5. CP-001(PL) + CP-002(PL): soundness and completeness for propositional logic
     - *Checkpoint*: Can state and sketch the proof of PL completeness

  **Bridge: PL → FOL (key conceptual jumps)**
  - PL formulas are built from atomic propositions ($p, q, r$). FOL formulas are built from **terms** (naming objects) and **predicates** (stating properties of objects). This is the shift from "true/false propositions" to "objects with properties and relationships."
  - PL semantics uses truth-value assignments (a function from variables to $\{0,1\}$). FOL semantics uses **structures** (a domain of objects + interpretations of symbols). This is the shift from "which propositions are true?" to "what universe are we talking about?"
  - PL proof systems use only propositional rules. FOL adds **quantifier rules** (generalization, instantiation) that manage the transition between "for all $x$" and specific instances.

  **Path 2: First-Order Logic (lift from PL)**
  6. SYN: terms, quantifiers, formulas, substitution, sentences
     - *Checkpoint*: Can determine free/bound variables; can compute substitution $\varphi[t/x]$
  7. SEM: structures, satisfaction, truth, validity, consequence, models
     - *Checkpoint*: Can evaluate $\mathfrak{A} \vDash \varphi[s]$ for a given structure and assignment
  8. DED: quantifier rules, generalization, FOL proof systems
     - *Checkpoint*: Can construct a proof of a first-order validity
  9. CP-001 through CP-004: soundness, completeness, compactness, Löwenheim-Skolem
     - *Checkpoint*: Can state all four; can sketch Henkin completeness proof; can apply compactness

  **Path 3: Computation & Limits**
  10. CMP: recursive functions, Turing machines, Church-Turing thesis, undecidability
      - *Checkpoint*: Can prove halting problem unsolvable; can explain Church-Turing thesis
  11. CP-005 through CP-008: incompleteness, undefinability, undecidability of validity
      - *Checkpoint*: Can state G1/G2; can explain role of arithmetization and diagonalization

  **Path 4: Formal Set Theory & Extensions**
  12. SET: ZFC, ordinals, cardinals
  13. Extensions: Modal, intuitionistic, many-valued, higher-order (via extension points)

- Index of all files with one-line descriptions
- Relationship to OpenLogic
- **File**: `taxonomy/README.md`

---

## Testing & Verification

Testing operates at three levels: **per-step gates** (pass before proceeding), **structural checks** (mechanically verifiable), and **end-to-end trace tests** (validate the taxonomy works as a system).

### Level 1: Per-Step Acceptance Gates

Each step has specific pass/fail criteria. A step is NOT complete until all its gates pass.

**Step 2 (CONVENTIONS.md) gates:**
- [ ] All 15 global SRC entries present with full bibliographic data
- [ ] All 5 ASM-GLB entries present with justifications
- [ ] All 3 UNK-GLB entries present with impact assessments
- [ ] Primitive Registry table exists (empty, with correct column headers: ID | Concept | Owner Domain | Referenced By)
- [ ] Boundary principles P1–P5 each have ≥1 worked example
- [ ] Normative language (MUST/SHOULD/MAY) definitions present
- [ ] Traceability ID scheme fully specified (domain codes, item types, reserved ranges)
- [ ] Redundancy detection procedure (5 steps) fully written
- [ ] Iteration/backtracking protocol fully written
- [ ] Worked example (AX-DED001) present and matches the format in this plan

**Step 3 (BST) gates:**
- [ ] ≥12 primitives defined (target ~15)
- [ ] Every PRIM has all 7 required fields (description, formal, ownership, source, referenced-by, fragment, example)
- [ ] Dissolution argument present and explains why BST ≠ SET
- [ ] Level-0/Level-1 distinction explicitly documented
- [ ] Primitive Registry in CONVENTIONS.md updated with all BST entries
- [ ] Self-audit checklist (12 items) all pass

**Step 4 (SYN) gates:**
- [ ] ≥15 primitives defined (target ~18)
- [ ] ≥6 definitions defined (target ~8)
- [ ] Imports from BST listed with specific PRIM-BST IDs
- [ ] BST exports table updated to reflect SYN consumption
- [ ] PL fragment items annotated (every PRIM and DEF has Fragment: PL | FOL | both)
- [ ] Formation rules for terms and formulas fully specified as inductive definitions
- [ ] Key theorems include unique readability
- [ ] Extension points cover at least additive (modal) and replacement (higher-order)
- [ ] Partial redundancy check: no SYN entry duplicates a BST entry
- [ ] Self-audit checklist all pass

**Step 5 (SEM) gates:**
- [ ] Core primitives ≤15; if total items >30, triage into core + supplement
- [ ] Tarski satisfaction definition fully specified as recursive DEF
- [ ] Imports from SYN and BST listed with specific IDs
- [ ] SYN and BST exports tables updated
- [ ] PL fragment includes: truth-value assignment, tautology, PL-validity, PL-consequence
- [ ] Extension points cover Kripke (additive), BHK (replacement), many-valued (replacement)
- [ ] Partial redundancy check: no SEM entry duplicates BST or SYN entries
- [ ] Self-audit checklist all pass

**Step 6 (DED) gates:**
- [ ] Proof system architectures (Hilbert, ND, SC, Tableaux) all present as parameterized variants
- [ ] Modus Ponens classified as AX-DED (not PRIM-DED) — instance of PRIM "rule of inference"
- [ ] Syntactic consistency defined here (not in SEM)
- [ ] Imports from SYN and BST listed with specific IDs
- [ ] PL fragment items annotated
- [ ] Extension points cover modal axiom schemas (additive), intuitionistic (replacement), substructural (structural)
- [ ] Partial redundancy check: no DED entry duplicates BST, SYN, or SEM entries
- [ ] Self-audit checklist all pass

**Step 7 (CMP) gates:**
- [ ] Church-Turing thesis explicitly marked as empirical thesis, NOT a theorem
- [ ] Scope limited to "computability for logic" — no complexity theory, no priority arguments
- [ ] Gödel numbering / arithmetization present (bridges CMP to SYN+DED for incompleteness)
- [ ] Representability cross-references DED+SYN
- [ ] Imports from BST listed; does NOT import from SYN/SEM/DED (CMP depends only on BST)
- [ ] Partial redundancy check against all prior domains
- [ ] Self-audit checklist all pass

**Step 8 (SET) gates:**
- [ ] Exactly 3 primitives (set-formal, ∈, class)
- [ ] All 9 ZFC axioms present as AX-SET entries
- [ ] Imports from SYN, SEM, DED, BST all listed (SET is analyzed using the full apparatus)
- [ ] Relationship between BST (naive) and SET (formal) explicitly documented
- [ ] Deferred definitions clearly marked with conditions for inclusion
- [ ] Partial redundancy check against all prior domains
- [ ] Self-audit checklist all pass

**Step 9 (Reconciliation) gates:**
- [ ] Full 5-step redundancy detection run; all flagged items resolved
- [ ] Every import verified against corresponding export
- [ ] Primitive Registry matches exact union of all domain specs
- [ ] All 6 intra-domain dependency graphs verified as DAGs
- [ ] All 6 domain specs pass full 12-item self-audit

**Step 10 (CROSS-DOMAIN-MAP) gates:**
- [ ] Primitive Ownership Table has one row per PRIM and DEF across all domains
- [ ] All 13 composition patterns fully specified with: domains involved, key dependencies, proof sketch reference
- [ ] Variant Compatibility Matrix complete with all footnotes
- [ ] No ownership conflicts in the table

**Step 11 (GAP-ANALYSIS) gates:**
- [ ] Every OL topic area (all 20) maps to ≥1 domain or composition pattern
- [ ] All 5 domain sufficiency criteria evaluated with explicit pass/fail
- [ ] Any gaps identified have a resolution plan (assign to domain, mark as out-of-scope, or flag as future work)

**Step 12 (README) gates:**
- [ ] Guided learning path present with all 4 paths and PL→FOL bridge
- [ ] Dependency diagram matches the actual dependency structure in domain specs
- [ ] All 10 files listed with one-line descriptions

### Level 2: Structural Checks (Mechanically Verifiable)

These can be verified by searching the files. Run after Step 9 and after Step 12.

| # | Check | Method | Pass Criterion |
|---|-------|--------|---------------|
| S1 | ID uniqueness | Search all domain specs for `PRIM-`, `DEF-`, `AX-`, `THM-` prefixes; collect all IDs | No duplicate IDs across the entire taxonomy |
| S2 | Cross-ref integrity | For every string matching `PRIM-{X}NNN` or `DEF-{X}NNN` where {X} ≠ current domain, verify the ID exists in domain {X} | Every cross-domain reference resolves to a real entry |
| S3 | Import/export match | For every domain: collect Imports table; verify each imported ID appears in the source domain's Exports table | 100% match |
| S4 | Registry = specs | Count total PRIM + DEF entries in all domain specs; compare to Primitive Registry row count | Counts match exactly |
| S5 | Fragment annotations | Search every PRIM and DEF entry for "Fragment:" | 100% present |
| S6 | Example coverage | Search every PRIM entry for "Motivating example:" or "example:" | 100% present |
| S7 | Source citations | Search every PRIM and DEF entry for "Source:" | 100% present |
| S8 | Normative on axioms | Search every AX entry for "Normative:" | 100% present |
| S9 | Dissolution arguments | Search each domain spec for "dissolution" or "Dissolution" | Present in all 6 domain specs |
| S10 | PL fragment extraction | Collect all items with Fragment: PL or Fragment: both from SYN+SEM+DED | Forms a self-contained sub-taxonomy (no dangling references to FOL-only items) |

### Level 3: End-to-End Trace Tests

Pick specific concepts and trace them through the full taxonomy to verify the system works as an integrated whole. Run after Step 12.

**Trace Test 1: "Tautology" (PL concept)**
- Start: What OL chapter covers tautologies? → Map via GAP-ANALYSIS
- Taxonomy path: PRIM-SYN (propositional formula, PL fragment) → DEF-SEM (truth-value assignment, PL) → DEF-SEM (tautology = true under all assignments, PL)
- Verify: Every ID in the chain exists. Every dependency is satisfied. Fragment = PL throughout.
- Pass: Complete chain with no broken links or forward references.

**Trace Test 2: "Soundness of FOL" (composition pattern)**
- Start: OL content on soundness → Map via GAP-ANALYSIS → CP-001 in CROSS-DOMAIN-MAP
- Taxonomy path: PRIM-DED (provability $\vdash$) + PRIM-SEM (semantic consequence $\vDash$) → CP-001 (if $\Gamma \vdash \varphi$ then $\Gamma \vDash \varphi$)
- Verify: CP-001 lists DED × SEM as domains. Both domains export the primitives CP-001 depends on. Proof sketch references induction on proof length.
- Pass: All cross-domain references resolve. Both DED and SEM list the relevant exports.

**Trace Test 3: "Gödel's First Incompleteness Theorem" (crown-jewel composition)**
- Start: OL incompleteness chapters → Map via GAP-ANALYSIS → CP-005 in CROSS-DOMAIN-MAP
- Taxonomy path: PRIM-CMP (Gödel numbering, diagonalization) + PRIM-SYN (formula, sentence) + PRIM-DED (provability, consistency) + PRIM-BST (natural number, function) → CP-005
- Verify: CP-005 lists SYN × DED × CMP × BST. Every referenced primitive exists in its claimed domain. Proof sketch references arithmetization and the diagonal lemma.
- Pass: 4-domain trace completes with no broken links.

**Trace Test 4: "Substitution" (contested concept — ownership test)**
- Start: "substitution" appears in SYN, SEM, and DED
- Verify: PRIM or DEF for substitution exists in exactly ONE domain (SYN, per boundary P1). SEM and DED reference it via cross-domain format (DEF-SYN or PRIM-SYN). No local redefinition in SEM or DED.
- Pass: Single owner, zero redefinitions, boundary principle P1 cited.

**Trace Test 5: "Consistency" (twin concept — ownership split test)**
- Start: "consistency" appears in both DED and SEM
- Verify: Syntactic consistency ($\Gamma \nvdash \bot$) owned by DED. Semantic consistency (has a model) owned by SEM. Both have distinct IDs. Cross-reference between them cites CP-001/CP-002.
- Pass: Two distinct entries, two distinct owners, linked by composition pattern, boundary principle P2 cited.

**Trace Test 6: "Set" (Level-0 / Level-1 stratification test)**
- Start: "set" appears in BST and SET
- Verify: BST has PRIM-BST for naive set (Level-0). SET has PRIM-SET for formal set (Level-1). They are explicitly distinguished. BST does NOT axiomatize. SET does axiomatize (9 ZFC axioms). Boundary principle P5 cited.
- Pass: Two distinct entries at different levels, clearly distinguished, P5 cited.

### Failure Protocol

If any test fails:
1. **Per-step gate failure**: Do not proceed to next step. Fix the issue in the current step. Re-run the gate.
2. **Structural check failure**: Log the failing item. Apply the iteration/backtracking protocol (Section 8 of this plan). Fix the source domain spec. Re-run the affected structural checks.
3. **Trace test failure**: Identify which link in the chain broke. Fix the relevant domain spec(s) and cross-domain map. Re-run the trace test and any structural checks that might be affected.

## What Phase 1 Does NOT Do

- Does NOT compress or rewrite OpenLogic content (Phase 3)
- Does NOT produce a compilable LaTeX textbook (Phase 4)
- Does NOT formalize to Metamath/machine-checkable level (future phase)
- Does NOT fully specify non-classical logic variants (noted as extension points; detailed in future phase)
- Does NOT cover advanced recursion theory or advanced set theory (scoped to "for logic" per ASM-GLB005)

## Estimated Scope

- 10 documents
- ~300–600 lines per domain spec, ~200–400 for structural docs
- Total: ~3500–5500 lines
- **Time**: ~60–80 focused hours
  - Step 1: 30 min | Step 2: 5 hrs | Steps 3–8: 8–12 hrs each (~58 hrs) | Step 9: 6 hrs | Step 10: 8 hrs | Step 11: 5 hrs | Step 12: 2 hrs
- Complexity: Steps 3–8 and 10 are **hard**. Steps 2, 9, 11 are **medium**. Steps 1, 12 are **easy**.
