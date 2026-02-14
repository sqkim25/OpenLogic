# Phase 1: Taxonomy

> **📍 You are here: 01-TAXONOMY (Phase 1)**
> Prev: [00-OVERVIEW.md](00-OVERVIEW.md) | Next: [02-MAPPING.md](02-MAPPING.md)
> Template: [06-TEMPLATES.md](06-TEMPLATES.md) | Quality gate: [05-QUALITY-GATES.md](05-QUALITY-GATES.md) (Gate 1)

---

## Goal

Build the primitive taxonomy: a complete inventory of every irreducible concept in the corpus, organized into domains, with explicit dependencies and zero redundancy.

**Input:** The source corpus (searchable), plus a rough sense of its subfields (table of contents is enough).

**Output:**
- One domain specification file per domain (use template in [06-TEMPLATES.md](06-TEMPLATES.md))
- A primitive registry listing every PRIM, DEF, and AX across all domains
- A dependency DAG showing inter-domain prerequisite ordering
- A cross-domain map with composition patterns

**Exit criterion:** Pass Quality Gate 1 (see [05-QUALITY-GATES.md](05-QUALITY-GATES.md)). Every item has a unique ID; the dependency graph is acyclic; every PRIM is truly primitive (cannot be defined from other items in its domain); no concept is owned by more than one domain.

---

## Step 1: Domain Discovery

Identify the irreducible subject areas in the corpus. Each domain answers exactly one governing question that no other domain answers.

### What makes a good domain

A domain is an irreducible subject area if:
1. It has a single governing question that is not a sub-question of any other domain's question.
2. Removing it would leave a gap that no combination of remaining domains can fill.
3. It has primitives that genuinely cannot be defined within any other domain.

### Decision tree for domain identification

```
Is this topic area answerable by an existing domain's governing question?
├── YES → It is NOT a separate domain. Assign its concepts to the existing domain.
└── NO →
    Does removing this topic leave an unfillable gap?
    ├── YES → It IS a candidate domain. Proceed to dissolution test.
    └── NO → It is NOT a domain. It is either redundant or a composition pattern.
```

The **dissolution test**: write a 2-3 sentence argument explaining why this domain cannot be merged into any other. If you cannot write a convincing dissolution argument, the domain is not irreducible.

### Dual examples

**Mathematical logic.** Scan the table of contents and identify the governing questions:
- How are expressions formed? (SYNTAX)
- How is meaning assigned? (SEMANTICS)
- How are truths derived? (DEDUCTION)
- What is effectively decidable? (COMPUTATION)
- What are the foundational axioms of the mathematical universe? (SET THEORY)
- What naive mathematical objects does the metalanguage use? (SET-BOOTSTRAP)

Each question is independent: you can form expressions without assigning meaning, assign meaning without deriving truths, study computability without formal set axioms. Six domains survive the dissolution test.

**Organic chemistry.** Scan an organic chemistry textbook's table of contents:
- What structural features do molecules have? (STRUCTURE)
- How do electrons behave in bonds and reactions? (ELECTRONIC EFFECTS)
- How do 3D arrangements affect properties? (STEREOCHEMISTRY)
- What pathways transform one molecule into another? (REACTION MECHANISMS)
- How do we determine molecular identity? (SPECTROSCOPY)
- How do we construct target molecules from simpler ones? (SYNTHESIS)

Dissolution test for STEREOCHEMISTRY: "3D arrangement of atoms cannot be reduced to electronic effects or structural formulas. Two molecules with identical structural formulas and identical electronic configurations (enantiomers) have different physical and biological properties. Removing stereochemistry leaves an unfillable gap."

### Metalanguage domain

Most corpora have one domain that serves as shared infrastructure. In mathematical logic, this is SET-BOOTSTRAP (naive set theory). In organic chemistry, this is STRUCTURE (atoms, bonds, molecular formulas). Identify this root domain first. It has no prerequisites; all other domains import from it.

### How many domains?

Aim for 4-8 domains. Fewer than 4 usually means you have not separated concerns. More than 8 usually means some domains are sub-topics that should be merged. If you find yourself at 9+, look for domains that can be combined under a single governing question.

### Action items

1. Read the corpus table of contents end to end.
2. List candidate domains as governing questions.
3. Apply the dissolution test to each candidate.
4. Identify the metalanguage/root domain.
5. Write a 1-paragraph domain intent for each survivor.

---

## Step 2: Dependency Graph

Establish the prerequisite ordering between domains. This determines the order in which domain specs must be written: write prerequisites first.

### Constructing the DAG

For each pair of domains (A, B), ask: "Does defining the primitives of A require concepts from B?" If yes, draw an edge B -> A (B is a prerequisite of A).

### Acyclicity check

The dependency graph MUST be a directed acyclic graph (DAG). If you find a cycle (A depends on B and B depends on A), one of the following is true:
- One direction is a genuine dependency and the other is merely a cross-reference (resolve by removing the weaker edge).
- The two domains should be merged into one.
- The cycle involves a composition pattern, not a definitional dependency (resolve by documenting the pattern separately).

### Dual examples

**Mathematical logic:**
```
BST (root, no prerequisites)
 +-- SYN (depends: BST)
 |    +-- SEM (depends: SYN, BST)
 |    +-- DED (depends: SYN, BST)
 +-- CMP (depends: BST)
 +-- SET (depends: SYN, SEM, DED, BST)
```

SEM depends on SYN because you must have formulas before you can assign them truth values. SET depends on SYN, SEM, and DED because formal set theory is a first-order theory analyzed using all three.

**Organic chemistry:**
```
STRUCTURE (root, no prerequisites)
 +-- ELECTRONIC EFFECTS (depends: STRUCTURE)
 |    +-- REACTION MECHANISMS (depends: ELECTRONIC EFFECTS, STRUCTURE, STEREOCHEMISTRY)
 +-- STEREOCHEMISTRY (depends: STRUCTURE)
 +-- SPECTROSCOPY (depends: STRUCTURE, ELECTRONIC EFFECTS)
 +-- SYNTHESIS (depends: REACTION MECHANISMS, STEREOCHEMISTRY)
```

REACTION MECHANISMS depends on STEREOCHEMISTRY because S_N2 vs S_N1 pathways are determined by 3D accessibility. SYNTHESIS depends on REACTION MECHANISMS because retrosynthetic analysis chains reaction steps.

### Action items

1. For each domain pair, determine if a prerequisite relationship exists.
2. Draw the DAG. Verify it is acyclic.
3. Determine authoring order: topological sort of the DAG.

---

## Step 3: Item Enumeration

Populate each domain with its primitives (PRIM), definitions (DEF), and axioms (AX). Work through domains in dependency order (topological sort from Step 2).

### PRIM vs DEF decision tree

For each concept in a domain, determine whether it is a primitive or a definition:

```
Can this concept be defined using only previously listed items in this domain
(plus imports from prerequisite domains)?
├── YES → It is a DEF. Write its definition in terms of those items.
└── NO →
    Is it taken as given (undefined) within this domain?
    ├── YES → It is a PRIM. Document it as a primitive notion.
    └── NO →
        Is it an axiom (postulated without proof)?
        ├── YES → It is an AX.
        └── NO → It belongs to a different domain. Reassign it.
```

### Dual examples

**Mathematical logic (SYNTAX domain):**
- "Symbol" -- cannot be defined from anything else in SYN. It is PRIM-SYN001.
- "Formula" -- cannot be defined from simpler SYN concepts alone (it is the core inductive object). It is PRIM-SYN012.
- "Substitution" -- defined using variable, term, formula, and free occurrence (all already listed). It is DEF-SYN001.
- "Formation rules for formulas" -- postulated as the inductive definition. It is AX-SYN002.

**Organic chemistry (STRUCTURE domain):**
- "Atom" -- cannot be defined from other STRUCTURE concepts. It is PRIM.
- "Covalent bond" -- cannot be defined from other STRUCTURE concepts without invoking electronic effects (which is a separate domain). It is PRIM within STRUCTURE (the shared bonding concept), with the electronic explanation owned by ELECTRONIC EFFECTS.
- "Degree of unsaturation" -- defined from molecular formula (count of carbons, hydrogens, etc.). It is DEF.
- "Octet rule" -- postulated as a governing principle for bonding. It is AX.

### Target counts

Aim for the following ranges per domain. These are guidelines, not hard limits:

| Item type | Target per domain | Warning sign |
|-----------|------------------|--------------|
| PRIM | 8-20 | < 5 means the domain may be too narrow; > 25 means split it |
| DEF | 5-20 | > 30 means check for redundancy or scope creep |
| AX | 0-10 | > 15 means check if some are derivable (should be THM) |

### Contested concepts

When a concept seems to belong to two domains, apply the boundary principles from Step 5. Pre-analyze the split and document both the syntactic and semantic (or otherwise domain-specific) versions with distinct IDs and a cross-reference.

### Action items

1. For each domain (in dependency order), list every concept.
2. Apply the PRIM/DEF/AX decision tree to each concept.
3. Assign a unique ID to each item using the scheme: `{TYPE}-{DOMAIN}{NUMBER}` (e.g., PRIM-SYN001, DEF-CMP003).
4. Check target counts. Investigate domains that fall outside the ranges.

---

## Step 4: Item Specification

Write a full specification for every PRIM, DEF, and AX. Each entry MUST include all of the following fields:

### Required fields

| Field | Description |
|-------|------------|
| **ID** | Unique identifier: `{TYPE}-{DOMAIN}{NUMBER}` |
| **Name** | Short, descriptive name |
| **Description** | Natural language explanation (at least 1 complete sentence) |
| **Formal** | LaTeX math notation for the formal statement or characterization |
| **Depends** | List of item IDs this entry depends on (prerequisite items) |
| **Ownership** | `OWNS` if this domain owns the concept; otherwise cross-reference |
| **Source** | SRC reference to authoritative textbook/paper |
| **Referenced by** | List of domains that import or reference this item |
| **Fragment** | Which logic fragment this applies to: `PL`, `FOL`, or `both` (domain-specific variant for non-logic corpora) |
| **Motivating example** | A concrete instance that makes the abstract concept tangible |

### Specification standard

Every entry must satisfy this test: a reader with one semester of background in the field can parse the formal statement after reading the description and example. If not, the description is insufficient.

### Dual examples

**Mathematical logic (fully specified entry):**

> - PRIM-SEM007: **Satisfaction**
>   - Description: The fundamental semantic relation. $\mathfrak{A} \vDash \varphi[s]$ means "the structure $\mathfrak{A}$ satisfies the formula $\varphi$ under the variable assignment $s$." This is the bridge between syntax and meaning: it assigns a truth value to every formula relative to a structure and assignment.
>   - Formal: $\mathfrak{A} \vDash \varphi[s]$ defined recursively on the structure of $\varphi$ (see DEF-SEM001 for the full Tarski definition).
>   - Depends: PRIM-SEM001 (structure), PRIM-SEM004 (variable assignment), PRIM-SYN012 (formula)
>   - Ownership: OWNS
>   - Source: SRC-GLB001 (Enderton Ch. 2), SRC-GLB004 (Tarski 1935)
>   - Referenced by: DED, CMP
>   - Fragment: both
>   - Motivating example: Let $\mathfrak{A} = (\mathbb{N}, <)$ and $s(x) = 3$. Then $\mathfrak{A} \vDash (x < S(S(S(S(0)))))[s]$ because $3 < 4$.

**Organic chemistry (fully specified entry):**

> - PRIM-STR003: **Functional Group**
>   - Description: A specific grouping of atoms within a molecule that determines the molecule's characteristic chemical reactions. Functional groups are the basis for classifying organic compounds into families (alcohols, aldehydes, carboxylic acids, etc.).
>   - Formal: A functional group is a connected subgraph of the molecular graph containing at least one heteroatom or multiple bond.
>   - Depends: PRIM-STR001 (atom), PRIM-STR002 (covalent bond)
>   - Ownership: OWNS
>   - Source: Clayden et al., *Organic Chemistry*, Ch. 2
>   - Referenced by: ELECTRONIC EFFECTS, REACTION MECHANISMS, SPECTROSCOPY
>   - Fragment: N/A
>   - Motivating example: The hydroxyl group (-OH) defines alcohols. Ethanol (CH3CH2OH) and methanol (CH3OH) both contain -OH and share characteristic reactions (dehydration, oxidation).

### Action items

1. For each item from Step 3, write all required fields.
2. Verify the Depends field forms an acyclic graph within the domain.
3. Verify every cross-domain reference uses the full `{TYPE}-{DOMAIN}{NUMBER}` format.

---

## Step 5: Boundary Principles

Boundary principles resolve ownership disputes. When a concept could belong to multiple domains, apply these principles in order until ownership is determined.

### P1 -- Formation vs. Interpretation

If a concept is definable purely via symbol manipulation without any notion of truth or meaning, it belongs to the formation/structural domain. If it requires interpretation or truth values, it belongs to the semantic domain.

- **Logic example:** "Formula" is pure symbol manipulation (SYN). "Satisfaction" requires a structure and truth values (SEM).
- **Chemistry example:** "Molecular formula" is pure atom counting (STRUCTURE). "Acidity" requires electron density interpretation (ELECTRONIC EFFECTS).
- **Failure mode:** Concepts with both syntactic and semantic versions (e.g., "consistency"). Resolution: create two entries with distinct IDs and a documented cross-reference.
- **When stuck:** Ask: "Can I define this concept without ever mentioning truth, meaning, or interpretation?" If yes, it belongs to the formation domain.

### P2 -- Derivation vs. Truth

Syntactic consequence (derivation, proof) belongs to the deduction/procedure domain. Semantic consequence (truth preservation) belongs to the semantic domain. Results connecting them are composition patterns, not owned by either domain.

- **Logic example:** "Proof" belongs to DED. "Validity" belongs to SEM. "Soundness" (every provable formula is valid) is a composition pattern connecting DED and SEM.
- **Chemistry example:** "Reaction mechanism" (step-by-step electron movement) belongs to REACTION MECHANISMS. "Thermodynamic stability" (energy state of products) belongs to a thermodynamics domain. Predicting product ratios from mechanism + thermodynamics is a composition pattern.
- **Failure mode:** Confusing a metatheorem for a primitive. Resolution: if a result requires concepts from two domains, it is a composition pattern (Step 6), not a primitive of either.
- **When stuck:** Ask: "Does this concept involve a step-by-step procedure, or a global property of the result?" Procedures go to derivation; global properties go to semantics/interpretation.

### P3 -- Effective vs. Abstract

If a concept inherently involves algorithms, effective procedures, or decidability, it belongs to the computation domain. If it involves arbitrary existence (not necessarily constructive), it belongs to the set-theoretic or semantic domain.

- **Logic example:** "Decidable set" belongs to CMP. "Power set" belongs to BST (naive) or SET (formal).
- **Chemistry example:** "Computational prediction of NMR shifts" belongs to a computational chemistry domain. "Molecular orbital" as an abstract wavefunction belongs to ELECTRONIC EFFECTS.
- **Failure mode:** Calling something "computable" without specifying the computation model. Resolution: effective procedures require an explicit model (Turing machine, recursive function) or Church-Turing thesis.
- **When stuck:** Ask: "Does this concept require an algorithm to exist, or does it merely assert existence?" Algorithms go to computation; mere existence goes elsewhere.

### P4 -- One Owner, Many References

Every concept has exactly one owning domain. Other domains reference it by its full cross-domain ID, never redefine it.

- **Logic example:** "Substitution" is owned by SYN (DEF-SYN001). SEM and DED reference it as DEF-SYN001, never create their own substitution definition.
- **Chemistry example:** "Chirality" is owned by STEREOCHEMISTRY. REACTION MECHANISMS references it when discussing stereospecific reactions, but does not redefine it.
- **Failure mode:** Two domains each defining "the same thing with different notation." Resolution: pick one owner; the other imports. Use the governing question test: which domain's question does this concept answer?
- **When stuck:** Ask: "Which domain's governing question does this concept most directly answer?" That domain owns it.

### P5 -- Metalanguage vs. Object Language

Naive metalanguage concepts (used to talk about the formal system) belong to the bootstrap/root domain. Formal concepts (studied as objects within the formal system) belong to their respective object-level domains.

- **Logic example:** "The set of all formulas" is a naive collection (BST). "The axiom of infinity" is a formal statement in ZFC (SET).
- **Chemistry example:** "Drawing a structural formula on paper" is a representational convention (STRUCTURE as metalanguage). "The molecular orbital as a quantum-mechanical object" is a formal concept (ELECTRONIC EFFECTS).
- **Failure mode:** Conflating the metalanguage use and the object-language use of the same term (e.g., "set" at Level-0 vs Level-1). Resolution: assign distinct IDs at each level and document the relationship explicitly.
- **When stuck:** Ask: "Am I using this concept to build the formalism, or is this concept a subject of the formalism?" Builder concepts go to the metalanguage domain.

---

## Step 6: Composition Patterns

Composition patterns document metatheorems and cross-domain results that live at the intersection of two or more domains. They are NOT owned by any single domain.

### When to create a composition pattern

Create a composition pattern when a result:
1. Requires primitives or definitions from two or more domains.
2. Cannot be stated using the vocabulary of a single domain.
3. Connects domain-specific concepts in a way that reveals structural relationships.

### Template

```
CP-NNN: **{Pattern Name}**
- Domains: {DomainCode} x {DomainCode} [x ...]
- Statement: [semi-formal statement with LaTeX]
- Natural language: [explanation, >= 1 sentence]
- Key dependencies: [PRIM/DEF/AX IDs from each involved domain]
- Proof sketch: [outline or reference]
- Source: SRC reference
- Significance: [why this matters for the taxonomy]
```

### Dual examples

**Mathematical logic:**

> CP-001: **Soundness Theorem**
> - Domains: DED x SEM
> - Statement: If $\Gamma \vdash \varphi$, then $\Gamma \vDash \varphi$.
> - Natural language: Everything provable is true. If a formula can be derived from a set of assumptions using the proof system, then it is a semantic consequence of those assumptions.
> - Key dependencies: PRIM-DED006 (provability), PRIM-SEM010 (logical consequence)
> - Proof sketch: By induction on derivation length. Base: axioms are valid (check each schema). Step: each rule of inference preserves truth.
> - Source: SRC-GLB001 (Enderton Ch. 2)
> - Significance: Guarantees the proof system never produces false results. Without soundness, derivation is meaningless.

**Organic chemistry:**

> CP-OC001: **Curtin-Hammett Principle**
> - Domains: REACTION MECHANISMS x STEREOCHEMISTRY
> - Statement: When two conformational isomers interconvert rapidly relative to their rates of reaction, the product ratio is determined by the difference in transition state energies, not by the conformer population ratio.
> - Natural language: For fast-equilibrating conformers, the product distribution depends on which conformer reacts faster, not on which conformer is more abundant.
> - Key dependencies: PRIM-STEREO (conformational isomer), PRIM-MECH (transition state energy)
> - Proof sketch: Rate equations with pre-equilibrium approximation.
> - Source: Seeman, *Chem. Rev.* 1983
> - Significance: Connects 3D molecular arrangement (stereochemistry) with reaction pathway energetics (mechanism). Without this pattern, stereochemical predictions from conformer populations alone are wrong.

### Action items

1. Identify all results that require concepts from 2+ domains.
2. Write each as a composition pattern using the template.
3. Assign sequential IDs: CP-001, CP-002, etc.
4. Verify that every dependency listed in the pattern exists in its owning domain's registry.

---

## Quality Gate 1

Before proceeding to Phase 2 ([02-MAPPING.md](02-MAPPING.md)), verify all of the following. Every item must pass.

- [ ] **Unique IDs.** Every PRIM, DEF, AX, and CP has a unique identifier following the `{TYPE}-{DOMAIN}{NUMBER}` scheme.
- [ ] **Acyclic DAG.** The inter-domain dependency graph has no cycles. Verify by topological sort.
- [ ] **Primitives are primitive.** For every PRIM, confirm it cannot be defined from other items in its domain plus imports. If it can, demote it to DEF.
- [ ] **Single ownership.** No concept appears as a PRIM or DEF in more than one domain. Run an alphabetical cross-domain sort and flag duplicates.
- [ ] **Complete specification.** Every item has all required fields (ID, name, description, formal, depends, ownership, source, referenced-by, fragment, example).
- [ ] **Dissolution arguments.** Every domain has a non-trivial dissolution argument explaining why it cannot be merged into another.
- [ ] **Boundary principles applied.** Every contested concept has been resolved using P1-P5, with the resolution documented.
- [ ] **Intra-domain acyclicity.** Within each domain, the dependency ordering (PRIM before DEF, earlier DEF before later DEF) is acyclic.
- [ ] **Self-audit passed.** Each domain spec passes the validation rules in [06-TEMPLATES.md](06-TEMPLATES.md) §S1.
- [ ] **Composition patterns complete.** Every known cross-domain result is documented as a CP with full template fields.

If any item fails, fix it before proceeding. Backtracking within Phase 1 is expected. If Gate 1 reveals that a domain should be split or merged, do so and re-run the gate.

---

## AI Prompt Block

Copy and paste the following prompt to start Phase 1 with an AI assistant. Replace bracketed placeholders with your corpus details.

````
You are helping me build a primitive taxonomy for a knowledge compression project.

**Corpus:** [name of corpus, e.g., "OpenLogic textbook, ~1,200 pages of mathematical logic"]
**Format:** [format, e.g., "LaTeX source files in content/ directory"]
**Rough subfields:** [list from table of contents, e.g., "propositional logic, first-order logic, model theory, computability, set theory, incompleteness"]

Perform Phase 1 — Taxonomy — following these steps:

1. **Domain discovery.** Read the table of contents and identify candidate domains.
   Each domain must answer exactly one irreducible governing question. Write a
   dissolution argument for each candidate. Aim for 4-8 domains.

2. **Dependency graph.** Determine prerequisite relationships between domains.
   Draw the DAG. Verify it is acyclic. Identify the metalanguage/root domain.

3. **Item enumeration.** For each domain (in dependency order), enumerate every
   primitive (PRIM), definition (DEF), and axiom (AX). Apply the PRIM vs DEF
   decision tree. Assign unique IDs using the scheme {TYPE}-{DOMAIN}{NUMBER}.

4. **Item specification.** For each item, write: description, formal notation,
   depends, ownership, source, referenced-by, fragment, motivating example.

5. **Boundary principles.** Resolve any contested concepts using P1-P5:
   P1 (Formation vs Interpretation), P2 (Derivation vs Truth),
   P3 (Effective vs Abstract), P4 (One Owner Many References),
   P5 (Metalanguage vs Object Language).

6. **Composition patterns.** Identify all cross-domain results and document
   each as a composition pattern (CP-NNN) with domains, statement, dependencies,
   proof sketch, and significance.

7. **Quality Gate 1.** Verify: unique IDs, acyclic DAG, primitives are truly
   primitive, single ownership, complete specifications, dissolution arguments,
   boundary resolutions, intra-domain acyclicity, self-audit, and composition
   pattern completeness.

Output each domain spec as a separate file. Output the primitive registry and
dependency DAG in a conventions/cross-domain-map file.
````
