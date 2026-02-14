# CONVENTIONS v0.1

This document establishes the cross-domain conventions, traceability infrastructure, and quality standards governing all chemistry taxonomy files. It MUST be read before any domain spec and MUST be complete before any domain spec is authored.

---

## 1. Foundational Principles

### Principle 1: Closed Domain Catalog, Open Pattern Catalog

The **domain catalog is closed**: 5 domains (COM, STR, NRG, CHG, SCL). No 6th domain will be added. Any concept that appears to need a new domain MUST be resolved by: (a) assigning it to an existing domain via boundary principles (Section 5), or (b) documenting it as a composition pattern (Section 11).

The **composition pattern catalog is open**: new cross-domain results, application deployment patterns, and interdisciplinary connections can be added indefinitely without restructuring the taxonomy.

New chemistry topics (organic chemistry, biochemistry, materials science, environmental chemistry) are **applications of existing domains**, not new domains. They deploy primitives from COM, STR, NRG, CHG, and SCL in combination, documented as composition patterns or application deployment patterns (Section 6).

### Principle 2: Reasoning-Move Standard

Every PRIM is a deployable cognitive operation statable as: **"Given [input], [operation] to determine [output]."** Every DEF is defined from previously listed PRIMs and DEFs. All items include a real-world hook grounding the concept in everyday, non-major contexts.

This standard ensures the taxonomy is not a topic list but a toolkit of transferable reasoning moves. A student who masters a PRIM can deploy it across contexts without re-learning the underlying logic.

### Principle 3: One Owner, Zero Redundancy

Every concept has **exactly one owning domain**. Other domains reference it, never redefine it. This is enforced by:
- Boundary principles P1--P5 (Section 5)
- Primitive Registry (Section 9)
- Redundancy detection procedure (Section 7)
- Self-audit checklists (Section 12)

### Principle 4: Non-Majors Calibration

Mathematical sophistication is capped: **no calculus**. Only algebra and proportional reasoning are assumed. Every item carries a **Tier annotation**:

| Tier | Meaning | Criterion |
|------|---------|-----------|
| **C** (Core) | Essential for chemical literacy | Required for every student in a 14-week semester |
| **E** (Enrichment) | Valuable but cuttable | Can be omitted without breaking dependency chains |

Enrichment items MUST NOT be prerequisites for Core items. The Core tier alone MUST form a self-contained, dependency-complete sub-taxonomy.

---

## 2. No Metatheory Stratification Needed

Unlike the logic taxonomy, which requires a two-level metatheory stratification (naive metalanguage vs. formal object language), chemistry for non-majors operates at a single conceptual level. There is no meta/object-level distinction to manage: chemical reasoning is about substances, structures, energies, and transformations directly. No bootstrap domain is needed.

The closest analogy is that SCL (Scale) bridges between submicroscopic and macroscopic descriptions, but this is a **perspective shift within chemistry**, not a metalanguage/object-language stratification. Both perspectives describe the same physical reality at different scales.

---

## 3. Traceability ID Scheme

### Domain Codes (unambiguous, 3-letter)

| Code | Domain |
|------|--------|
| COM | Composition |
| STR | Structure |
| NRG | Energy |
| CHG | Change |
| SCL | Scale |
| GLB | Global (shared references in this document) |

### Item Type Prefixes

| Prefix | Meaning | Example |
|--------|---------|---------|
| PRIM | Primitive reasoning move (foundational) | PRIM-COM001 |
| DEF | Definition (built from PRIMs/DEFs) | DEF-STR003 |
| AX | Axiom (minimal; conservation laws only) | AX-COM001 |
| SRC | Source reference | SRC-GLB001 (global) or SRC-COM001 (domain-specific) |
| ASM | Assumption | ASM-GLB001 (global) or ASM-NRG001 (domain-specific) |
| UNK | Unknown / open question | UNK-GLB002 |
| DEP | Dependency on another domain | DEP-CHG001 |
| EXT | Extension point | EXT-STR001 |

### ID Format

All IDs follow the pattern `{TYPE}-{CODE}{NNN}`, e.g., `PRIM-COM001`, `DEF-STR003`, `AX-COM001`.

### Cross-Domain Reference Format

References use the full format `{ItemType}-{DomainCode}{Number}`. When domain A references domain B's primitive, write `PRIM-NRG002` (not a local alias). The owning domain MUST list it in Exports; the referencing domain MUST list it in Imports.

### Source Reference Scoping

Global SRC entries (SRC-GLB001 through SRC-GLBNNN) live in this document and are shared across all domain specs. Domain-specific SRC entries (SRC-{D}NNN) live in their domain spec for sources relevant only to that domain. Domain specs MAY cite global SRCs by their GLB ID.

### ID Stability

IDs are permanent once assigned. Deprecated items use `DEPRECATED-{original-ID}` with pointer to replacement. IDs MUST NOT be renumbered across versions.

### Document Versioning

Domain specs use semantic versioning (v0.1 to v0.2 for non-breaking additions, v1.0 for first stable release). Breaking changes (removing/renaming primitives) require v(N+1).0 and a migration note listing all affected cross-references.

---

## 4. Normative Language

Per RFC 2119, used at full strength throughout all taxonomy documents:

- **MUST** / **MUST NOT** = structural requirement; violation means the taxonomy is broken or the reasoning move is misspecified
- **SHOULD** / **SHOULD NOT** = strong convention; deviation requires documented justification
- **MAY** = optional; extension point or instructor-specific

---

## 5. Boundary Principles (Ownership Disambiguation)

When a concept could belong to multiple domains, these principles resolve ownership:

| Principle | Rule | Example |
|-----------|------|---------|
| **P1 -- Identity vs. Arrangement** | Counting atoms/protons without geometry --> COM. 3D arrangement --> STR. | "molecular formula" --> COM. "molecular shape" --> STR. |
| **P2 -- Energy vs. Transformation** | Energy concepts (storage, transfer, favorability) --> NRG. Transformation concepts (what reacts, products, rate, equilibrium) --> CHG. | "enthalpy" --> NRG. "equilibrium" --> CHG. |
| **P3 -- Molecular vs. Macroscopic** | Individual molecules --> STR/NRG/CHG. Bridging to bulk --> SCL. | "H-bond" --> STR. "boiling point" --> SCL (via CP-001). |
| **P4 -- One Owner, Many References** | Every concept owned by one domain. Others import. | "activation energy" owned by NRG. CHG references PRIM-NRG006. |
| **P5 -- Qualitative vs. Quantitative** | Qualitative reasoning pattern --> domain PRIM/DEF. Measurement/units --> SCL. | "polarity" --> STR. "dipole moment measurement" --> SCL. |

### Pre-Analyzed Ownership Splits for Contested Concepts

| Concept | NRG Version (Owner) | CHG Version (Owner) | Connection |
|---------|---------------------|---------------------|------------|
| Activation energy | PRIM-NRG006 (energy barrier concept) | DEF-CHG001 (catalyst lowers it) | CHG imports PRIM-NRG006 |
| Spontaneity | PRIM-NRG005 (thermodynamic favorability) | CHG uses for reaction direction | CHG imports PRIM-NRG005 |
| Bond energy | PRIM-NRG002 (energy stored in bonds) | CHG uses for reaction energetics | CHG imports PRIM-NRG002 |
| Equilibrium | NRG explains WHY (entropy drives) | PRIM-CHG003 (HOW it behaves dynamically) | CHG owns; NRG provides driving force |

**Governing rule**: NRG owns energy concepts (what energy is, how it is stored, whether a process is favorable). CHG owns transformation concepts (what reacts, what forms, how fast, how far). When a transformation uses energy reasoning, CHG imports from NRG.

---

## 6. Extension Protocol

New chemistry topics are NOT new domains. They are applications that deploy primitives from existing domains. The extension protocol works as follows:

| Application Area | Deployed Domains | Example Primitives Used |
|-----------------|-----------------|------------------------|
| Organic chemistry | COM + STR + CHG | PRIM-COM007 (valence), DEF-STR007 (carbon backbone), DEF-STR005 (isomers) |
| Biochemistry | STR + NRG + CHG | PRIM-STR004 (IMF hierarchy), PRIM-NRG002 (bond energy), PRIM-CHG004 (rate) |
| Environmental chemistry | CHG + SCL | PRIM-CHG005 (acid-base), PRIM-SCL003 (concentration), DEF-SCL002 (ppm/ppb) |
| Materials science | STR + NRG + SCL | DEF-STR009 (metallic structure), PRIM-NRG001 (energy tracking), PRIM-SCL004 (emergent) |

To document a new application area:
1. Identify which existing PRIMs and DEFs from COM, STR, NRG, CHG, SCL are deployed
2. If a new composition pattern is needed, add it using the CP-NNN template (Section 11)
3. DO NOT create new domain codes or domain specs
4. Document the application as a deployment pattern in COMPOSITION-PATTERNS.md

---

## 7. Redundancy Detection Procedure

Run **after completing each domain spec** (partial check against existing registry) and **in full during the Reconciliation Pass**:

1. **Alphabetical cross-domain sort**: Export all PRIM and DEF entries from all domains into a single list sorted by concept name. Flag any name appearing in more than one domain.
2. **For each flagged name**: Apply boundary principles P1--P5. Determine: is this genuinely two different concepts (like energy barrier vs. catalyst mechanism), or an ownership violation (same concept defined twice)?
3. **If two different concepts**: Ensure both have distinct names, distinct IDs, and a documented cross-reference linking them via a composition pattern or import.
4. **If ownership violation**: Remove the duplicate from the non-owning domain. Replace with a REFERENCES annotation pointing to the owner's ID.
5. **Registry update**: After resolution, update the Primitive Registry (Section 9).

---

## 8. Iteration and Backtracking Protocol

Writing domain specs is not purely linear. When Step N reveals a needed change to Step M (M < N):

1. **Identify the change**: What primitive/definition in domain M needs to be added, modified, or have its ownership changed?
2. **Update domain M's spec**: Make the change, update the Primitive Registry, increment version (v0.1 to v0.2).
3. **Cascade check**: Search all domain specs written between M and N for references to the changed item. Update cross-references.
4. **Re-run self-audit**: Run the 10-item checklist on both the modified domain M and any domains with updated cross-references.
5. **Continue**: Resume Step N with the fix in place.

The Reconciliation Pass is the scheduled iteration point, but backtracking MAY happen at any step.

---

## 9. Primitive Registry

Single source of truth for all primitives and definitions across the taxonomy. Updated after each domain spec is completed. Total: 62 items (32 PRIM + 30 DEF).

### COM -- Composition (8 PRIM + 5 DEF = 13 items)

| ID | Concept | Owner | Referenced By | Tier |
|----|---------|-------|---------------|------|
| PRIM-COM001 | Atomic composition analysis | COM | STR, NRG, SCL, CHG | C |
| PRIM-COM002 | Elemental identity | COM | STR, NRG | C |
| PRIM-COM003 | Periodic position reasoning | COM | STR, NRG | C |
| PRIM-COM004 | Substance classification | COM | CHG | C |
| PRIM-COM005 | Chemical formula reading | COM | SCL, CHG | C |
| PRIM-COM006 | Conservation of atoms | COM | CHG | C |
| PRIM-COM007 | Valence electron reasoning | COM | STR, CHG | C |
| PRIM-COM008 | Causal chain reasoning | COM | STR, NRG, CHG, SCL | C |
| DEF-COM001 | Isotope | COM | CHG | C |
| DEF-COM002 | Ion | COM | STR, CHG | C |
| DEF-COM003 | Molecular vs empirical formula | COM | SCL | E |
| DEF-COM004 | Percent composition | COM | SCL | E |
| DEF-COM005 | Electronegativity | COM | STR | C |

### STR -- Structure (5 PRIM + 10 DEF = 15 items)

| ID | Concept | Owner | Referenced By | Tier |
|----|---------|-------|---------------|------|
| PRIM-STR001 | Bond type classification | STR | NRG, CHG | C |
| PRIM-STR002 | Bond polarity reasoning | STR | NRG, CHG | C |
| PRIM-STR003 | Molecular shape reasoning | STR | CHG, SCL | C |
| PRIM-STR004 | Intermolecular force hierarchy | STR | SCL, CHG | C |
| PRIM-STR005 | Structure-to-property inference | STR | SCL, CHG | C |
| DEF-STR001 | Lewis structure | STR | CHG | C |
| DEF-STR002 | Molecular polarity | STR | SCL, CHG | C |
| DEF-STR003 | Hydrogen bond | STR | SCL, CHG | C |
| DEF-STR004 | "Like dissolves like" | STR | SCL | C |
| DEF-STR005 | Isomer recognition | STR | CHG | C |
| DEF-STR006 | Phase from IMF balance | STR | SCL | C |
| DEF-STR007 | Carbon backbone reasoning | STR | CHG | C |
| DEF-STR008 | Polymer reasoning | STR | SCL | C |
| DEF-STR009 | Metallic structure | STR | -- | E |
| DEF-STR010 | Water as solvent | STR | CHG, SCL | C |

### NRG -- Energy (6 PRIM + 5 DEF = 11 items)

| ID | Concept | Owner | Referenced By | Tier |
|----|---------|-------|---------------|------|
| PRIM-NRG001 | Energy tracking | NRG | CHG | C |
| PRIM-NRG002 | Bond energy reasoning | NRG | CHG | C |
| PRIM-NRG003 | Exo/endothermic classification | NRG | CHG | C |
| PRIM-NRG004 | Entropy reasoning | NRG | CHG | C |
| PRIM-NRG005 | Spontaneity reasoning | NRG | CHG | C |
| PRIM-NRG006 | Activation energy reasoning | NRG | CHG | C |
| DEF-NRG001 | Heat vs temperature | NRG | SCL | C |
| DEF-NRG002 | Specific heat capacity | NRG | SCL | C |
| DEF-NRG003 | Enthalpy change (delta-H) | NRG | CHG | C |
| DEF-NRG004 | Free energy (conceptual) | NRG | CHG | E |
| DEF-NRG005 | Calorie/joule | NRG | SCL | C |

### CHG -- Change (7 PRIM + 5 DEF = 12 items)

| ID | Concept | Owner | Referenced By | Tier |
|----|---------|-------|---------------|------|
| PRIM-CHG001 | Equation reading and balancing | CHG | SCL | C |
| PRIM-CHG002 | Reaction type recognition | CHG | -- | C |
| PRIM-CHG003 | Equilibrium reasoning | CHG | SCL | C |
| PRIM-CHG004 | Rate reasoning | CHG | -- | C |
| PRIM-CHG005 | Acid-base reasoning | CHG | SCL | C |
| PRIM-CHG006 | Oxidation-reduction reasoning | CHG | SCL | C |
| PRIM-CHG007 | Nuclear change reasoning | CHG | SCL | E |
| DEF-CHG001 | Catalyst | CHG | -- | C |
| DEF-CHG002 | pH scale | CHG | SCL | C |
| DEF-CHG003 | Le Chatelier's principle | CHG | -- | C |
| DEF-CHG004 | Half-life | CHG | SCL | C |
| DEF-CHG005 | Precipitation | CHG | -- | E |

### SCL -- Scale (6 PRIM + 5 DEF = 11 items)

| ID | Concept | Owner | Referenced By | Tier |
|----|---------|-------|---------------|------|
| PRIM-SCL001 | Macro-to-submicro translation | SCL | -- | C |
| PRIM-SCL002 | Mole concept | SCL | CHG | C |
| PRIM-SCL003 | Concentration reasoning | SCL | CHG | C |
| PRIM-SCL004 | Emergent property reasoning | SCL | -- | C |
| PRIM-SCL005 | Proportional reasoning | SCL | CHG | C |
| PRIM-SCL006 | Unit analysis | SCL | -- | C |
| DEF-SCL001 | Molarity | SCL | CHG | C |
| DEF-SCL002 | Parts per million/billion | SCL | -- | C |
| DEF-SCL003 | Ideal gas reasoning | SCL | -- | E |
| DEF-SCL004 | Colligative properties | SCL | -- | E |
| DEF-SCL005 | Safety and risk reasoning | SCL | -- | C |

---

## 10. Domain Dependency DAG

```
COM (root -- no prerequisites)
 |-- STR (depends: COM)
 |-- NRG (depends: COM)
 |-- SCL (depends: COM)
 +-- CHG (depends: STR, NRG, SCL)
```

STR, NRG, and SCL are **mutually independent**. CHG depends on all three.

**Topological sort (pedagogical order)**: COM --> STR --> NRG --> SCL --> CHG

### Independence Verification Arguments

Each independence claim below is supported by a non-trivial argument:

- **STR does not depend on NRG**: Bond type classification (PRIM-STR001) uses electronegativity difference from COM (DEF-COM005), not bond energy from NRG. Molecular shape reasoning (PRIM-STR003) uses electron-pair repulsion geometry, which is a structural argument. No NRG primitive is required to determine bond type, polarity, or molecular geometry.

- **STR does not depend on SCL**: Molecular structure reasoning operates at the individual-molecule level. Lewis structures, bond angles, and intermolecular force hierarchies are all defined without reference to moles, concentration, or macroscopic measurement. Bulk properties like boiling point are SCL's responsibility (bridging via CP-001).

- **NRG does not depend on STR**: Energy conservation, entropy, spontaneity, and activation energy are defined as abstract energy-accounting reasoning moves. They do not require knowledge of molecular geometry or intermolecular force hierarchies. Bond energy reasoning (PRIM-NRG002) reasons about energy stored in bonds without needing to know bond angles or molecular shape.

- **NRG does not depend on SCL**: Energy concepts (exo/endothermic, entropy, spontaneity) are defined qualitatively at the conceptual level, not in terms of moles, molarity, or macroscopic measurement. Specific heat capacity (DEF-NRG002) is defined as an energy-per-mass-per-degree concept within NRG; SCL handles its deployment in quantitative calculations.

- **SCL does not depend on STR or NRG**: The mole concept (PRIM-SCL002), concentration reasoning (PRIM-SCL003), proportional reasoning (PRIM-SCL005), and unit analysis (PRIM-SCL006) are general bridging tools between submicroscopic and macroscopic descriptions. They do not require molecular geometry (STR) or energy concepts (NRG) to define.

---

## 11. Composition Pattern Template

Composition patterns document cross-domain reasoning chains that integrate primitives from multiple domains. Each pattern follows this format:

```markdown
### CP-NNN: **{Pattern Name}**

- **Domains**: {DomainCode} x {DomainCode} [x ...]
- **Statement**: [what this pattern accomplishes]
- **Natural language**: [explanation, >= 1 sentence]
- **Key dependencies**: [list of PRIM/DEF IDs from each involved domain]
- **Real-world hook**: [everyday context where this pattern is deployed]
- **Tier**: C or E
- **Significance**: [why this cross-domain integration matters]
```

### Registered Composition Patterns

Seven composition patterns are registered. Full specifications live in COMPOSITION-PATTERNS.md.

| ID | Name | Domains | Tier |
|----|------|---------|------|
| CP-001 | Structure-to-Property Prediction | STR x SCL | C |
| CP-002 | Energy-Driven Transformation | NRG x CHG | C |
| CP-003 | Acid-Base in the Body | STR x CHG x SCL | C |
| CP-004 | Greenhouse Effect | STR x NRG x SCL | C |
| CP-005 | Dose Makes the Poison | STR x CHG x SCL | C |
| CP-006 | Food Chemistry | COM x NRG x CHG x SCL | C |
| CP-007 | Biochemistry Connection | STR x CHG x SCL | E |

---

## 12. Self-Audit Checklist

Every domain spec MUST pass all 10 items before being considered complete:

- [ ] Every PRIM has: reasoning move formulation ("Given X, do Y to determine Z"), description, semi-formal statement, depends, ownership, source, referenced-by, tier, real-world hook
- [ ] Every DEF depends only on previously listed PRIM/DEF (check intra-domain dependency graph)
- [ ] Every cross-domain reference uses full `{Type}-{Code}{Number}` format
- [ ] Every import is listed in the source domain's exports
- [ ] Dissolution argument is present and non-trivial (at least 2 sentences explaining why this domain is distinct)
- [ ] Real-world hooks cover everyday non-major contexts (cooking, cleaning, health, environment, consumer products)
- [ ] Intra-domain dependency graph is acyclic
- [ ] Tier annotations (C/E) are present on all items
- [ ] No PRIM/DEF duplicates an entry in another domain (checked against Primitive Registry)
- [ ] Reasoning moves are genuinely "Given X, do Y" cognitive operations (not mere topic labels or vocabulary words)

---

## 13. CER Framework Mapping

This section maps established chemistry education research (CER) frameworks onto the taxonomy's domain structure, ensuring that the 5-domain architecture is not arbitrary but aligns with independently validated conceptual dimensions.

### Talanquer Reasoning Dimensions (2006)

| Talanquer Dimension | Primary Domain | Key Primitives |
|---------------------|---------------|----------------|
| Composition/Structure | COM, STR | PRIM-COM001 (atomic composition), PRIM-STR001 (bond type), PRIM-STR003 (shape) |
| Energy | NRG | PRIM-NRG001 (energy tracking), PRIM-NRG003 (exo/endo), PRIM-NRG005 (spontaneity) |
| Mechanism/Process | CHG | PRIM-CHG001 (equation balancing), PRIM-CHG004 (rate), PRIM-CHG003 (equilibrium) |
| Scale/Proportionality | SCL | PRIM-SCL001 (macro-submicro), PRIM-SCL002 (mole), PRIM-SCL005 (proportional) |
| Classification | COM | PRIM-COM004 (substance classification), PRIM-COM003 (periodic position) |
| Causality | COM (foundational) | PRIM-COM008 (causal chain reasoning) -- deployed across all domains |
| Prediction | Cross-domain | Composition patterns CP-001 through CP-007 |

### Cooper CLUE Core Ideas (2013)

| CLUE Core Idea | Domain Mapping | Key Primitives |
|----------------|---------------|----------------|
| Electrostatic and bonding interactions | STR | PRIM-STR001, PRIM-STR002, PRIM-STR004, DEF-COM005 (imported) |
| Energy: transformations, transfers | NRG | PRIM-NRG001, PRIM-NRG002, PRIM-NRG003, PRIM-NRG005 |
| Atomic/molecular structure and properties | COM + STR | PRIM-COM001, PRIM-COM007, PRIM-STR003, PRIM-STR005 |
| Change and stability in chemical systems | CHG | PRIM-CHG001, PRIM-CHG003, PRIM-CHG004, DEF-CHG003 |

### Johnstone's Triplet and Mahaffy's Tetrahedron

| Johnstone Level | Domain(s) | Role |
|----------------|-----------|------|
| Submicroscopic | COM, STR, NRG, CHG | These domains define reasoning at the atomic/molecular level |
| Macroscopic | SCL | SCL bridges submicroscopic reasoning to observable, measurable phenomena |
| Symbolic | COM (formulas), CHG (equations), SCL (units) | Symbolic representations are distributed across domains |

| Mahaffy Extension | Domain(s) | Role |
|-------------------|-----------|------|
| Human element (contexts, applications) | All via real-world hooks | Every PRIM and DEF includes a real-world hook; applications deploy primitives |

### Talanquer Threshold Schemas (2015)

| Threshold Schema | Domain | Key Primitives |
|-----------------|--------|----------------|
| Electric interactions govern structure and properties | STR | PRIM-STR001, PRIM-STR002, PRIM-STR004 |
| Energy is quantized and conserved | NRG | PRIM-NRG001, PRIM-NRG002 |
| Chemical identity is determined by atomic composition | COM | PRIM-COM001, PRIM-COM002, PRIM-COM003 |
| Chemical change involves breaking and making of bonds | CHG + NRG | PRIM-CHG001 (CHG owns), PRIM-NRG002 (NRG provides energy reasoning) |
| Emergent properties arise from collective behavior | SCL | PRIM-SCL001, PRIM-SCL004 |

---

## 14. Global Sources (SRC-GLB)

| ID | Reference |
|----|-----------|
| SRC-GLB001 | Talanquer, "How do students reason about chemical substances and reactions?" *Chemical Education Research and Practice*, 2006 |
| SRC-GLB002 | Cooper & Klymkowsky, "Chemistry, Life, the Universe, and Everything: A New Approach to General Chemistry," *J. Chem. Educ.*, 2013 |
| SRC-GLB003 | Johnstone, "Why is science difficult to learn? Things are seldom what they seem," *J. Computer Assisted Learning*, 1991 |
| SRC-GLB004 | Mahaffy et al., "Beyond 'Inert' Ideas to Teaching General Chemistry from Rich Contexts," *Nature Reviews Chemistry*, 2018 |
| SRC-GLB005 | Talanquer, "Threshold concepts in chemistry," *Chemistry Education Research and Practice*, 2015 |
| SRC-GLB006 | Bennett, Lubben, & Hogarth, "Bringing science to life: A synthesis of the research evidence," *International Journal of Science Education*, 2007 |
| SRC-GLB007 | Perkins & Salomon, "Transfer of learning," *International Encyclopedia of Education*, 1992 |
| SRC-GLB008 | OpenStax, *Chemistry 2e*, 2019 (Creative Commons) |
| SRC-GLB009 | Zumdahl & Zumdahl, *Chemistry*, 10th ed., 2017 |
| SRC-GLB010 | ACS, *Chemistry in Context*, 10th ed., 2020 |

---

## 15. Global Assumptions (ASM-GLB)

| ID | Assumption | Justification |
|----|-----------|---------------|
| ASM-GLB001 | Target audience is non-science majors in a one-semester course | Design constraint from project brief |
| ASM-GLB002 | No calculus; algebra and proportional reasoning only | Math ceiling for non-majors; proportional reasoning is sufficient for all Core-tier items |
| ASM-GLB003 | Chemical literacy = ability to decompose and evaluate chemical claims, not solve quantitative STEM problems | Core design goal: students should be able to read a news article about a chemical topic and reason about it using named primitives |
| ASM-GLB004 | Applications are deployment exercises for named primitives, not the organizational backbone | Solves the situatedness paradox (Bennett et al. 2007, SRC-GLB006): contexts motivate but do not define the curriculum architecture |
| ASM-GLB005 | ACS exam alignment is verified after design, not used to drive architecture | Prevents exam content from dictating conceptual structure; alignment is a validation step, not a design input |

---

## 16. Global Unknowns (UNK-GLB)

| ID | Unknown | Impact |
|----|---------|--------|
| UNK-GLB001 | Optimal granularity for organic chemistry: should functional groups each be separate DEFs or one general "functional group recognition" primitive? | Affects item count in STR. Resolve during DOMAIN-STR authoring. Currently, DEF-STR007 (carbon backbone reasoning) is a single entry; functional groups may warrant expansion. |
| UNK-GLB002 | How deep into nuclear chemistry should CHG go for non-majors? | PRIM-CHG007 is Enrichment tier; may need further scoping or additional DEFs (fission/fusion). Resolve during DOMAIN-CHG authoring. |
| UNK-GLB003 | Should "scientific method" or "evidence evaluation" be an explicit primitive in COM? | Currently implicit in PRIM-COM008 (causal chain reasoning). If pilot testing reveals students cannot transfer causal reasoning without explicit metacognitive scaffolding, promote to separate PRIM. Monitor during pilot. |

---

## 17. Worked Example: One Fully Specified Entry

This demonstrates exactly what a completed entry looks like in a domain spec:

- PRIM-NRG003: **Exo/endothermic classification**
  - Reasoning move: Given an energy diagram or description of a process, classify it as exothermic (energy released to surroundings) or endothermic (energy absorbed from surroundings) to predict temperature changes and energy flow direction.
  - Description: The cognitive operation of determining whether a chemical or physical process releases or absorbs energy. This is the foundational binary classification in energy reasoning: every process that involves energy change is either exo- or endothermic. The classification depends on comparing energy of reactants vs. products, not on the speed or mechanism of the process.
  - Semi-formal: Given a process P with initial state energy E_i and final state energy E_f: if E_f < E_i, then P is exothermic (delta-E < 0, energy released). If E_f > E_i, then P is endothermic (delta-E > 0, energy absorbed).
  - Depends: PRIM-NRG001 (energy tracking)
  - Ownership: NRG
  - Source: SRC-GLB008 (OpenStax Chemistry 2e, Ch. 5), SRC-GLB009 (Zumdahl Ch. 6)
  - Referenced by: CHG
  - Tier: C
  - Real-world hook: When you hold an instant cold pack (endothermic dissolution of ammonium nitrate) or feel warmth from a hand warmer (exothermic oxidation of iron), you are experiencing the macroscopic consequence of exo/endothermic classification.

Every item in every domain spec MUST match this level of detail.
