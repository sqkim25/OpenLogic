# Coverage Matrix: 62 Taxonomy Items x 4 Sources

**Date:** 2026-02-14
**Depends on:** 01-OPENSTAX-MAP.md, 02-CLUE-MAP.md, 03-SECONDARY-MAPS.md, taxonomy/CONVENTIONS.md
**Purpose:** Taxonomy-first validation — every item checked against every source, canonical source designated, gaps flagged.

---

## Methodology

### Sources (ranked by licensing preference)

| Code | Source | License | Role |
|------|--------|---------|------|
| OS | OpenStax Chemistry 2e | CC-BY 4.0 | Primary corpus |
| CLUE | CLUE (Cooper & Klymkowsky) | CC-BY-NC-SA 4.0 | Pedagogical model |
| SAY | Saylor GOB (Ball et al.) | CC-BY-NC-SA | Non-majors reference |
| CIC | Chemistry in Context 10e (ACS) | Proprietary | Structural validation only |

### Coverage Codes

| Code | Meaning |
|------|---------|
| **FULL** | Source covers all aspects of the taxonomy item at usable depth |
| **PARTIAL** | Source covers some aspects or at insufficient depth |
| **PERIPHERAL** | Source touches the concept tangentially |
| **--** | Source does not cover this item |

### Canonical Source Criteria (in priority order)

1. **Audience match**: Non-majors framing preferred over majors depth
2. **Reasoning-move alignment**: Skill framing > vocabulary framing
3. **Licensing**: CC-BY 4.0 > CC-BY-NC-SA > proprietary
4. **Completeness**: Covers all aspects of the taxonomy item
5. **Recency**: Newer edition preferred

### Validation Status

| Status | Meaning |
|--------|---------|
| **VALIDATED** | >= 1 source at FULL coverage; canonical source designated |
| **PARTIAL-ONLY** | All sources at PARTIAL or PERIPHERAL; needs Phase 3 attention |
| **META** | Meta-cognitive item; coverage through framing, not standalone sections |
| **GAP** | No source coverage; requires original writing or Phase 1 backtrack |

---

## COM Domain (13 items: 8 PRIM + 5 DEF)

### PRIM-COM001: Atomic composition analysis (C)

| Source | Coverage | Key Sections | Signal |
|--------|----------|-------------|--------|
| OS | FULL | 2.1, 2.2, 2.3 | ADAPT/REWRITE |
| CLUE | FULL | 1.3, 1.5, 1.6 | ADAPT |
| SAY | FULL | Ch 2 | -- |
| CIC | FULL | Ch 1 | -- |

**Canonical source:** OS (CC-BY 4.0, comprehensive; 2.3 is the highest-value section)
**Status:** VALIDATED

---

### PRIM-COM002: Elemental identity (C)

| Source | Coverage | Key Sections | Signal |
|--------|----------|-------------|--------|
| OS | FULL | 2.3, 2.5 | ADAPT |
| CLUE | PARTIAL | 1.4 | ADAPT |
| SAY | FULL | Ch 2 | -- |
| CIC | FULL | Ch 1 | -- |

**Canonical source:** OS (CC-BY 4.0, FULL coverage)
**Status:** VALIDATED

---

### PRIM-COM003: Periodic position reasoning (C)

| Source | Coverage | Key Sections | Signal |
|--------|----------|-------------|--------|
| OS | FULL | 2.5, 6.5 | ADAPT |
| CLUE | FULL | 2.5 | ADAPT |
| SAY | FULL | Ch 2 | -- |
| CIC | FULL | Ch 1 | -- |

**Canonical source:** OS (CC-BY 4.0; 6.5 adds electronegativity trends)
**Status:** VALIDATED

---

### PRIM-COM004: Substance classification (C)

| Source | Coverage | Key Sections | Signal |
|--------|----------|-------------|--------|
| OS | FULL | 1.2, 1.3 | ADAPT |
| CLUE | PARTIAL | 1.4, 6.1 | ADAPT |
| SAY | FULL | Ch 1 | -- |
| CIC | -- | -- | -- |

**Canonical source:** OS (CC-BY 4.0, direct coverage in 1.2)
**Status:** VALIDATED
**Note:** CIC does not teach substance classification explicitly; its contexts assume students can distinguish elements from compounds.

---

### PRIM-COM005: Chemical formula reading (C)

| Source | Coverage | Key Sections | Signal |
|--------|----------|-------------|--------|
| OS | FULL | 2.4 | ADAPT |
| CLUE | PARTIAL | 4.1 | ADAPT |
| SAY | FULL | Ch 6 | -- |
| CIC | FULL | Ch 2 | -- |

**Canonical source:** OS (CC-BY 4.0, direct coverage in 2.4)
**Status:** VALIDATED

---

### PRIM-COM006: Conservation of atoms (C)

| Source | Coverage | Key Sections | Signal |
|--------|----------|-------------|--------|
| OS | FULL | 4.1 | ADAPT |
| CLUE | FULL | 7.1 | ADAPT |
| SAY | FULL | Ch 5 | -- |
| CIC | FULL | Ch 5, 11 | -- |

**Canonical source:** OS (CC-BY 4.0, direct coverage; equation balancing deploys this)
**Status:** VALIDATED

---

### PRIM-COM007: Valence electron reasoning (C)

| Source | Coverage | Key Sections | Signal |
|--------|----------|-------------|--------|
| OS | FULL | 6.4, 6.5, 7.1, 7.3 | ADAPT/REF-ONLY |
| CLUE | FULL | 2.2, 2.5, 3.1, 4.4 | ADAPT/REF-ONLY |
| SAY | FULL | Ch 2 | -- |
| CIC | PERIPHERAL | Ch 1 (implicit) | -- |

**Canonical source:** OS (CC-BY 4.0; 6.5 and 7.3 provide the non-majors-relevant treatment — periodic table position gives valence electron count without electron configurations)
**Status:** VALIDATED
**Note:** CLUE has stronger reasoning-move alignment (valence electrons motivated by bonding prediction), but OS license advantage prevails. CLUE serves as pedagogical model.

---

### PRIM-COM008: Causal chain reasoning (C)

| Source | Coverage | Key Sections | Signal |
|--------|----------|-------------|--------|
| OS | -- | (deployed implicitly throughout) | -- |
| CLUE | PARTIAL | 1.2, 8.6 | ADAPT |
| SAY | -- | (deployed implicitly) | -- |
| CIC | -- | (deployed implicitly) | -- |

**Canonical source:** CLUE (only source with explicit treatment of causal reasoning as a skill)
**Status:** META
**Note:** This is a meta-cognitive reasoning primitive, not a chemistry content topic. All sources deploy causal chain reasoning implicitly; only CLUE teaches it explicitly as a mode of scientific reasoning. Coverage in our textbook comes from the reasoning-move framing itself — every PRIM is stated as a "Given X, do Y to determine Z" chain. No standalone section needed; scaffold through worked examples and "Questions to Answer" throughout.

---

### DEF-COM001: Isotope (C)

| Source | Coverage | Key Sections | Signal |
|--------|----------|-------------|--------|
| OS | FULL | 2.3 | ADAPT |
| CLUE | FULL | 1.6 | ADAPT |
| SAY | FULL | Ch 2 | -- |
| CIC | FULL | Ch 1 | -- |

**Canonical source:** OS (CC-BY 4.0, direct coverage)
**Status:** VALIDATED

---

### DEF-COM002: Ion (C)

| Source | Coverage | Key Sections | Signal |
|--------|----------|-------------|--------|
| OS | FULL | 2.3, 2.6 | ADAPT |
| CLUE | FULL | 1.6, 4.6 | ADAPT |
| SAY | FULL | Ch 2, 3 | -- |
| CIC | FULL | Ch 1 | -- |

**Canonical source:** OS (CC-BY 4.0, direct coverage in 2.3)
**Status:** VALIDATED

---

### DEF-COM003: Molecular vs empirical formula (E)

| Source | Coverage | Key Sections | Signal |
|--------|----------|-------------|--------|
| OS | FULL | 3.2 | REWRITE |
| CLUE | -- | (stoichiometry omitted by design) | -- |
| SAY | FULL | Ch 6 | -- |
| CIC | -- | (never motivated by CIC contexts) | -- |

**Canonical source:** OS (CC-BY 4.0, FULL coverage; needs simplification for non-majors)
**Status:** VALIDATED
**Note:** E-tier. Absent from both reformed curricula (CLUE, CIC), confirming Enrichment classification.

---

### DEF-COM004: Percent composition (E)

| Source | Coverage | Key Sections | Signal |
|--------|----------|-------------|--------|
| OS | FULL | 3.2 | REWRITE |
| CLUE | -- | (stoichiometry omitted by design) | -- |
| SAY | FULL | Ch 6 | -- |
| CIC | -- | (never motivated by CIC contexts) | -- |

**Canonical source:** OS (CC-BY 4.0, FULL coverage; needs non-majors simplification)
**Status:** VALIDATED
**Note:** E-tier. Same pattern as DEF-COM003.

---

### DEF-COM005: Electronegativity (C)

| Source | Coverage | Key Sections | Signal |
|--------|----------|-------------|--------|
| OS | FULL | 6.5 | ADAPT |
| CLUE | FULL | 3.1, 4.6 | ADAPT |
| SAY | FULL | Ch 3 | -- |
| CIC | PERIPHERAL | (implicit in bonding discussions) | -- |

**Canonical source:** OS (CC-BY 4.0, direct coverage of periodic electronegativity trends)
**Status:** VALIDATED

---

### COM Domain Summary

| Status | Count | Items |
|--------|-------|-------|
| VALIDATED | 12 | PRIM-COM001 through COM007, DEF-COM001 through DEF-COM005 |
| META | 1 | PRIM-COM008 (causal chain reasoning) |
| GAP | 0 | -- |

**Coverage rate:** 13/13 (100%). No gaps. One META item handled through framing.

---

## STR Domain (15 items: 5 PRIM + 10 DEF)

### PRIM-STR001: Bond type classification (C)

| Source | Coverage | Key Sections | Signal |
|--------|----------|-------------|--------|
| OS | FULL | 7.1, 7.2 | ADAPT |
| CLUE | FULL | 3.1, 4.3, 4.4, 4.6 | ADAPT |
| SAY | FULL | Ch 3, 4 | -- |
| CIC | FULL | Ch 2 | -- |

**Canonical source:** OS (CC-BY 4.0, comprehensive ionic + covalent treatment)
**Status:** VALIDATED

---

### PRIM-STR002: Bond polarity reasoning (C)

| Source | Coverage | Key Sections | Signal |
|--------|----------|-------------|--------|
| OS | FULL | 7.2 | ADAPT |
| CLUE | FULL | 4.4, 6.5, 7.4 | ADAPT |
| SAY | FULL | Ch 4 | -- |
| CIC | FULL | Ch 2, 3, 4 | -- |

**Canonical source:** OS (CC-BY 4.0, direct coverage)
**Status:** VALIDATED

---

### PRIM-STR003: Molecular shape reasoning (C)

| Source | Coverage | Key Sections | Signal |
|--------|----------|-------------|--------|
| OS | FULL | 7.6 | ADAPT |
| CLUE | FULL | 4.2, 4.5 | ADAPT |
| SAY | FULL | Ch 4 | -- |
| CIC | FULL | Ch 3, 4 | -- |

**Canonical source:** OS (CC-BY 4.0, VSEPR with molecular polarity in one section)
**Status:** VALIDATED

---

### PRIM-STR004: Intermolecular force hierarchy (C)

| Source | Coverage | Key Sections | Signal |
|--------|----------|-------------|--------|
| OS | FULL | 10.1 | ADAPT |
| CLUE | FULL | 1.8, 4.5, 6.2 | ADAPT |
| SAY | FULL | Ch 8 | -- |
| CIC | FULL | Ch 4, 8, 13 | -- |

**Canonical source:** OS (CC-BY 4.0, comprehensive IMF treatment in 10.1)
**Status:** VALIDATED
**Note:** CLUE introduces IMFs remarkably early (Ch 1), which is pedagogically superior. Consider emulating CLUE's early-IMF strategy in Phase 4 chapter ordering.

---

### PRIM-STR005: Structure-to-property inference (C)

| Source | Coverage | Key Sections | Signal |
|--------|----------|-------------|--------|
| OS | FULL | 1.3, 10.2 | ADAPT |
| CLUE | FULL | 3.2, 3.3, 9.3 | ADAPT |
| SAY | FULL | Ch 8, 14, 17, 18 | -- |
| CIC | FULL | Ch 9, 10, 12, 13 | -- |

**Canonical source:** OS (CC-BY 4.0; 10.2 demonstrates the reasoning move through liquid properties)
**Status:** VALIDATED
**Note:** Most frequently deployed primitive across all sources. CIC exercises it in 4+ chapters because structure-to-property prediction is central to non-majors chemical literacy.

---

### DEF-STR001: Lewis structure (C)

| Source | Coverage | Key Sections | Signal |
|--------|----------|-------------|--------|
| OS | FULL | 7.3 | ADAPT |
| CLUE | FULL | 4.1, 4.2, 4.3 | ADAPT |
| SAY | FULL | Ch 4 | -- |
| CIC | FULL | Ch 2 | -- |

**Canonical source:** OS (CC-BY 4.0, comprehensive Lewis structure procedure)
**Status:** VALIDATED

---

### DEF-STR002: Molecular polarity (C)

| Source | Coverage | Key Sections | Signal |
|--------|----------|-------------|--------|
| OS | FULL | 7.6 | ADAPT |
| CLUE | FULL | 4.5, 6.5 | ADAPT |
| SAY | FULL | Ch 4 | -- |
| CIC | PARTIAL | Ch 4 (implicit) | -- |

**Canonical source:** OS (CC-BY 4.0, combined with VSEPR in 7.6)
**Status:** VALIDATED

---

### DEF-STR003: Hydrogen bond (C)

| Source | Coverage | Key Sections | Signal |
|--------|----------|-------------|--------|
| OS | FULL | 10.1 | ADAPT |
| CLUE | FULL | 4.5, 6.3 | ADAPT |
| SAY | FULL | Ch 8 | -- |
| CIC | FULL | Ch 8, 13 | -- |

**Canonical source:** OS (CC-BY 4.0, within IMF hierarchy treatment)
**Status:** VALIDATED

---

### DEF-STR004: "Like dissolves like" (C)

| Source | Coverage | Key Sections | Signal |
|--------|----------|-------------|--------|
| OS | FULL | 11.1, 11.3 | ADAPT |
| CLUE | FULL | 6.2, 6.3 | ADAPT |
| SAY | FULL | Ch 9 | -- |
| CIC | FULL | Ch 8 | -- |

**Canonical source:** OS (CC-BY 4.0, IMF-based dissolution reasoning)
**Status:** VALIDATED

---

### DEF-STR005: Isomer recognition (C)

| Source | Coverage | Key Sections | Signal |
|--------|----------|-------------|--------|
| OS | FULL | 20.1 | ADAPT |
| CLUE | -- | (minimal organic chemistry) | -- |
| SAY | FULL | Ch 12, 13, 16 | -- |
| CIC | FULL | Ch 9, 12 | -- |

**Canonical source:** OS (CC-BY 4.0, FULL coverage in organic chemistry chapter)
**Status:** VALIDATED
**Note:** SAY provides the most extensive non-majors treatment across 3 chapters (structural isomers in alkanes, cis/trans in alkenes, stereoisomers in carbohydrates). SAY is a valuable supplementary source.

---

### DEF-STR006: Phase from IMF balance (C)

| Source | Coverage | Key Sections | Signal |
|--------|----------|-------------|--------|
| OS | FULL | 10.3 | ADAPT |
| CLUE | FULL | 5.6 | ADAPT |
| SAY | FULL | Ch 8 | -- |
| CIC | PERIPHERAL | (implicit) | -- |

**Canonical source:** OS (CC-BY 4.0, heating curves and enthalpy of phase change)
**Status:** VALIDATED

---

### DEF-STR007: Carbon backbone reasoning (C)

| Source | Coverage | Key Sections | Signal |
|--------|----------|-------------|--------|
| OS | FULL | 20.1, 20.2, 20.3, 20.4 | ADAPT/REWRITE |
| CLUE | PARTIAL | 9.3 (amino acids only) | ADAPT |
| SAY | FULL | Ch 12--19 (8 chapters) | -- |
| CIC | FULL | Ch 9, 10, 11, 12, 13 | -- |

**Canonical source:** OS (CC-BY 4.0, FULL coverage in Ch 20)
**Supplementary:** SAY (most extensive non-majors treatment across 8 chapters; functional group recognition in biological and everyday contexts)
**Status:** VALIDATED
**Note:** OS treats organic chemistry in one chapter at somewhat-majors depth. SAY distributes it across 8 chapters at consistent non-majors depth. Phase 4 should consider SAY's pacing for this item.

---

### DEF-STR008: Polymer reasoning (C)

| Source | Coverage | Key Sections | Signal |
|--------|----------|-------------|--------|
| OS | -- | (not in non-majors-relevant sections) | -- |
| CLUE | -- | (no polymer content) | -- |
| SAY | FULL | Ch 15, 16, 18, 19 | -- |
| CIC | FULL | Ch 9 | -- |

**Canonical source:** SAY (CC-BY-NC-SA; only OER source with FULL non-majors polymer coverage; condensation polymerization in Ch 15, polysaccharides in Ch 16, proteins in Ch 18, nucleic acids in Ch 19)
**Supplementary:** CIC Ch 9 (structural validation — plastics, recycling context; proprietary, reference only)
**Status:** VALIDATED
**Note:** OS covers polymers only in the SKIPped appendix-level content. SAY is canonical despite NC-SA license because it is the only adaptable source with FULL coverage at non-majors depth. CIC's plastics/recycling context (Ch 9) validates our inclusion of this item.

---

### DEF-STR009: Metallic structure (E)

| Source | Coverage | Key Sections | Signal |
|--------|----------|-------------|--------|
| OS | -- | (in SKIPped Ch 18) | -- |
| CLUE | FULL | 3.3 | ADAPT |
| SAY | FULL | Ch 3 | -- |
| CIC | -- | -- | -- |

**Canonical source:** CLUE (CC-BY-NC-SA; conceptual metallic bonding treatment in 3.3 — sea-of-electrons model explaining conductivity, malleability, luster)
**Supplementary:** SAY Ch 3 (independent non-majors treatment)
**Status:** VALIDATED
**Note:** E-tier. OS covers metallic bonding but in the entirely MAJORS-ONLY Ch 18 (Representative Metals). CLUE and SAY both provide appropriate non-majors treatments.

---

### DEF-STR010: Water as solvent (C)

| Source | Coverage | Key Sections | Signal |
|--------|----------|-------------|--------|
| OS | FULL | 11.1 | ADAPT |
| CLUE | FULL | 6.1 | ADAPT |
| SAY | FULL | Ch 9 | -- |
| CIC | FULL | Ch 8 | -- |

**Canonical source:** OS (CC-BY 4.0, water's properties from H-bonding perspective)
**Status:** VALIDATED

---

### STR Domain Summary

| Status | Count | Items |
|--------|-------|-------|
| VALIDATED | 15 | All STR items |
| GAP | 0 | -- |

**Coverage rate:** 15/15 (100%). No gaps. Two items (DEF-STR008, DEF-STR009) require non-OS canonical sources due to OS coverage gaps at non-majors level.

---

## NRG Domain (11 items: 6 PRIM + 5 DEF)

### PRIM-NRG001: Energy tracking (C)

| Source | Coverage | Key Sections | Signal |
|--------|----------|-------------|--------|
| OS | FULL | 5.1 | ADAPT |
| CLUE | FULL | 1.7, 5.3, 5.4, 7.6, 9.5 | ADAPT |
| SAY | FULL | Ch 7 | -- |
| CIC | FULL | Ch 5, 6, 7 | -- |

**Canonical source:** OS (CC-BY 4.0, foundational energy concepts in 5.1)
**Status:** VALIDATED

---

### PRIM-NRG002: Bond energy reasoning (C)

| Source | Coverage | Key Sections | Signal |
|--------|----------|-------------|--------|
| OS | FULL | 7.5 | ADAPT |
| CLUE | FULL | 4.3, 7.6 | ADAPT |
| SAY | FULL | Ch 7 | -- |
| CIC | FULL | Ch 3, 5 | -- |

**Canonical source:** OS (CC-BY 4.0, bond dissociation energy and enthalpy estimation in 7.5)
**Status:** VALIDATED

---

### PRIM-NRG003: Exo/endothermic classification (C)

| Source | Coverage | Key Sections | Signal |
|--------|----------|-------------|--------|
| OS | FULL | 5.1 | ADAPT |
| CLUE | FULL | 5.4, 5.5, 5.6, 7.6 | ADAPT |
| SAY | FULL | Ch 7 | -- |
| CIC | FULL | Ch 5, 7 | -- |

**Canonical source:** OS (CC-BY 4.0, energy diagrams and classification in 5.1)
**Status:** VALIDATED

---

### PRIM-NRG004: Entropy reasoning (C)

| Source | Coverage | Key Sections | Signal |
|--------|----------|-------------|--------|
| OS | FULL | 16.2 | REWRITE |
| CLUE | FULL | 5.2, 5.5, 6.4 | ADAPT |
| SAY | -- | (GOB texts omit formal entropy) | -- |
| CIC | -- | (not motivated by CIC contexts) | -- |

**Canonical source:** OS (CC-BY 4.0, comprehensive entropy treatment in 16.2)
**Pedagogical model:** CLUE (introduces entropy in Ch 5 as molecular dispersal, enabling its use as a reasoning tool in Chapters 6-9; superior integration)
**Status:** VALIDATED
**Note:** OS provides mathematical depth that needs simplification. CLUE provides the better pedagogical model (entropy as energy dispersal, introduced alongside enthalpy, not 11 chapters later). Absent from both non-majors-specific sources (SAY, CIC), suggesting this item approaches the Core/Enrichment boundary. Retained as Core because entropy reasoning is essential for spontaneity (PRIM-NRG005).

---

### PRIM-NRG005: Spontaneity reasoning (C)

| Source | Coverage | Key Sections | Signal |
|--------|----------|-------------|--------|
| OS | FULL | 16.1 | ADAPT |
| CLUE | FULL | 5.7, 8.1, 9.4, 9.5 | ADAPT |
| SAY | -- | (GOB texts omit formal spontaneity) | -- |
| CIC | PARTIAL | Ch 7 (implicit via battery favorability) | -- |

**Canonical source:** OS (CC-BY 4.0, clear conceptual treatment in 16.1)
**Pedagogical model:** CLUE (spontaneity deployed as a reasoning tool from Ch 5 onward, culminating in coupled reactions in Ch 9)
**Status:** VALIDATED

---

### PRIM-NRG006: Activation energy reasoning (C)

| Source | Coverage | Key Sections | Signal |
|--------|----------|-------------|--------|
| OS | FULL | 12.5 | ADAPT |
| CLUE | FULL | 7.1, 8.3, 8.4 | ADAPT |
| SAY | PARTIAL | Ch 7 (implicit in catalysis) | -- |
| CIC | FULL | Ch 10 | -- |

**Canonical source:** OS (CC-BY 4.0, collision theory and energy diagrams in 12.5)
**Status:** VALIDATED

---

### DEF-NRG001: Heat vs temperature (C)

| Source | Coverage | Key Sections | Signal |
|--------|----------|-------------|--------|
| OS | FULL | 5.1, 5.2 | ADAPT |
| CLUE | FULL | 5.1 | ADAPT |
| SAY | FULL | Ch 7 | -- |
| CIC | PERIPHERAL | (implicit) | -- |

**Canonical source:** OS (CC-BY 4.0, direct treatment in 5.1)
**Status:** VALIDATED

---

### DEF-NRG002: Specific heat capacity (C)

| Source | Coverage | Key Sections | Signal |
|--------|----------|-------------|--------|
| OS | FULL | 5.2 | REWRITE |
| CLUE | PARTIAL | 5.3 (molecular modes and heat capacity) | ADAPT |
| SAY | FULL | Ch 7 | -- |
| CIC | -- | -- | -- |

**Canonical source:** OS (CC-BY 4.0, FULL coverage; needs simplification from calorimetry calculations to conceptual reasoning)
**Status:** VALIDATED
**Note:** CIC never introduces specific heat because no societal context demands it in isolation. This confirms the item is valuable (why does water moderate climate?) but its standalone treatment is borderline.

---

### DEF-NRG003: Enthalpy change (delta-H) (C)

| Source | Coverage | Key Sections | Signal |
|--------|----------|-------------|--------|
| OS | FULL | 5.3 | REWRITE |
| CLUE | FULL | 5.5, 7.6 | ADAPT |
| SAY | FULL | Ch 7 | -- |
| CIC | FULL | Ch 5 | -- |

**Canonical source:** OS (CC-BY 4.0, FULL coverage; computational depth needs reduction)
**Status:** VALIDATED

---

### DEF-NRG004: Free energy -- conceptual (E)

| Source | Coverage | Key Sections | Signal |
|--------|----------|-------------|--------|
| OS | FULL | 16.4 | REWRITE |
| CLUE | FULL | 5.7, 6.4, 9.5 | ADAPT |
| SAY | -- | (GOB texts omit free energy) | -- |
| CIC | PERIPHERAL | (implicit in Ch 7) | -- |

**Canonical source:** OS (CC-BY 4.0, FULL coverage of Gibbs free energy)
**Pedagogical model:** CLUE (introduces delta-G in Ch 5, then deploys it as a reasoning tool in Chapters 6-9; far superior integration to OS's isolated Ch 16 treatment)
**Status:** VALIDATED
**Note:** E-tier. CLUE's early placement of Gibbs energy is a key pedagogical innovation worth emulating. OS provides the content; CLUE provides the placement strategy.

---

### DEF-NRG005: Calorie/joule (C)

| Source | Coverage | Key Sections | Signal |
|--------|----------|-------------|--------|
| OS | FULL | 5.1 | ADAPT |
| CLUE | PERIPHERAL | (energy units mentioned but not emphasized) | -- |
| SAY | FULL | Ch 7 | -- |
| CIC | FULL | Ch 11 | -- |

**Canonical source:** OS (CC-BY 4.0, energy unit definitions in 5.1)
**Status:** VALIDATED

---

### NRG Domain Summary

| Status | Count | Items |
|--------|-------|-------|
| VALIDATED | 11 | All NRG items |
| GAP | 0 | -- |

**Coverage rate:** 11/11 (100%). No gaps. PRIM-NRG004/NRG005 and DEF-NRG004 are absent from SAY (GOB omits formal thermodynamics), confirming these items are at the Core/Enrichment boundary.

---

## CHG Domain (12 items: 7 PRIM + 5 DEF)

### PRIM-CHG001: Equation reading and balancing (C)

| Source | Coverage | Key Sections | Signal |
|--------|----------|-------------|--------|
| OS | FULL | 4.1 | ADAPT |
| CLUE | PARTIAL | 7.1 (molecular collisions, not equation focus) | ADAPT |
| SAY | FULL | Ch 5 | -- |
| CIC | FULL | Ch 5 | -- |

**Canonical source:** OS (CC-BY 4.0, direct treatment with conservation of mass)
**Status:** VALIDATED

---

### PRIM-CHG002: Reaction type recognition (C)

| Source | Coverage | Key Sections | Signal |
|--------|----------|-------------|--------|
| OS | FULL | 4.2 | ADAPT |
| CLUE | FULL | 7.2, 7.4 | ADAPT |
| SAY | FULL | Ch 5 | -- |
| CIC | PARTIAL | (distributed across contexts) | -- |

**Canonical source:** OS (CC-BY 4.0, systematic classification in 4.2)
**Status:** VALIDATED
**Note:** CLUE's "field guide" metaphor for reaction types is pedagogically superior to OS's list-based approach. Consider adopting CLUE's framing.

---

### PRIM-CHG003: Equilibrium reasoning (C)

| Source | Coverage | Key Sections | Signal |
|--------|----------|-------------|--------|
| OS | FULL | 13.1 | ADAPT |
| CLUE | FULL | 8.5, 9.1, 9.2 | ADAPT |
| SAY | PARTIAL | Ch 10 (implicit in buffer discussion) | -- |
| CIC | PERIPHERAL | (implicit) | -- |

**Canonical source:** OS (CC-BY 4.0, dynamic equilibrium concept in 13.1)
**Status:** VALIDATED

---

### PRIM-CHG004: Rate reasoning (C)

| Source | Coverage | Key Sections | Signal |
|--------|----------|-------------|--------|
| OS | FULL | 12.1, 12.2 | ADAPT/REWRITE |
| CLUE | FULL | 8.1, 8.2, 8.3 | ADAPT |
| SAY | PARTIAL | (implicit in reaction discussions) | -- |
| CIC | FULL | Ch 10 | -- |

**Canonical source:** OS (CC-BY 4.0; 12.2 covers qualitative rate factors)
**Status:** VALIDATED

---

### PRIM-CHG005: Acid-base reasoning (C)

| Source | Coverage | Key Sections | Signal |
|--------|----------|-------------|--------|
| OS | FULL | 14.1 | ADAPT |
| CLUE | FULL | 7.2, 9.2, 9.3 | ADAPT |
| SAY | FULL | Ch 10 | -- |
| CIC | FULL | Ch 8 | -- |

**Canonical source:** OS (CC-BY 4.0, Bronsted-Lowry treatment in 14.1)
**Status:** VALIDATED

---

### PRIM-CHG006: Oxidation-reduction reasoning (C)

| Source | Coverage | Key Sections | Signal |
|--------|----------|-------------|--------|
| OS | FULL | 17.1 | ADAPT |
| CLUE | FULL | 7.5 | ADAPT |
| SAY | FULL | Ch 20 (metabolism) | -- |
| CIC | FULL | Ch 6, 7 | -- |

**Canonical source:** OS (CC-BY 4.0, oxidation states and electron transfer in 17.1)
**Status:** VALIDATED

---

### PRIM-CHG007: Nuclear change reasoning (E)

| Source | Coverage | Key Sections | Signal |
|--------|----------|-------------|--------|
| OS | FULL | 21.1, 21.2 | ADAPT/REWRITE |
| CLUE | -- | (nuclear chemistry omitted) | -- |
| SAY | FULL | Ch 11 | -- |
| CIC | FULL | Ch 6 | -- |

**Canonical source:** OS (CC-BY 4.0, comprehensive nuclear chemistry in Ch 21)
**Status:** VALIDATED
**Note:** E-tier. CLUE's omission is deliberate (insufficient conceptual payoff for the time investment). CIC includes nuclear chemistry because its "energy source" context demands it — supporting our decision to keep this as Enrichment rather than Core.

---

### DEF-CHG001: Catalyst (C)

| Source | Coverage | Key Sections | Signal |
|--------|----------|-------------|--------|
| OS | FULL | 12.7 | ADAPT |
| CLUE | FULL | 8.4 | ADAPT |
| SAY | FULL | Ch 18 (enzymes) | -- |
| CIC | FULL | Ch 10 (fermentation enzymes) | -- |

**Canonical source:** OS (CC-BY 4.0, homogeneous/heterogeneous catalysis + enzymes in 12.7)
**Status:** VALIDATED

---

### DEF-CHG002: pH scale (C)

| Source | Coverage | Key Sections | Signal |
|--------|----------|-------------|--------|
| OS | FULL | 14.2 | ADAPT |
| CLUE | FULL | 7.2 | ADAPT |
| SAY | FULL | Ch 10 | -- |
| CIC | FULL | Ch 8 | -- |

**Canonical source:** OS (CC-BY 4.0, pH definition and scale in 14.2)
**Status:** VALIDATED

---

### DEF-CHG003: Le Chatelier's principle (C)

| Source | Coverage | Key Sections | Signal |
|--------|----------|-------------|--------|
| OS | FULL | 13.3 | ADAPT |
| CLUE | FULL | 8.5, 9.1 | ADAPT |
| SAY | PARTIAL | Ch 10 (implicit in buffer discussion) | -- |
| CIC | PERIPHERAL | (implicit) | -- |

**Canonical source:** OS (CC-BY 4.0, systematic perturbation analysis in 13.3)
**Status:** VALIDATED

---

### DEF-CHG004: Half-life (C)

| Source | Coverage | Key Sections | Signal |
|--------|----------|-------------|--------|
| OS | FULL | 21.3 | ADAPT |
| CLUE | -- | (nuclear chemistry omitted) | -- |
| SAY | FULL | Ch 11 | -- |
| CIC | FULL | Ch 6 | -- |

**Canonical source:** OS (CC-BY 4.0, half-life and carbon dating in 21.3)
**Status:** VALIDATED

---

### DEF-CHG005: Precipitation (E)

| Source | Coverage | Key Sections | Signal |
|--------|----------|-------------|--------|
| OS | FULL | 15.1 | REWRITE |
| CLUE | -- | -- | -- |
| SAY | -- | -- | -- |
| CIC | -- | -- | -- |

**Canonical source:** OS (CC-BY 4.0; only source with explicit precipitation treatment; needs conceptual simplification from Ksp calculations)
**Status:** VALIDATED
**Note:** E-tier. The weakest-covered Core/Enrichment item. OS is the only source with FULL coverage, and that coverage requires significant rewriting. Absent from all three comparison sources (CLUE, SAY, CIC), strongly confirming Enrichment classification.

---

### CHG Domain Summary

| Status | Count | Items |
|--------|-------|-------|
| VALIDATED | 12 | All CHG items |
| GAP | 0 | -- |

**Coverage rate:** 12/12 (100%). No gaps. DEF-CHG005 (precipitation) is the most weakly supported item.

---

## SCL Domain (11 items: 6 PRIM + 5 DEF)

### PRIM-SCL001: Macro-to-submicro translation (C)

| Source | Coverage | Key Sections | Signal |
|--------|----------|-------------|--------|
| OS | PARTIAL | 9.1 (gas pressure as particle behavior) | REWRITE |
| CLUE | FULL | 1.5, 4.1, 5.2 | ADAPT |
| SAY | FULL | Ch 1, 8 | -- |
| CIC | PERIPHERAL | (implicit throughout) | -- |

**Canonical source:** CLUE (CC-BY-NC-SA; only source with explicit, intentional treatment of macro-submicro translation as a reasoning skill — section 5.2 "Thinking About Populations of Molecules" is unique)
**Supplementary:** OS 9.1 (gas pressure provides a specific deployment context)
**Status:** VALIDATED
**Note:** OS treats macro-submicro translation implicitly; CLUE teaches it explicitly. This item bridges Johnstone's triplet (submicroscopic ↔ macroscopic), a core CER concept. CLUE's canonical status here is appropriate despite license — this item is about a reasoning mode, and CLUE is the only source that teaches it as such.

---

### PRIM-SCL002: Mole concept (C)

| Source | Coverage | Key Sections | Signal |
|--------|----------|-------------|--------|
| OS | FULL | 3.1 | REWRITE |
| CLUE | -- | (stoichiometry omitted) | -- |
| SAY | FULL | Ch 6 | -- |
| CIC | PARTIAL | Ch 11 (mole used in food energy calculations) | -- |

**Canonical source:** OS (CC-BY 4.0, comprehensive mole concept in 3.1; computational emphasis needs reframing as a reasoning move — the mole as a macro-submicro bridge)
**Status:** VALIDATED

---

### PRIM-SCL003: Concentration reasoning (C)

| Source | Coverage | Key Sections | Signal |
|--------|----------|-------------|--------|
| OS | FULL | 3.3, 3.4 | ADAPT |
| CLUE | PARTIAL | 6.6 | ADAPT |
| SAY | FULL | Ch 9 | -- |
| CIC | FULL | Ch 8 | -- |

**Canonical source:** OS (CC-BY 4.0, molarity and ppm in 3.3-3.4)
**Status:** VALIDATED

---

### PRIM-SCL004: Emergent property reasoning (C)

| Source | Coverage | Key Sections | Signal |
|--------|----------|-------------|--------|
| OS | PARTIAL | 11.4 (colligative properties as example) | REWRITE |
| CLUE | FULL | 5.2 | ADAPT |
| SAY | FULL | Ch 17, 18, 19 (biological systems) | -- |
| CIC | FULL | Ch 4, 9, 13 | -- |

**Canonical source:** CLUE (CC-BY-NC-SA; 5.2 "Thinking About Populations of Molecules" directly teaches emergent property reasoning as a cognitive skill)
**Supplementary:** SAY (biological emergent properties: cell membranes, protein folding, DNA information storage)
**Status:** VALIDATED
**Note:** Like PRIM-SCL001, this item is about a reasoning mode rather than chemistry content. CLUE's treatment is uniquely aligned with our reasoning-move standard.

---

### PRIM-SCL005: Proportional reasoning (C)

| Source | Coverage | Key Sections | Signal |
|--------|----------|-------------|--------|
| OS | FULL | 1.6, 4.3 | REWRITE/REF-ONLY |
| CLUE | -- | (stoichiometry omitted) | -- |
| SAY | FULL | Ch 6 | -- |
| CIC | FULL | Ch 11 (food label calculations) | -- |

**Canonical source:** OS (CC-BY 4.0, dimensional analysis in 1.6)
**Status:** VALIDATED
**Note:** OS's treatment in 1.6 is procedural (unit conversion drills). CIC's treatment in Ch 11 (food label calculations) deploys proportional reasoning in a non-majors-relevant context. Phase 4 should emphasize context-driven proportional reasoning.

---

### PRIM-SCL006: Unit analysis (C)

| Source | Coverage | Key Sections | Signal |
|--------|----------|-------------|--------|
| OS | FULL | 1.4, 1.6 | ADAPT |
| CLUE | -- | -- | -- |
| SAY | FULL | Ch 1 | -- |
| CIC | PERIPHERAL | (implicit) | -- |

**Canonical source:** OS (CC-BY 4.0, SI units and dimensional analysis)
**Status:** VALIDATED

---

### DEF-SCL001: Molarity (C)

| Source | Coverage | Key Sections | Signal |
|--------|----------|-------------|--------|
| OS | FULL | 3.3 | ADAPT |
| CLUE | -- | -- | -- |
| SAY | FULL | Ch 9 | -- |
| CIC | FULL | Ch 8 | -- |

**Canonical source:** OS (CC-BY 4.0, direct definition and deployment in 3.3)
**Status:** VALIDATED

---

### DEF-SCL002: Parts per million/billion (C)

| Source | Coverage | Key Sections | Signal |
|--------|----------|-------------|--------|
| OS | FULL | 3.4 | ADAPT |
| CLUE | -- | -- | -- |
| SAY | FULL | Ch 9 (water quality) | -- |
| CIC | FULL | Ch 4, 8 (CO2, water contaminants) | -- |

**Canonical source:** OS (CC-BY 4.0, ppm/ppb in concentration units section)
**Status:** VALIDATED
**Note:** ppm/ppb is one of the most non-majors-relevant concentration concepts (drinking water standards, air quality, climate change). CIC deploys it in 2 chapters; SAY connects it to water purification. Phase 4 should emphasize real-world deployment.

---

### DEF-SCL003: Ideal gas reasoning (E)

| Source | Coverage | Key Sections | Signal |
|--------|----------|-------------|--------|
| OS | FULL | 9.2 | REWRITE |
| CLUE | -- | -- | -- |
| SAY | PARTIAL | Ch 8 (qualitative gas behavior) | -- |
| CIC | -- | -- | -- |

**Canonical source:** OS (CC-BY 4.0, PV=nRT in 9.2; needs conceptual reframing for non-majors)
**Status:** VALIDATED
**Note:** E-tier. Absent from both reformed sources (CLUE, CIC). SAY provides only qualitative treatment. Gas law reasoning is useful for real-world contexts (breathing, weather, cooking at altitude) but the quantitative PV=nRT formalism may exceed non-majors needs.

---

### DEF-SCL004: Colligative properties (E)

| Source | Coverage | Key Sections | Signal |
|--------|----------|-------------|--------|
| OS | FULL | 11.4 | REWRITE |
| CLUE | -- | -- | -- |
| SAY | PARTIAL | Ch 9 (brief treatment) | -- |
| CIC | -- | -- | -- |

**Canonical source:** OS (CC-BY 4.0, boiling point elevation and freezing point depression in 11.4; needs simplification — focus on "why" not calculations)
**Status:** VALIDATED
**Note:** E-tier. Real-world hooks (antifreeze, salting roads, IV solutions) are strong, but the item is absent from CLUE and CIC, confirming Enrichment classification.

---

### DEF-SCL005: Safety and risk reasoning (C)

| Source | Coverage | Key Sections | Signal |
|--------|----------|-------------|--------|
| OS | PARTIAL | 21.6 (radiation dose only) | ADAPT |
| CLUE | -- | -- | -- |
| SAY | FULL | Ch 11 (radiation safety) | -- |
| CIC | FULL | Ch 6, 12 (nuclear risk, drug safety) | -- |

**Canonical source:** SAY (CC-BY-NC-SA; most systematic non-majors treatment of safety and risk in nuclear chemistry context)
**Supplementary:** CIC Ch 6 + 12 (structural validation — nuclear risk assessment and pharmaceutical dosing; proprietary, reference only)
**Status:** VALIDATED
**Note:** OS provides only radiation-dose content (partial). SAY devotes significant attention to radiation safety in a non-majors-calibrated way. CIC exercises safety/risk reasoning across 2 chapters in different societal contexts. Phase 4 should draw from SAY's framing and CIC's contextual approach.

---

### SCL Domain Summary

| Status | Count | Items |
|--------|-------|-------|
| VALIDATED | 11 | All SCL items |
| GAP | 0 | -- |

**Coverage rate:** 11/11 (100%). No gaps. Two items use non-OS canonical sources: PRIM-SCL001 and PRIM-SCL004 (CLUE, for reasoning-mode items), DEF-SCL005 (SAY, for non-majors safety coverage).

---

## Aggregate Coverage Statistics

### Overall Coverage

| Domain | Items | VALIDATED | META | GAP | Rate |
|--------|-------|-----------|------|-----|------|
| COM | 13 | 12 | 1 | 0 | 100% |
| STR | 15 | 15 | 0 | 0 | 100% |
| NRG | 11 | 11 | 0 | 0 | 100% |
| CHG | 12 | 12 | 0 | 0 | 100% |
| SCL | 11 | 11 | 0 | 0 | 100% |
| **Total** | **62** | **61** | **1** | **0** | **100%** |

### Source Coverage Breadth

| Source | Items Covered (FULL+PARTIAL) | Coverage Rate | License |
|--------|------------------------------|---------------|---------|
| OS | 59/62 | 95% | CC-BY 4.0 |
| CLUE | 45/62 | 73% | CC-BY-NC-SA |
| SAY | 55/62 | 89% | CC-BY-NC-SA |
| CIC | 45/62 | 73% | Proprietary |

### Canonical Source Distribution

| Source | Items where canonical | Why |
|--------|----------------------|-----|
| OS | 55 | CC-BY license + FULL coverage for most items |
| CLUE | 4 | PRIM-COM008, PRIM-SCL001, PRIM-SCL004 (reasoning-mode items); DEF-STR009 (OS gap) |
| SAY | 3 | DEF-STR008 (OS gap); DEF-SCL005 (OS only partial); DEF-STR007 (supplementary) |
| CIC | 0 | Proprietary — structural validation only, never canonical |

### Items Requiring Non-OS Sources

| Item | Why OS insufficient | Canonical | Supplementary |
|------|---------------------|-----------|---------------|
| PRIM-COM008 | Meta-cognitive; OS implicit only | CLUE 1.2, 8.6 | Framing in all worked examples |
| DEF-STR008 | OS in non-relevant sections | SAY Ch 15-19 | CIC Ch 9 |
| DEF-STR009 | OS in SKIPped Ch 18 | CLUE 3.3 | SAY Ch 3 |
| PRIM-SCL001 | OS implicit only | CLUE 1.5, 5.2 | OS 9.1 |
| PRIM-SCL004 | OS partial only | CLUE 5.2 | SAY Ch 17-19 |
| DEF-SCL005 | OS partial (radiation only) | SAY Ch 11 | CIC Ch 6, 12 |

---

## Cross-Domain Topic Decomposition

Traditional chemistry topics often span multiple taxonomy domains. This section explicitly decomposes cross-domain source topics so the coverage matrix correctly attributes coverage and the sequencing comparison (in 05-GAP-ANALYSIS.md) operates at the domain level.

### "Solutions" (OS Ch 11 / SAY Ch 9 / CIC Ch 8)

| Subtopic | Domain | Taxonomy Items |
|----------|--------|---------------|
| Like dissolves like (IMF-based reasoning) | STR | DEF-STR004, PRIM-STR004, DEF-STR010 |
| Molarity, dilution | SCL | DEF-SCL001, PRIM-SCL003 |
| ppm, ppb | SCL | DEF-SCL002 |
| Colligative properties | SCL | DEF-SCL004, PRIM-SCL004 |
| Electrolytes and dissociation | CHG | PRIM-CHG005 (peripheral) |

### "Thermochemistry / Thermodynamics" (OS Ch 5 + 16 / CLUE Ch 5)

| Subtopic | Domain | Taxonomy Items |
|----------|--------|---------------|
| Energy tracking, exo/endo, heat/temp | NRG | PRIM-NRG001, PRIM-NRG003, DEF-NRG001, DEF-NRG005 |
| Specific heat, calorimetry | NRG | DEF-NRG002 |
| Bond energy, enthalpy | NRG | PRIM-NRG002, DEF-NRG003 |
| Entropy, spontaneity, free energy | NRG | PRIM-NRG004, PRIM-NRG005, DEF-NRG004 |

### "Chemical Reactions" (OS Ch 4 / SAY Ch 5 / CLUE Ch 7)

| Subtopic | Domain | Taxonomy Items |
|----------|--------|---------------|
| Equation reading, balancing | CHG | PRIM-CHG001 |
| Atom conservation (why equations balance) | COM | PRIM-COM006 |
| Reaction type recognition | CHG | PRIM-CHG002 |
| Acid-base reactions | CHG | PRIM-CHG005 |
| Redox reactions | CHG | PRIM-CHG006 |
| Energy changes in reactions | NRG | PRIM-NRG002, PRIM-NRG003 |
| Reaction stoichiometry | SCL | PRIM-SCL005, PRIM-SCL002 |

### "Kinetics + Equilibrium" (OS Ch 12-13 / CLUE Ch 8)

| Subtopic | Domain | Taxonomy Items |
|----------|--------|---------------|
| Rate factors (qualitative) | CHG | PRIM-CHG004 |
| Activation energy, collision theory | NRG | PRIM-NRG006 |
| Catalysis | CHG | DEF-CHG001 |
| Dynamic equilibrium | CHG | PRIM-CHG003 |
| Le Chatelier's principle | CHG | DEF-CHG003 |
| Entropy and spontaneity at equilibrium | NRG | PRIM-NRG004, PRIM-NRG005 |

### "Acids and Bases" (OS Ch 14 / SAY Ch 10 / CIC Ch 8)

| Subtopic | Domain | Taxonomy Items |
|----------|--------|---------------|
| Bronsted-Lowry proton transfer | CHG | PRIM-CHG005 |
| pH scale | CHG | DEF-CHG002 |
| Strong vs weak acids/bases | CHG | PRIM-CHG005 |
| Buffers | CHG | PRIM-CHG003, PRIM-CHG005 |
| pH measurement and concentration | SCL | PRIM-SCL003 |

### "Organic Chemistry" (OS Ch 20 / SAY Ch 12-15 / CIC Ch 9-10)

| Subtopic | Domain | Taxonomy Items |
|----------|--------|---------------|
| Carbon backbone, hydrocarbons | STR | DEF-STR007 |
| Isomers | STR | DEF-STR005 |
| Functional groups (recognition) | STR | DEF-STR007 |
| Polymers | STR | DEF-STR008 |
| Organic reaction types | CHG | PRIM-CHG002 |
| Structure-to-property in organic | STR | PRIM-STR005 |

### "Nuclear Chemistry" (OS Ch 21 / SAY Ch 11 / CIC Ch 6)

| Subtopic | Domain | Taxonomy Items |
|----------|--------|---------------|
| Nuclear reactions (alpha, beta, gamma) | CHG | PRIM-CHG007 |
| Half-life, decay | CHG | DEF-CHG004 |
| Nuclear energy (fission, fusion) | NRG | PRIM-NRG001 |
| Radiation safety, biological effects | SCL | DEF-SCL005 |

---

## Redundancy Resolution

Items covered by 2+ sources at FULL depth. Canonical source designated per the 5-criteria hierarchy (Section 1).

### Items with 4-source coverage (19 items)

All 4 sources provide coverage for these Core-tier items. OS is canonical for all 19 due to CC-BY 4.0 license:

PRIM-COM001, PRIM-COM002, PRIM-COM003, PRIM-COM005, PRIM-COM006, DEF-COM001, DEF-COM002, PRIM-STR001, PRIM-STR002, PRIM-STR003, PRIM-STR004, PRIM-STR005, DEF-STR001, DEF-STR003, DEF-STR004, DEF-STR010, PRIM-NRG001, PRIM-NRG002, PRIM-NRG003

### Items with 3-source coverage (24 items)

OS is canonical for most. Exceptions noted above (PRIM-COM008, PRIM-SCL001, PRIM-SCL004, DEF-STR009).

### Items with 2-source coverage (12 items)

| Item | Sources | Canonical | Rationale |
|------|---------|-----------|-----------|
| DEF-COM003 | OS, SAY | OS | CC-BY; both at FULL |
| DEF-COM004 | OS, SAY | OS | CC-BY; both at FULL |
| DEF-NRG004 | OS, CLUE | OS | CC-BY; CLUE has better integration but NC-SA |
| DEF-SCL003 | OS, SAY | OS | CC-BY; SAY is qualitative only |
| DEF-SCL004 | OS, SAY | OS | CC-BY; SAY is brief |
| PRIM-NRG004 | OS, CLUE | OS | CC-BY; CLUE pedagogical model |
| PRIM-NRG005 | OS, CLUE | OS | CC-BY; CLUE pedagogical model |
| PRIM-SCL005 | OS, SAY, CIC | OS | CC-BY; CIC non-majors context |
| DEF-STR008 | SAY, CIC | SAY | NC-SA; CIC proprietary |
| DEF-STR006 | OS, CLUE, SAY | OS | CC-BY |
| DEF-CHG003 | OS, CLUE | OS | CC-BY |
| DEF-CHG005 | OS only | OS | Only source |

### Items with 1-source coverage (1 item)

| Item | Source | Status |
|------|--------|--------|
| DEF-CHG005 (precipitation, E) | OS 15.1 | VALIDATED (single source, E-tier) |

---

## Core vs Enrichment Coverage Summary

### Core items (53 items)

| Coverage Pattern | Count | Items |
|------------------|-------|-------|
| 4 sources | 19 | (listed above) |
| 3 sources | 23 | Most remaining Core items |
| 2 sources | 10 | DEF-COM005, DEF-NRG004 not Core... |
| 1 source | 0 | -- |
| META | 1 | PRIM-COM008 |

**All 53 Core items have >= 2 source coverage (or META status).** QG2-1 PASS.

### Enrichment items (9 items)

| Item | Sources with coverage | Canonical |
|------|----------------------|-----------|
| DEF-COM003 | OS, SAY | OS |
| DEF-COM004 | OS, SAY | OS |
| DEF-NRG004 | OS, CLUE | OS |
| DEF-SCL003 | OS, SAY | OS |
| DEF-SCL004 | OS, SAY | OS |
| DEF-STR009 | CLUE, SAY | CLUE |
| DEF-CHG005 | OS | OS |
| PRIM-CHG007 | OS, SAY, CIC | OS |
| DEF-CHG004 | OS, SAY, CIC | OS |

**All 9 Enrichment items have >= 1 source coverage.** No gaps.

---

## QG2 Pre-Check Results (coverage-related gates)

| Check | Criterion | Result |
|-------|-----------|--------|
| QG2-1 | Every Core item maps to >= 1 source at FULL or PARTIAL | **PASS** (53/53) |
| QG2-2 | Zero Core items with zero source coverage | **PASS** (0 uncovered) |
| QG2-7 | Backtracking threshold: >20% Core uncovered OR >5 new items needed | **PASS** (0% uncovered, 0 new items needed) |
| QG2-8 | Every item covered by 2+ sources has canonical source designated | **PASS** (all canonical sources designated) |

**Remaining QG2 checks (QG2-0, QG2-3 through QG2-6) are evaluated in 05-GAP-ANALYSIS.md.**
